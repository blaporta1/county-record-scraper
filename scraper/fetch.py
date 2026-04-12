#!/usr/bin/env python3
"""
Harris County Motivated Seller Lead Scraper
============================================
Scrapes Official Public Records from the Harris County Clerk portal
(cclerk.hctx.net) and enriches results with HCAD bulk parcel data.

Outputs:
  dashboard/records.json   – served via GitHub Pages
  data/records.json        – raw archive
  data/ghl_export.csv      – GoHighLevel import
"""

from __future__ import annotations

import asyncio
import csv
import io
import json
import logging
import os
import re
import sys
import tempfile
import time
import zipfile
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from urllib.parse import urljoin, urlencode

import requests
from bs4 import BeautifulSoup
from dbfread import DBF
from playwright.async_api import (
    async_playwright,
    Page,
    TimeoutError as PlaywrightTimeout,
)

# ─────────────────────────────────────────────────────────────────────────────
# Configuration
# ─────────────────────────────────────────────────────────────────────────────

LOOKBACK_DAYS: int = int(os.getenv("LOOKBACK_DAYS", "7"))

# Harris County Clerk – Official Public Records search (ASP.NET WebForms)
CLERK_SEARCH_URL: str = os.getenv(
    "CLERK_URL",
    "https://caopay.harriscountytx.gov/",
)

# Harris County Appraisal District bulk parcel data
HCAD_BULK_URL: str = os.getenv(
    "HCAD_BULK_URL",
    "",  # auto-discovered if empty
)

MAX_RETRIES: int  = 3
RETRY_DELAY: int  = 6        # seconds between retries
PAGE_TIMEOUT: int = 90_000   # ms – Playwright navigation
NAV_TIMEOUT: int  = 45_000   # ms – element wait

OUTPUT_FILES: List[Path] = [
    Path("dashboard/records.json"),
    Path("data/records.json"),
]
GHL_CSV_PATH: Path = Path("data/ghl_export.csv")

# ─────────────────────────────────────────────────────────────────────────────
# Document-type registry
# ─────────────────────────────────────────────────────────────────────────────

# Keyed by the short code used in the clerk portal drop-down / search box.
# Values: (category, human label)
DOC_REGISTRY: Dict[str, Tuple[str, str]] = {
    "LP":       ("foreclosure", "Lis Pendens"),
    "NOFC":     ("foreclosure", "Notice of Foreclosure"),
    "TAXDEED":  ("tax",         "Tax Deed"),
    "JUD":      ("judgment",    "Judgment"),
    "CCJ":      ("judgment",    "Certified Judgment"),
    "DRJUD":    ("judgment",    "Domestic Judgment"),
    "LNCORPTX": ("lien",        "Corp Tax Lien"),
    "LNIRS":    ("lien",        "IRS Lien"),
    "LNFED":    ("lien",        "Federal Lien"),
    "LN":       ("lien",        "Lien"),
    "LNMECH":   ("lien",        "Mechanic Lien"),
    "LNHOA":    ("lien",        "HOA Lien"),
    "MEDLN":    ("lien",        "Medicaid Lien"),
    "PRO":      ("probate",     "Probate"),
    "NOC":      ("lien",        "Notice of Commencement"),
    "RELLP":    ("foreclosure", "Release Lis Pendens"),
}

# ─────────────────────────────────────────────────────────────────────────────
# Logging
# ─────────────────────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)-8s %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger("hctx_scraper")


# ═════════════════════════════════════════════════════════════════════════════
# SECTION 1 – HCAD Parcel Data
# ═════════════════════════════════════════════════════════════════════════════

# Column-name candidates in HCAD DBF files (varies by year/release)
_OWNER_COLS  = ["OWN1", "OWNER", "OWNER_NAME", "NAME1", "NAME"]
_SADDR_COLS  = ["SITEADDR", "SITE_ADDR", "PROP_ADDR", "STADDR", "ADDRESS"]
_SCITY_COLS  = ["SITE_CITY", "SITECITY", "PROP_CITY", "CITY"]
_SZIP_COLS   = ["SITE_ZIP",  "SITEZIP",  "PROP_ZIP",  "ZIP"]
_MADDR_COLS  = ["MAILADR1", "ADDR_1",   "MAIL_ADDR", "MAIL1", "MAILADDR"]
_MCITY_COLS  = ["MAILCITY", "MAIL_CITY","CITY2"]
_MSTATE_COLS = ["MAILSTATE","STATE",    "ST"]
_MZIP_COLS   = ["MAILZIP",  "MAIL_ZIP", "ZIP2"]


def _dbf_get(record, candidates: List[str]) -> str:
    """Return the first non-empty value from a DBF record matching any candidate column."""
    for col in candidates:
        for variant in (col, col.lower(), col.upper()):
            val = record.get(variant)
            if val and str(val).strip():
                return str(val).strip()
    return ""


def _name_variants(raw: str) -> List[str]:
    """
    Generate normalized lookup keys for a raw owner name.
    Handles:  LAST, FIRST  |  FIRST LAST  |  LAST FIRST  |  ENTITY NAME
    """
    name = raw.strip().upper()
    if not name:
        return []

    variants: List[str] = [name]

    # Strip common entity suffixes for fuzzy matching
    for sfx in (" LLC", " INC", " CORP", " LTD", " LP", " LLP",
                 " TRUST", " ESTATE", " ETAL"):
        if name.endswith(sfx):
            variants.append(name[: -len(sfx)].strip())

    if "," in name:
        # "LAST, FIRST MIDDLE" → "FIRST MIDDLE LAST"
        last, rest = name.split(",", 1)
        first_last = f"{rest.strip()} {last.strip()}"
        variants += [first_last, last.strip(), rest.strip()]
    else:
        parts = name.split()
        if len(parts) >= 2:
            # "FIRST LAST" → "LAST, FIRST" and "LAST FIRST"
            variants.append(f"{parts[-1]}, {' '.join(parts[:-1])}")
            variants.append(f"{parts[-1]} {' '.join(parts[:-1])}")

    # Deduplicate while preserving order
    seen: set = set()
    result: List[str] = []
    for v in variants:
        if v and v not in seen:
            seen.add(v)
            result.append(v)
    return result


def _read_dbf_to_lookup(path: str) -> Dict[str, Dict]:
    """Parse one DBF file into {owner_variant: address_dict}."""
    lookup: Dict[str, Dict] = {}
    try:
        table = DBF(path, encoding="cp1252", ignore_missing_memofile=True)
        for rec in table:
            try:
                owner = _dbf_get(rec, _OWNER_COLS)
                if not owner:
                    continue
                entry = {
                    "prop_address": _dbf_get(rec, _SADDR_COLS),
                    "prop_city":    _dbf_get(rec, _SCITY_COLS) or "Houston",
                    "prop_state":   "TX",
                    "prop_zip":     _dbf_get(rec, _SZIP_COLS),
                    "mail_address": _dbf_get(rec, _MADDR_COLS),
                    "mail_city":    _dbf_get(rec, _MCITY_COLS),
                    "mail_state":   _dbf_get(rec, _MSTATE_COLS) or "TX",
                    "mail_zip":     _dbf_get(rec, _MZIP_COLS),
                }
                for variant in _name_variants(owner):
                    lookup[variant] = entry
            except Exception:
                continue
    except Exception as exc:
        log.warning(f"DBF read error ({path}): {exc}")
    return lookup


def _parse_zip_or_dbf(content: bytes) -> Dict[str, Dict]:
    """Accept either a raw ZIP or a bare DBF; return owner lookup."""
    lookup: Dict[str, Dict] = {}
    try:
        with zipfile.ZipFile(io.BytesIO(content)) as zf:
            dbf_files = [n for n in zf.namelist() if n.lower().endswith(".dbf")]
            if not dbf_files:
                log.warning("ZIP contained no .dbf files")
                return {}
            for dbf_name in dbf_files:
                log.info(f"  Parsing DBF: {dbf_name}")
                with tempfile.NamedTemporaryFile(suffix=".dbf", delete=False) as tmp:
                    tmp.write(zf.read(dbf_name))
                    tmp_path = tmp.name
                try:
                    partial = _read_dbf_to_lookup(tmp_path)
                    lookup.update(partial)
                    log.info(f"  → {len(partial):,} name variants loaded")
                finally:
                    try:
                        os.unlink(tmp_path)
                    except OSError:
                        pass
    except zipfile.BadZipFile:
        # Treat as bare DBF
        with tempfile.NamedTemporaryFile(suffix=".dbf", delete=False) as tmp:
            tmp.write(content)
            tmp_path = tmp.name
        try:
            lookup = _read_dbf_to_lookup(tmp_path)
        finally:
            try:
                os.unlink(tmp_path)
            except OSError:
                pass
    return lookup


def _discover_hcad_url() -> List[str]:
    """Try to scrape the HCAD data portal for the real account/owner download URL."""
    candidate_pages = [
        "https://pdata.hcad.org/",
        "https://pdata.hcad.org/data/",
        "https://hcad.org/hcad-resources/hcad-appraisal-codes/hcad-real-property-download-files/",
    ]
    found: List[str] = []
    for page_url in candidate_pages:
        try:
            r = requests.get(page_url, timeout=20)
            if r.status_code != 200:
                continue
            soup = BeautifulSoup(r.text, "lxml")
            for a in soup.find_all("a", href=True):
                href: str = a["href"]
                lower = href.lower()
                if (href.endswith(".zip") or href.endswith(".dbf")) and any(
                    kw in lower for kw in ["owner", "acct", "real", "parcel"]
                ):
                    full = urljoin(page_url, href)
                    if full not in found:
                        found.append(full)
        except Exception:
            pass
    return found


def download_hcad_parcel_data() -> Dict[str, Dict]:
    """
    Download HCAD bulk parcel data and build an owner-name → address lookup.
    Falls back gracefully; returns {} on total failure.
    """
    year = datetime.now().year
    candidates: List[str] = []

    if HCAD_BULK_URL and HCAD_BULK_URL not in ("[paste URL here]", ""):
        candidates.append(HCAD_BULK_URL)

    # Well-known HCAD paths (current year first, then prior year)
    for y in (year, year - 1):
        candidates += [
            f"https://pdata.hcad.org/data/cama/{y}/real_acct_owner.zip",
            f"https://pdata.hcad.org/data/{y}/real_acct_owner.zip",
        ]
    candidates.append("https://pdata.hcad.org/data/cama/real_acct_owner.zip")

    # Discover additional URLs from the portal HTML
    try:
        discovered = _discover_hcad_url()
        candidates = discovered + [c for c in candidates if c not in discovered]
    except Exception:
        pass

    for url in candidates:
        for attempt in range(1, MAX_RETRIES + 1):
            try:
                log.info(f"HCAD download attempt {attempt}: {url}")
                resp = requests.get(url, timeout=180, stream=True)
                if resp.status_code != 200:
                    log.warning(f"  HTTP {resp.status_code}")
                    break  # try next URL
                content = resp.content
                lookup = _parse_zip_or_dbf(content)
                if lookup:
                    log.info(f"HCAD parcel data loaded: {len(lookup):,} owner variants")
                    return lookup
            except Exception as exc:
                log.warning(f"  Attempt {attempt} failed: {exc}")
                if attempt < MAX_RETRIES:
                    time.sleep(RETRY_DELAY)

    log.warning("HCAD parcel data unavailable — addresses will be empty")
    return {}


def lookup_parcel(owner: str, parcel_data: Dict[str, Dict]) -> Optional[Dict]:
    """Return address dict for owner, or None."""
    if not owner or not parcel_data:
        return None
    for variant in _name_variants(owner.upper()):
        hit = parcel_data.get(variant)
        if hit:
            return hit
    # Last resort: prefix match on first surname token
    first_token = owner.upper().split()[0] if owner.split() else ""
    if first_token and len(first_token) >= 4:
        for key, val in parcel_data.items():
            if key.startswith(first_token):
                return val
    return None


# ═════════════════════════════════════════════════════════════════════════════
# SECTION 2 – Seller Scoring
# ═════════════════════════════════════════════════════════════════════════════

def compute_score(record: Dict, all_owner_types: Optional[Dict[str, List[str]]] = None) -> Tuple[int, List[str]]:
    """
    Return (score 0-100, flags list) for a single record.

    Scoring rubric:
      Base:                           30
      Per distress flag:             +10  (capped implicitly)
      LP + foreclosure combo:        +20  (checked via all_owner_types)
      Amount > $100k:                +15
      Amount > $50k (and <= $100k):  +10
      Filed within last 7 days:       +5
      Has property address:           +5
      LLC / corp owner:              +10
    """
    score = 30
    flags: List[str] = []

    doc_type  = record.get("doc_type", "")
    amount    = record.get("amount") or 0
    filed_str = record.get("filed", "") or ""
    owner     = record.get("owner", "") or ""

    # ── Distress flags ──────────────────────────────────────────────────────
    if doc_type in ("LP", "RELLP"):
        flags.append("Lis pendens")
        score += 10

    if doc_type in ("NOFC", "TAXDEED"):
        flags.append("Pre-foreclosure")
        score += 10

    if doc_type in ("JUD", "CCJ", "DRJUD"):
        flags.append("Judgment lien")
        score += 10

    if doc_type in ("LNCORPTX", "LNIRS", "LNFED", "TAXDEED"):
        flags.append("Tax lien")
        score += 10

    if doc_type == "LNMECH":
        flags.append("Mechanic lien")
        score += 10

    if doc_type == "PRO":
        flags.append("Probate / estate")
        score += 10

    if doc_type in ("LNHOA", "MEDLN"):
        score += 10  # still distressed but no separate flag label

    # ── LP + Foreclosure combo bonus ────────────────────────────────────────
    if all_owner_types and owner:
        owner_types = set(all_owner_types.get(owner.upper(), []))
        has_lp = bool(owner_types & {"LP", "RELLP"})
        has_fc = bool(owner_types & {"NOFC", "TAXDEED"})
        if has_lp and has_fc:
            if "Pre-foreclosure" not in flags:
                flags.append("Pre-foreclosure")
            score += 20

    # ── Amount ──────────────────────────────────────────────────────────────
    try:
        amt = float(amount) if amount else 0.0
    except (ValueError, TypeError):
        amt = 0.0

    if amt > 100_000:
        flags.append("Large debt (>$100k)")
        score += 15
    elif amt > 50_000:
        score += 10

    # ── Recency ─────────────────────────────────────────────────────────────
    try:
        filed_dt = datetime.strptime(filed_str[:10], "%Y-%m-%d")
        if (datetime.now() - filed_dt).days <= 7:
            flags.append("New this week")
            score += 5
    except (ValueError, TypeError):
        pass

    # ── Address availability ─────────────────────────────────────────────────
    if record.get("prop_address"):
        score += 5
        flags.append("Has address")

    # ── Entity / corp owner ──────────────────────────────────────────────────
    if owner and re.search(r"\b(LLC|INC|CORP|LTD|LLP|LP|TRUST)\b", owner.upper()):
        flags.append("LLC / corp owner")
        score += 10

    # Deduplicate flags, preserving order
    seen: set = set()
    deduped: List[str] = []
    for f in flags:
        if f not in seen:
            seen.add(f)
            deduped.append(f)

    return min(score, 100), deduped


# ═════════════════════════════════════════════════════════════════════════════
# SECTION 3 – Clerk Portal Scraper (Playwright)
# ═════════════════════════════════════════════════════════════════════════════

def _normalize_date(raw: str) -> str:
    """Attempt to normalize various date formats to YYYY-MM-DD."""
    if not raw:
        return ""
    raw = raw.strip()
    for fmt in ("%m/%d/%Y", "%m-%d-%Y", "%Y-%m-%d", "%Y/%m/%d",
                "%m/%d/%y", "%d-%b-%Y", "%B %d, %Y"):
        try:
            return datetime.strptime(raw[:len(fmt) + 2], fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    # Regex fallback: grab first date-like token
    m = re.search(r"(\d{1,2})[/\-](\d{1,2})[/\-](\d{2,4})", raw)
    if m:
        mm, dd, yy = m.groups()
        year = int(yy) + 2000 if len(yy) == 2 else int(yy)
        return f"{year}-{int(mm):02d}-{int(dd):02d}"
    return raw[:10]


def _parse_amount(raw: str) -> Optional[float]:
    """Parse a dollar-amount string."""
    if not raw:
        return None
    cleaned = re.sub(r"[^\d.]", "", raw)
    if not cleaned or cleaned == ".":
        return None
    try:
        return float(cleaned)
    except ValueError:
        return None


def _build_blank_record(doc_type: str) -> Dict:
    cat, cat_label = DOC_REGISTRY.get(doc_type, ("other", doc_type))
    return {
        "doc_num":      "",
        "doc_type":     doc_type,
        "filed":        "",
        "cat":          cat,
        "cat_label":    cat_label,
        "owner":        "",
        "grantee":      "",
        "amount":       None,
        "legal":        "",
        "prop_address": "",
        "prop_city":    "",
        "prop_state":   "TX",
        "prop_zip":     "",
        "mail_address": "",
        "mail_city":    "",
        "mail_state":   "",
        "mail_zip":     "",
        "clerk_url":    "",
        "flags":        [],
        "score":        0,
    }


def _infer_col_map(headers: List[str]) -> Dict[str, int]:
    """Map header text → column index for known data columns."""
    mapping: Dict[str, int] = {}
    for i, h in enumerate(headers):
        hl = h.lower().replace(" ", "")
        if any(kw in hl for kw in ["docno", "docnum", "instrument", "recno", "number", "document"]):
            mapping.setdefault("doc_num", i)
        if any(kw in hl for kw in ["instrtype", "doctype", "type", "code"]):
            mapping.setdefault("doc_type_col", i)
        if any(kw in hl for kw in ["filedate", "filed", "recorded", "date"]):
            mapping.setdefault("filed", i)
        if any(kw in hl for kw in ["grantor", "owner", "from", "party1"]):
            mapping.setdefault("grantor", i)
        if any(kw in hl for kw in ["grantee", "to", "party2"]):
            mapping.setdefault("grantee", i)
        if any(kw in hl for kw in ["legal", "description", "property"]):
            mapping.setdefault("legal", i)
        if any(kw in hl for kw in ["amount", "consideration", "money"]):
            mapping.setdefault("amount", i)
    return mapping


def _parse_results_html(html: str, doc_type: str) -> List[Dict]:
    """Extract record rows from a results-page HTML string."""
    records: List[Dict] = []
    soup = BeautifulSoup(html, "lxml")

    # Locate the results table (GridView / data grid)
    results_table = None
    for tbl in soup.find_all("table"):
        ths = tbl.find_all("th")
        tds = tbl.find_all("td")
        cell_texts = " ".join(
            c.get_text(" ", strip=True).lower() for c in ths + tds[:20]
        )
        if any(
            kw in cell_texts
            for kw in ["grantor", "grantee", "instrument", "filed", "document no"]
        ):
            results_table = tbl
            break

    # Fallback: largest table with > 2 columns
    if not results_table:
        best, best_cols = None, 0
        for tbl in soup.find_all("table"):
            rows = tbl.find_all("tr")
            if rows:
                cols = len(rows[0].find_all(["th", "td"]))
                if cols > best_cols and cols > 2:
                    best, best_cols = tbl, cols
        results_table = best

    if not results_table:
        return records

    rows = results_table.find_all("tr")
    if len(rows) < 2:
        return records

    # Header row
    header_cells = rows[0].find_all(["th", "td"])
    headers = [c.get_text(strip=True) for c in header_cells]
    col_map = _infer_col_map(headers)

    def cell_text(cells: List, idx: int) -> str:
        if 0 <= idx < len(cells):
            return cells[idx].get_text(" ", strip=True).strip()
        return ""

    def cell_link(cells: List, idx: int) -> str:
        for i in range(len(cells)):
            a = cells[i].find("a", href=True)
            if a and "javascript" not in a["href"].lower():
                return urljoin(CLERK_SEARCH_URL, a["href"])
        return ""

    for row in rows[1:]:
        cells = row.find_all("td")
        if not cells or len(cells) < 2:
            continue
        try:
            doc_num_idx = col_map.get("doc_num", 0)
            doc_num = cell_text(cells, doc_num_idx)
            if not doc_num:
                continue

            rec = _build_blank_record(doc_type)
            rec["doc_num"]   = doc_num
            rec["filed"]     = _normalize_date(cell_text(cells, col_map.get("filed", 2)))
            rec["owner"]     = cell_text(cells, col_map.get("grantor", 3))
            rec["grantee"]   = cell_text(cells, col_map.get("grantee", 4))
            rec["legal"]     = cell_text(cells, col_map.get("legal", 5))
            rec["amount"]    = _parse_amount(cell_text(cells, col_map.get("amount", -1)))
            rec["clerk_url"] = cell_link(cells, doc_num_idx) or cell_link(cells, 0)
            records.append(rec)
        except Exception as exc:
            log.debug(f"Row parse error: {exc}")
            continue

    return records


async def _wait_for_results(page: Page):
    """Wait for results grid or 'no records' message to appear."""
    try:
        await page.wait_for_selector(
            "table tr td, .no-records, [id*='lblNoResults'], "
            "[id*='lblMessage'], #lblMessage",
            timeout=PAGE_TIMEOUT,
        )
    except PlaywrightTimeout:
        pass


async def _find_and_select_instrument(page: Page, doc_type: str) -> bool:
    """
    Locate the instrument-type selector and choose the matching option.
    Returns True on success.
    """
    drop_selectors = [
        "#ddlInstrumentType", "#ddlDocType", "#ddlType",
        "select[id*='Instrument']", "select[id*='DocType']",
        "select[id*='InstrType']", "select[name*='Instrument']",
        "select[id*='Type']",
    ]
    label = DOC_REGISTRY.get(doc_type, (None, doc_type))[1]

    for sel in drop_selectors:
        try:
            el = page.locator(sel).first
            if not await el.is_visible(timeout=3_000):
                continue
            # Try matching by value (code) first, then by label text
            try:
                await el.select_option(value=doc_type, timeout=3_000)
                return True
            except Exception:
                pass
            try:
                await el.select_option(label=label, timeout=3_000)
                return True
            except Exception:
                pass
            # Partial label match
            opts = await el.evaluate("el => [...el.options].map(o => o.text)")
            for opt_text in opts:
                if doc_type.upper() in opt_text.upper() or label.upper() in opt_text.upper():
                    await el.select_option(label=opt_text, timeout=3_000)
                    return True
        except Exception:
            continue

    # Fall back: look for a text input labelled "Instrument Type"
    for inp in await page.locator("input[type='text']").all():
        try:
            placeholder = (await inp.get_attribute("placeholder") or "").lower()
            name        = (await inp.get_attribute("name") or "").lower()
            iid         = (await inp.get_attribute("id") or "").lower()
            if any(kw in placeholder + name + iid for kw in ["instr", "doctype", "type"]):
                await inp.fill(doc_type)
                return True
        except Exception:
            continue

    return False


async def _fill_dates(page: Page, start_date: str, end_date: str):
    """Fill from-date and to-date fields."""
    dt_from = datetime.strptime(start_date, "%Y-%m-%d")
    dt_to   = datetime.strptime(end_date,   "%Y-%m-%d")
    s_from  = dt_from.strftime("%m/%d/%Y")
    s_to    = dt_to.strftime("%m/%d/%Y")

    from_selectors = [
        "#txtFromDate", "#txtBeginDate", "#dtFrom", "#dtBegin",
        "input[id*='From']", "input[id*='Begin']", "input[id*='Start']",
        "input[name*='From']", "input[name*='Begin']",
    ]
    to_selectors = [
        "#txtToDate", "#txtEndDate", "#dtTo", "#dtEnd",
        "input[id*='ToDate']", "input[id*='EndDate']",
        "input[name*='To']", "input[name*='End']",
    ]

    async def fill_first_visible(selectors: List[str], value: str):
        for sel in selectors:
            try:
                el = page.locator(sel).first
                if await el.is_visible(timeout=2_000):
                    await el.triple_click()
                    await el.fill(value)
                    return
            except Exception:
                continue

    await fill_first_visible(from_selectors, s_from)
    await fill_first_visible(to_selectors, s_to)


async def _click_search(page: Page):
    """Click the Search / Submit button."""
    submit_selectors = [
        "#btnSearch", "#btnSubmit", "#btnGo",
        "input[value='Search']", "input[value='Submit']",
        "button:has-text('Search')", "button:has-text('Submit')",
        "input[type='submit']", "button[type='submit']",
    ]
    for sel in submit_selectors:
        try:
            el = page.locator(sel).first
            if await el.is_visible(timeout=2_000):
                await el.click()
                await page.wait_for_load_state("networkidle", timeout=PAGE_TIMEOUT)
                return
        except Exception:
            continue
    await page.keyboard.press("Return")
    await page.wait_for_load_state("networkidle", timeout=PAGE_TIMEOUT)


async def _next_page(page: Page) -> bool:
    """
    Navigate to the next results page.  Returns False if no next page exists.
    Handles both anchor links and ASP.NET __doPostBack pager buttons.
    """
    next_selectors = [
        "a:has-text('Next')", "a:has-text('>')", "a:has-text('>>')",
        "input[value='Next']", "input[value='>']", "input[value='>>']",
        "a[id*='Next']", "[id*='btnNext']",
        "a[href*='Page$Next']", "a[href*='__doPostBack'][id*='Next']",
    ]
    for sel in next_selectors:
        try:
            el = page.locator(sel).first
            if await el.is_visible(timeout=2_000) and await el.is_enabled(timeout=2_000):
                await el.click()
                await page.wait_for_load_state("networkidle", timeout=PAGE_TIMEOUT)
                return True
        except Exception:
            continue
    return False


async def _scrape_one_doc_type(
    page: Page,
    doc_type: str,
    start_date: str,
    end_date: str,
) -> List[Dict]:
    """Search and paginate one document type on the clerk portal."""
    records: List[Dict] = []

    # Navigate fresh each time to avoid stale ViewState
    await page.goto(CLERK_SEARCH_URL, timeout=PAGE_TIMEOUT, wait_until="domcontentloaded")
    await page.wait_for_load_state("networkidle", timeout=NAV_TIMEOUT)

    # Instrument type
    selected = await _find_and_select_instrument(page, doc_type)
    if not selected:
        log.warning(f"  Could not select instrument type for {doc_type} — skipping")
        return records

    # Date range
    await _fill_dates(page, start_date, end_date)

    # Submit
    await _click_search(page)
    await _wait_for_results(page)

    page_num = 0
    while True:
        page_num += 1
        html = await page.content()
        batch = _parse_results_html(html, doc_type)
        records.extend(batch)
        log.debug(f"    page {page_num}: {len(batch)} rows")

        if len(batch) == 0 or page_num >= 100:
            break

        has_next = await _next_page(page)
        if not has_next:
            break
        await asyncio.sleep(1.5)

    return records


async def fetch_all_clerk_records(
    doc_types: List[str],
    start_date: str,
    end_date: str,
) -> List[Dict]:
    """
    Launch Playwright and scrape all requested document types.
    Uses one browser context; opens a new page per doc type.
    """
    all_records: List[Dict] = []

    async with async_playwright() as pw:
        browser = await pw.chromium.launch(
            headless=True,
            args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
        )
        context = await browser.new_context(
            viewport={"width": 1366, "height": 768},
            user_agent=(
                "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
            ),
        )
        page = await context.new_page()

        try:
            for doc_type in doc_types:
                for attempt in range(1, MAX_RETRIES + 1):
                    try:
                        log.info(f"Scraping {doc_type} ({DOC_REGISTRY[doc_type][1]}) "
                                 f"— attempt {attempt}/{MAX_RETRIES}")
                        recs = await _scrape_one_doc_type(
                            page, doc_type, start_date, end_date
                        )
                        all_records.extend(recs)
                        log.info(f"  ✓ {len(recs)} records for {doc_type}")
                        break
                    except PlaywrightTimeout as exc:
                        log.warning(f"  Timeout on {doc_type} attempt {attempt}: {exc}")
                        if attempt < MAX_RETRIES:
                            await asyncio.sleep(RETRY_DELAY)
                        else:
                            log.error(f"  Giving up on {doc_type}")
                    except Exception as exc:
                        log.warning(f"  Error on {doc_type} attempt {attempt}: {exc}")
                        if attempt < MAX_RETRIES:
                            await asyncio.sleep(RETRY_DELAY)
                        else:
                            log.error(f"  Giving up on {doc_type}")

                await asyncio.sleep(2)  # polite inter-type delay

        finally:
            await browser.close()

    log.info(f"Clerk scrape complete. Total raw records: {len(all_records)}")
    return all_records


# ═════════════════════════════════════════════════════════════════════════════
# SECTION 4 – Enrichment & Deduplication
# ═════════════════════════════════════════════════════════════════════════════

def enrich_records(
    raw: List[Dict],
    parcel_data: Dict[str, Dict],
) -> List[Dict]:
    """
    1. Deduplicate by doc_num.
    2. Attach parcel address data.
    3. Build per-owner doc-type index (for LP+FC combo bonus).
    4. Compute seller scores and flags.
    5. Sort by score descending.
    """
    # Dedup
    seen_nums: set = set()
    deduped: List[Dict] = []
    for r in raw:
        key = r.get("doc_num", "")
        if key and key not in seen_nums:
            seen_nums.add(key)
            deduped.append(r)
        elif not key:
            deduped.append(r)  # keep records without doc_num (rare)

    # Address lookup
    for r in deduped:
        try:
            hit = lookup_parcel(r.get("owner", ""), parcel_data)
            if hit:
                r.update({k: v for k, v in hit.items() if v})
        except Exception:
            pass

    # Owner → [doc_types] index for combo scoring
    owner_types: Dict[str, List[str]] = {}
    for r in deduped:
        owner_key = (r.get("owner") or "").upper()
        if owner_key:
            owner_types.setdefault(owner_key, []).append(r.get("doc_type", ""))

    # Score
    for r in deduped:
        try:
            score, flags = compute_score(r, owner_types)
            r["score"] = score
            r["flags"] = flags
        except Exception:
            r["score"] = 30
            r["flags"] = []

    deduped.sort(key=lambda x: x.get("score", 0), reverse=True)
    return deduped


# ═════════════════════════════════════════════════════════════════════════════
# SECTION 5 – Output Writers
# ═════════════════════════════════════════════════════════════════════════════

def write_json(records: List[Dict], start_date: str, end_date: str):
    with_address = sum(1 for r in records if r.get("prop_address"))
    payload = {
        "fetched_at":   datetime.utcnow().isoformat() + "Z",
        "source":       "Harris County Clerk – Official Public Records",
        "clerk_url":    CLERK_SEARCH_URL,
        "date_range":   {"from": start_date, "to": end_date},
        "total":        len(records),
        "with_address": with_address,
        "records":      records,
    }
    for path in OUTPUT_FILES:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, default=str), encoding="utf-8")
        log.info(f"JSON → {path}  ({len(records)} records, {with_address} with address)")


def _split_name(full: str) -> Tuple[str, str]:
    """Split owner name into (first, last) for CRM import."""
    full = (full or "").strip()
    if not full:
        return "", ""
    if "," in full:
        last, rest = full.split(",", 1)
        return rest.strip().title(), last.strip().title()
    parts = full.split()
    if len(parts) == 1:
        return "", parts[0].title()
    return " ".join(parts[:-1]).title(), parts[-1].title()


def write_ghl_csv(records: List[Dict]):
    GHL_CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "First Name", "Last Name",
        "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
        "Property Address", "Property City", "Property State", "Property Zip",
        "Lead Type", "Document Type", "Date Filed", "Document Number",
        "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
        "Source", "Public Records URL",
    ]
    with open(GHL_CSV_PATH, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        for r in records:
            first, last = _split_name(r.get("owner", ""))
            writer.writerow({
                "First Name":             first,
                "Last Name":              last,
                "Mailing Address":        r.get("mail_address", ""),
                "Mailing City":           r.get("mail_city", ""),
                "Mailing State":          r.get("mail_state", ""),
                "Mailing Zip":            r.get("mail_zip", ""),
                "Property Address":       r.get("prop_address", ""),
                "Property City":          r.get("prop_city", ""),
                "Property State":         r.get("prop_state", "TX"),
                "Property Zip":           r.get("prop_zip", ""),
                "Lead Type":              r.get("cat_label", ""),
                "Document Type":          DOC_REGISTRY.get(r.get("doc_type", ""),
                                              (None, r.get("doc_type", "")))[1],
                "Date Filed":             r.get("filed", ""),
                "Document Number":        r.get("doc_num", ""),
                "Amount/Debt Owed":       r.get("amount", ""),
                "Seller Score":           r.get("score", 0),
                "Motivated Seller Flags": "; ".join(r.get("flags", [])),
                "Source":                 "Harris County Clerk",
                "Public Records URL":     r.get("clerk_url", ""),
            })
    log.info(f"GHL CSV → {GHL_CSV_PATH}  ({len(records)} rows)")


# ═════════════════════════════════════════════════════════════════════════════
# SECTION 6 – Entry Point
# ═════════════════════════════════════════════════════════════════════════════

async def main():
    today      = datetime.now()
    end_date   = today.strftime("%Y-%m-%d")
    start_date = (today - timedelta(days=LOOKBACK_DAYS)).strftime("%Y-%m-%d")

    log.info("=" * 60)
    log.info("Harris County Motivated Seller Lead Scraper")
    log.info(f"Date range : {start_date}  →  {end_date}  ({LOOKBACK_DAYS} days)")
    log.info(f"Doc types  : {len(DOC_REGISTRY)}")
    log.info("=" * 60)

    # Step 1 – Clerk portal
    doc_types = list(DOC_REGISTRY.keys())
    raw_records = await fetch_all_clerk_records(doc_types, start_date, end_date)

    # Step 2 – HCAD parcel data (can run while Playwright is tearing down)
    parcel_data = download_hcad_parcel_data()

    # Step 3 – Enrich, score, deduplicate
    enriched = enrich_records(raw_records, parcel_data)

    # Step 4 – Write outputs
    write_json(enriched, start_date, end_date)
    write_ghl_csv(enriched)

    log.info("=" * 60)
    log.info(f"Done. Total leads: {len(enriched)}")
    log.info(f"With address    : {sum(1 for r in enriched if r.get('prop_address'))}")
    if enriched:
        top = enriched[0]
        log.info(f"Top score       : {top['score']}  ({top.get('owner','?')} – {top.get('doc_type','?')})")
    log.info("=" * 60)


if __name__ == "__main__":
    asyncio.run(main())
