from pathlib import Path
from urllib.parse import quote_plus
import math
from datetime import date
import hmac
import os

from flask import Flask, render_template, request, redirect, url_for, Response, jsonify, session
import re

import pedigree_tools as pt
import pandas as pd


APP_DIR = Path(__file__).parent
BASE_CSV = APP_DIR / "drc-Hunde-mit-eltern-rkey-gentest.csv"
ZWS_CSV = APP_DIR / "ed_zws_results_all_animals.csv"


app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY") or os.environ.get("FLASK_SECRET_KEY") or "dev-secret-change-me"

AUTH_USERNAME = os.environ.get("APP_USERNAME", "admin")
AUTH_PASSWORD = os.environ.get("APP_PASSWORD", "admin")


def is_authenticated():
    return session.get("authenticated") is True


def is_safe_next_url(value):
    return bool(value) and value.startswith("/") and not value.startswith("//")


@app.before_request
def require_login():
    public_endpoints = {"login", "static"}
    if request.endpoint in public_endpoints:
        return None

    if is_authenticated():
        return None

    return redirect(url_for("login", next=request.full_path if request.query_string else request.path))


def load_data():
    """Lädt die Daten (merge) und baut den ZBNr-Index."""
    try:
        merged_df, report = pt.merge_dog_data_with_ebv(
            base_csv_path=BASE_CSV, ebv_csv_path=ZWS_CSV, out_csv_path=None
        )
    except Exception:
        # Fallback: try to load merged file if present
        try:
            merged_df = pt.load_merged_dog_file(APP_DIR / "hunde_mit_zws.csv")
        except Exception:
            merged_df = pd.read_csv(BASE_CSV, dtype=str)

    index, duplicates = pt.build_zbnr_index(merged_df)

    return merged_df, index


# load at startup
MERGED_DF, ZBNR_INDEX = load_data()
PAIRING_SEARCH_CACHE_DATE = None
GENETIC_TEST_FIELDS = [
    ("prcd_pra", "prcd-PRA"),
    ("hnpk", "HNPK"),
    ("sd2", "SD2"),
    ("cnm", "CNM"),
    ("eic", "EIC"),
    ("zs", "ZS"),
    ("stgd_status", "STGD_Status"),
]


# Helper functions for formatting and classification

def get_breeding_value_classification(value):    

    """Classify breeding value compared to population average (lower is better for ED)."""
    if value is None:
        return None
    try:
        val = float(value)
        if val < 95:
            return {"text": "besser als Durchschnitt", "class": "favorable"}
        elif val <= 105:
            return {"text": "nahe am Durchschnitt", "class": "average"}
        else:
            return {"text": "schlechter als Durchschnitt", "class": "unfavorable"}
    except:
        return None


def get_reliability_classification(value):
    """Classify reliability/confidence of breeding value estimate."""
    if value is None:
        return None
    try:
        val = float(value)
        # Handle both percentage (0-100) and decimal (0-1) formats
        if val > 1:
            val = val / 100.0
        if val < 0.30:
            return {"text": "niedrig", "class": "low"}
        elif val < 0.60:
            return {"text": "mittel", "class": "medium"}
        else:
            return {"text": "hoch", "class": "high"}
    except:
        return None


def get_ed_css_class(ed_value):
    """Return CSS class for ED finding color-coding."""
    if ed_value is None or ed_value == "":
        return "ed-missing"
    val_str = str(ed_value).lower().strip()
    if "0" in val_str and ("frei" in val_str or "free" in val_str or val_str.startswith("0/")):
        return "ed-free"
    elif "0.5" in val_str or "borderline" in val_str:
        return "ed-borderline"
    elif "1" in val_str or "grade 1" in val_str.lower():
        return "ed-grade-1"
    elif "2" in val_str or "grade 2" in val_str.lower():
        return "ed-grade-2"
    elif "3" in val_str or "grade 3" in val_str.lower():
        return "ed-grade-3"
    else:
        return "ed-unknown"


def format_ed_result(ed_value):
    """Format ED result for display."""
    if ed_value is None or str(ed_value).strip() == "":
        return "kein ED-Befund"
    return str(ed_value)


def format_zbnr(zbnr):
    """Format ZBNr for display."""
    if zbnr is None:
        return "unbekannt"
    return str(zbnr).strip()


def safe_get(dict_obj, keys, default=""):
    """Safely get nested values from dict, trying multiple keys."""
    if isinstance(keys, str):
        keys = [keys]
    for key in keys:
        if key in dict_obj and dict_obj[key] is not None:
            val = dict_obj[key]
            if isinstance(val, str):
                val = val.strip()
            if val != "":
                return val
    return default


def clean_text(value):
    if value is None or pd.isna(value):
        return ""
    text = str(value).strip()
    if text.lower() in {"", "nan", "none", "nat"}:
        return ""
    return text


def dog_summary(row):
    age_years = calculate_age_years(row)
    name = clean_text(row.get("Name")) or "unbekannt"
    zbnr = clean_text(row.get("ZBNr_norm")) or clean_text(row.get("ZBNr"))
    ed = clean_text(row.get("ED_rechts")) or clean_text(row.get("ED_rechts_raw")) or clean_text(row.get("ED_links"))
    try:
        ebv_raw = row.get("EBV") or row.get("ed_zw_0_10_niedrig_gut")
        ebv = int(round(float(ebv_raw))) if clean_text(ebv_raw) else None
    except Exception:
        ebv = None

    try:
        confidence_raw = row.get("Confidenz") or row.get("reliability_prozent") or row.get("reliability")
        confidence = int(round(float(confidence_raw))) if clean_text(confidence_raw) else None
    except Exception:
        confidence = None

    kc_health_url = ""
    if zbnr.upper().startswith("KC"):
        kc_health_url = (
            "https://www.royalkennelclub.com/search/health-test-results-finder/"
            f"?Filter={quote_plus(name)}"
        )

    genetic_tests = {key: clean_text(row.get(column)) for key, column in GENETIC_TEST_FIELDS}

    return {
        "name": name,
        "zbnr": zbnr,
        "wurfdatum": clean_text(row.get("Wurfdatum")) or clean_text(row.get("geburt")),
        "alter": age_years,
        "geschlecht": clean_text(row.get("Geschlecht")) or clean_text(row.get("sex")),
        "hd": clean_text(row.get("HD_Grad")) or clean_text(row.get("HD")),
        **genetic_tests,
        "ed": ed,
        "anz_nachkommen": dog_offspring_count(row),
        "zuchtwert": ebv,
        "zuchtwert_marker": zuchtwert_marker_position(ebv),
        "konfidenz": confidence,
        "kc_health_url": kc_health_url,
    }


def parent_display_by_zbnr(zbnr):
    normalized = pt.normalize_zbnr(clean_text(zbnr)) or clean_text(zbnr)
    if not normalized:
        return None

    parent = ZBNR_INDEX.get(normalized) or ZBNR_INDEX.get(clean_text(zbnr))
    if parent is None:
        return {"name": "", "zbnr": normalized, "label": normalized}

    name = clean_text(parent.get("Name"))
    parent_zbnr = clean_text(parent.get("ZBNr_norm")) or clean_text(parent.get("ZBNr")) or normalized
    label = " · ".join(part for part in [name, parent_zbnr] if part)
    return {"name": name, "zbnr": parent_zbnr, "label": label or normalized}


def is_carrier_status(value):
    return "träger".casefold() in clean_text(value).casefold()


def carrier_conflicts_with_dam(sire_row, dam_row):
    conflicts = []
    if sire_row is None or dam_row is None:
        return conflicts
    for key, column in GENETIC_TEST_FIELDS:
        if is_carrier_status(dam_row.get(column)) and is_carrier_status(sire_row.get(column)):
            conflicts.append(column)
    return conflicts


def parse_int_filter(value):
    text = clean_text(value)
    if not text:
        return None
    try:
        return int(text)
    except Exception:
        return None


def zuchtwert_marker_position(value):
    if value is None:
        return None
    try:
        numeric = float(value)
    except Exception:
        return None
    lower = -20
    upper = 20
    clamped = max(lower, min(upper, numeric))
    return (clamped - lower) / (upper - lower) * 100


def calculate_age_years(row, today=None):
    today = today or date.today()
    cached_age = row.get("_age_years") if hasattr(row, "get") else None
    if cached_age is not None and not pd.isna(cached_age):
        try:
            return int(cached_age)
        except Exception:
            pass

    birth = clean_text(row.get("Wurfdatum") or row.get("geburt"))
    if birth:
        birth_date = pd.to_datetime(birth, errors="coerce")
        if pd.notna(birth_date):
            bdate = birth_date.date()
            return today.year - bdate.year - ((today.month, today.day) < (bdate.month, bdate.day))

    birth_year_raw = clean_text(row.get("geburtsjahr") or row.get("birthyear_clean"))
    try:
        return today.year - int(float(birth_year_raw))
    except Exception:
        return None


def _extract_birth_year_series(df):
    if "geburtsjahr" in df.columns:
        source = df["geburtsjahr"]
    elif "birthyear_clean" in df.columns:
        source = df["birthyear_clean"]
    else:
        source = df.get("Wurfdatum", pd.Series([pd.NA] * len(df), index=df.index))

    return pd.to_numeric(
        source.astype(str).str.extract(r"(\d{4})")[0],
        errors="coerce",
    )


def ensure_pairing_search_columns():
    global PAIRING_SEARCH_CACHE_DATE
    today = date.today()
    required_columns = {
        "_sex_clean",
        "_search_name",
        "_search_zbnr",
        "_search_zbnr_norm",
        "_age_years",
        "_ebv_numeric",
        "_confidence_numeric",
        "_offspring_numeric",
        "_sort_name",
        "_sort_zbnr",
    }
    if PAIRING_SEARCH_CACHE_DATE == today and required_columns.issubset(MERGED_DF.columns):
        return

    MERGED_DF["_sex_clean"] = MERGED_DF["Geschlecht"].fillna("").astype(str).str.strip()
    MERGED_DF["_search_name"] = MERGED_DF["Name"].fillna("").astype(str).str.lower()
    MERGED_DF["_search_zbnr"] = MERGED_DF["ZBNr"].fillna("").astype(str).str.lower()
    MERGED_DF["_search_zbnr_norm"] = MERGED_DF["ZBNr_norm"].fillna("").astype(str).str.lower()
    MERGED_DF["_sort_name"] = MERGED_DF["Name"].fillna("").astype(str).str.lower()
    MERGED_DF["_sort_zbnr"] = MERGED_DF["ZBNr_norm"].fillna(MERGED_DF["ZBNr"]).fillna("").astype(str)

    birth_dates = pd.to_datetime(
        MERGED_DF.get("Wurfdatum", pd.Series([pd.NA] * len(MERGED_DF), index=MERGED_DF.index)),
        errors="coerce",
    )
    ages = today.year - birth_dates.dt.year - (
        (today.month < birth_dates.dt.month)
        | ((today.month == birth_dates.dt.month) & (today.day < birth_dates.dt.day))
    ).astype("int")
    ages = ages.where(birth_dates.notna())

    birth_years = _extract_birth_year_series(MERGED_DF)
    fallback_ages = today.year - birth_years
    MERGED_DF["_age_years"] = ages.fillna(fallback_ages)
    MERGED_DF["_ebv_numeric"] = pd.to_numeric(MERGED_DF.get("EBV"), errors="coerce")
    MERGED_DF["_confidence_numeric"] = pd.to_numeric(MERGED_DF.get("Confidenz"), errors="coerce")
    MERGED_DF["_offspring_numeric"] = pd.to_numeric(MERGED_DF.get("AnzNachkommen"), errors="coerce")

    PAIRING_SEARCH_CACHE_DATE = today


def apply_age_filter(df, min_age=None, max_age=None):
    if min_age is None and max_age is None:
        return df

    if "_age_years" in df.columns:
        ages = df["_age_years"]
    else:
        ages = df.apply(calculate_age_years, axis=1)
    mask = pd.Series([True] * len(df), index=df.index)
    if min_age is not None:
        mask &= ages.notna() & (ages >= min_age)
    if max_age is not None:
        mask &= ages.notna() & (ages <= max_age)
    return df.loc[mask]


def dog_matches_age(row, min_age=None, max_age=None):
    age = calculate_age_years(row)
    if min_age is not None and (age is None or age < min_age):
        return False
    if max_age is not None and (age is None or age > max_age):
        return False
    return True


def dog_ebv_value(row):
    cached = row.get("_ebv_numeric") if hasattr(row, "get") else None
    if cached is not None and not pd.isna(cached):
        return float(cached)
    return pt.to_float_or_none(row.get("EBV") or row.get("ed_zw_0_10_niedrig_gut"))


def dog_offspring_count(row):
    cached = row.get("_offspring_numeric") if hasattr(row, "get") else None
    if cached is not None and not pd.isna(cached):
        try:
            return int(cached)
        except Exception:
            pass
    value = clean_text(row.get("AnzNachkommen"))
    if not value:
        return None
    try:
        return int(float(value))
    except Exception:
        return None


def dog_matches_max_ebv(row, max_ebv=None):
    if max_ebv is None:
        return True
    ebv = dog_ebv_value(row)
    return ebv is not None and ebv <= max_ebv


def dog_matches_min_offspring(row, min_offspring=None):
    if min_offspring is None:
        return True
    count = dog_offspring_count(row)
    return count is not None and count >= min_offspring


def ancestor_zbnrs_for_dog(row, max_generations=5, include_self=True):
    zbnr = clean_text(row.get("ZBNr_norm") or row.get("ZBNr"))
    zbnr = pt.normalize_zbnr(zbnr) or zbnr
    if not zbnr:
        return set()

    slots = pt.build_ancestor_slots(ZBNR_INDEX, zbnr, max_generations=max_generations)
    ancestor_zbnrs = set()
    for slot_id, slot in slots.items():
        if slot_id == 1 and not include_self:
            continue
        dog = slot.get("dog") or {}
        slot_zbnr = clean_text(dog.get("ZBNr_norm") or dog.get("ZBNr")) or clean_text(slot.get("lookup_zbnr"))
        slot_zbnr = pt.normalize_zbnr(slot_zbnr) or slot_zbnr
        if slot_zbnr:
            ancestor_zbnrs.add(slot_zbnr)
    return ancestor_zbnrs


def dog_has_excluded_ancestor(row, excluded_zbnrs, max_generations=5):
    if not excluded_zbnrs:
        return False
    return bool(ancestor_zbnrs_for_dog(row, max_generations=max_generations) & set(excluded_zbnrs))


def parse_excluded_ancestor_values(values):
    result = []
    seen = set()
    for value in values:
        zbnr = parse_selected_zbnr(value)
        if not zbnr or zbnr in seen:
            continue
        seen.add(zbnr)
        result.append(zbnr)
    return result


def excluded_ancestor_summaries(zbnrs):
    summaries = []
    for zbnr in zbnrs:
        dog = resolve_dog(zbnr)
        if dog is None:
            summaries.append({"name": "", "zbnr": zbnr, "label": zbnr})
            continue
        summary = dog_summary(dog)
        summaries.append(
            {
                "name": summary["name"],
                "zbnr": summary["zbnr"] or zbnr,
                "label": f"{summary['name']} | {summary['zbnr'] or zbnr}",
            }
        )
    return summaries


def get_sire_candidates(
    min_age=None,
    max_age=None,
    max_ebv=None,
    min_offspring=None,
    dam_row=None,
    avoid_carrier_matches=False,
    excluded_ancestor_zbnrs=None,
    query="",
    sort_by="zuchtwert",
    sort_dir="asc",
):
    ensure_pairing_search_columns()
    candidates = MERGED_DF.loc[MERGED_DF["_sex_clean"] == "R"]

    q = clean_text(query).lower()
    if q:
        candidates = candidates[
            candidates["_search_name"].str.contains(q, na=False, regex=False)
            | candidates["_search_zbnr"].str.contains(q, na=False, regex=False)
            | candidates["_search_zbnr_norm"].str.contains(q, na=False, regex=False)
        ]

    candidates = apply_age_filter(candidates, min_age=min_age, max_age=max_age)
    if max_ebv is not None:
        candidates = candidates[candidates["_ebv_numeric"].notna() & (candidates["_ebv_numeric"] <= max_ebv)]
    if min_offspring is not None:
        candidates = candidates[
            candidates["_offspring_numeric"].notna() & (candidates["_offspring_numeric"] >= min_offspring)
        ]
    if avoid_carrier_matches and dam_row is not None:
        for _key, column in GENETIC_TEST_FIELDS:
            if column in candidates.columns and is_carrier_status(dam_row.get(column)):
                candidates = candidates.loc[~candidates[column].map(is_carrier_status)]
    if excluded_ancestor_zbnrs:
        excluded = set(excluded_ancestor_zbnrs)
        candidates = candidates.loc[
            ~candidates.apply(lambda row: bool(ancestor_zbnrs_for_dog(row) & excluded), axis=1)
        ]

    sort_map = {
        "name": "_sort_name",
        "zbnr": "_sort_zbnr",
        "alter": "_age_years",
        "zuchtwert": "_ebv_numeric",
        "konfidenz": "_confidence_numeric",
        "nachkommen": "_offspring_numeric",
    }
    sort_col = sort_map.get(sort_by, "_ebv_numeric")
    ascending = sort_dir != "desc"
    candidates = candidates.sort_values(by=[sort_col, "_sort_name"], ascending=[ascending, True], na_position="last")

    return candidates


def parse_selected_zbnr(value):
    text = clean_text(value)
    if "|" in text:
        text = text.rsplit("|", 1)[1].strip()
    return pt.normalize_zbnr(text) or text


def resolve_dog(value, required_sex=None):
    query = clean_text(value)
    if not query:
        return None

    zbnr = parse_selected_zbnr(query)
    dog = ZBNR_INDEX.get(zbnr)
    if dog is not None:
        if required_sex and clean_text(dog.get("Geschlecht")) != required_sex:
            return None
        return dog

    q = query.lower()
    matches = MERGED_DF[
        MERGED_DF["Name"].fillna("").str.lower().str.contains(q, na=False)
        | MERGED_DF["ZBNr"].fillna("").str.lower().str.contains(q, na=False)
        | MERGED_DF["ZBNr_norm"].fillna("").str.lower().str.contains(q, na=False)
    ].copy()

    if required_sex:
        matches = matches[matches["Geschlecht"].fillna("").astype(str).str.strip() == required_sex]

    if matches.empty:
        return None

    row = matches.iloc[0].to_dict()
    resolved_zbnr = clean_text(row.get("ZBNr_norm")) or clean_text(row.get("ZBNr"))
    return ZBNR_INDEX.get(resolved_zbnr) or row


def make_pairing_index(sire, dam):
    planned_zbnr = "__PLANNED_PAIRING__"
    sire_zbnr = clean_text(sire.get("ZBNr_norm") or sire.get("ZBNr"))
    dam_zbnr = clean_text(dam.get("ZBNr_norm") or dam.get("ZBNr"))

    pairing_index = dict(ZBNR_INDEX)
    pairing_index[planned_zbnr] = {
        "ZBNr": planned_zbnr,
        "ZBNr_norm": planned_zbnr,
        "Name": "Geplanter Wurf",
        "Geschlecht": "",
        "Wurfdatum": "",
        "vater_zbnr": sire_zbnr,
        "vater_zbnr_norm": sire_zbnr,
        "mutter_zbnr": dam_zbnr,
        "mutter_zbnr_norm": dam_zbnr,
        "pedigree_status": "ok",
        "father_found": True,
        "mother_found": True,
    }
    return planned_zbnr, pairing_index


def format_percent_or_dash(value):
    if value is None:
        return "—"
    try:
        return f"{float(value):.2f} %".replace(".", ",")
    except Exception:
        return "—"


def extract_embeddable_html(html):
    styles = "".join(re.findall(r"<style[^>]*>.*?</style>", html, re.S | re.I))
    m = re.search(r"<body[^>]*>(.*?)</body>", html, re.S | re.I)
    body = m.group(1) if m else html
    return styles + body


def _regularized_incomplete_beta(x, a, b, max_iter=200, eps=1e-12):
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    lbeta = math.lgamma(a) + math.lgamma(b) - math.lgamma(a + b)
    # continued fraction
    def betacf(a, b, x):
        m2 = 0
        aa = 0.0
        c = 1.0
        d = 1.0 - (a + b) * x / (a + 1.0)
        if abs(d) < 1e-30:
            d = 1e-30
        d = 1.0 / d
        h = d
        for m in range(1, max_iter + 1):
            m2 = 2 * m
            aa = m * (b - m) * x / ((a + m2 - 1.0) * (a + m2))
            d = 1.0 + aa * d
            if abs(d) < 1e-30:
                d = 1e-30
            c = 1.0 + aa / c
            if abs(c) < 1e-30:
                c = 1e-30
            d = 1.0 / d
            h *= d * c
            aa = -(a + m) * (a + b + m) * x / ((a + m2) * (a + m2 + 1.0))
            d = 1.0 + aa * d
            if abs(d) < 1e-30:
                d = 1e-30
            c = 1.0 + aa / c
            if abs(c) < 1e-30:
                c = 1e-30
            d = 1.0 / d
            delta = d * c
            h *= delta
            if abs(delta - 1.0) < eps:
                break
        return h
    cf = betacf(a, b, x)
    return math.exp(a * math.log(x) + b * math.log(1.0 - x) - lbeta) * cf / a


def _student_t_two_tailed_p(t_stat, df):
    if df <= 0:
        return 1.0
    x = df / (df + t_stat * t_stat)
    if t_stat > 0:
        prob = 1.0 - 0.5 * _regularized_incomplete_beta(x, df / 2.0, 0.5)
    else:
        prob = 0.5 * _regularized_incomplete_beta(x, df / 2.0, 0.5)
    return min(1.0, max(0.0, 2.0 * (1.0 - prob)))


def _compute_linear_trend_significance(years, values):
    if len(years) < 3:
        return None
    x = [float(y) for y in years]
    y = [float(v) for v in values]
    n = len(x)
    x_mean = sum(x) / n
    y_mean = sum(y) / n
    sxx = sum((xi - x_mean) ** 2 for xi in x)
    if sxx == 0:
        return None
    slope = sum((xi - x_mean) * (yi - y_mean) for xi, yi in zip(x, y)) / sxx
    intercept = y_mean - slope * x_mean
    residuals = [yi - (slope * xi + intercept) for xi, yi in zip(x, y)]
    ss_res = sum(r * r for r in residuals)
    if n <= 2:
        return None
    se_slope = math.sqrt(ss_res / (n - 2) / sxx) if ss_res >= 0 else None
    if not se_slope or se_slope == 0:
        return None
    t_stat = slope / se_slope
    p_value = _student_t_two_tailed_p(abs(t_stat), n - 2)
    return {
        'slope': slope,
        'intercept': intercept,
        't_stat': t_stat,
        'p_value': p_value,
        'n': n,
    }


def population_stats_context():
    stats_total = int(MERGED_DF.shape[0])
    stats_ed_series = MERGED_DF.get("ED_ZWS")
    stats_ed_distribution = []
    stats_ed23_analysis = None

    if stats_ed_series is not None:
        ed_clean = (
            stats_ed_series.astype(str)
            .str.strip()
            .replace({"": pd.NA, "nan": pd.NA, "None": pd.NA, "none": pd.NA})
        )
        stats_ed_evaluated = int(ed_clean.notna().sum())
        stats_ed_percent = float((stats_ed_evaluated / stats_total * 100) if stats_total else 0)

        ed_count_evaluated = int(ed_clean.notna().sum())
        roentgen_quote = (ed_count_evaluated / stats_total * 100) if stats_total > 0 else 0.0

        if "geburtsjahr" in MERGED_DF.columns:
            birth_year_source = MERGED_DF["geburtsjahr"]
        elif "birthyear_clean" in MERGED_DF.columns:
            birth_year_source = MERGED_DF["birthyear_clean"]
        else:
            birth_year_source = MERGED_DF.get("Wurfdatum")

        birth_year = (
            birth_year_source.astype(str)
            .str.extract(r"(\d{4})")[0]
            .where(lambda s: s.str.fullmatch(r"\d{4}"), pd.NA)
        )

        dist_df = (
            MERGED_DF.loc[ed_clean.notna() & birth_year.notna(), ["ED_ZWS"]]
            .assign(birth_year=birth_year)
            .assign(birth_year_int=lambda d: pd.to_numeric(d["birth_year"], errors="coerce"))
            .loc[lambda d: d["birth_year_int"].notna() & (d["birth_year_int"] >= 2000) & (d["birth_year_int"] != 2025)]
            .groupby(["birth_year", "ED_ZWS"])
            .size()
            .reset_index(name="count")
        )
        if not dist_df.empty:
            dist_df["year_total"] = dist_df.groupby("birth_year")["count"].transform("sum")
            year_pop = birth_year.dropna().value_counts().to_dict()
            dist_df["year_population"] = dist_df["birth_year"].map(year_pop).fillna(0).astype(int)
            dist_df["percent"] = dist_df["count"] / dist_df["year_total"] * 100
            dist_df["birth_year_int"] = pd.to_numeric(dist_df["birth_year"], errors="coerce").fillna(0).astype(int)
            dist_df = dist_df.sort_values(["birth_year_int", "count"], ascending=[True, False]).drop(columns=["birth_year_int"])
            stats_ed_distribution = dist_df.to_dict(orient="records")

            ed23_df = (
                dist_df.loc[dist_df["ED_ZWS"].astype(str).isin(["2.0", "3.0", "2", "3"]), ["birth_year", "percent"]]
                .groupby("birth_year")["percent"]
                .sum()
                .reset_index()
                .sort_values("birth_year")
            )
            if len(ed23_df) >= 3:
                trend = _compute_linear_trend_significance(ed23_df["birth_year"].astype(int).tolist(), ed23_df["percent"].astype(float).tolist())
                if trend:
                    p_value = trend["p_value"]
                    stats_ed23_analysis = {
                        "is_significant": p_value < 0.05,
                        "p_value": p_value,
                        "interpretation": "Der Anteil schwererer ED-Befunde zeigt im betrachteten Zeitraum keinen statistisch gesicherten Trend."
                    }
    else:
        stats_ed_evaluated = 0
        stats_ed_percent = 0.0
        roentgen_quote = 0.0

    return {
        "stats_total": stats_total,
        "stats_ed_evaluated": stats_ed_evaluated,
        "stats_ed_percent": stats_ed_percent,
        "roentgen_quote": roentgen_quote,
        "stats_ed_distribution": stats_ed_distribution,
        "stats_ed23_analysis": stats_ed23_analysis,
    }


@app.route("/login", methods=["GET", "POST"])
def login():
    next_url = request.args.get("next") or request.form.get("next") or url_for("landing")
    if not is_safe_next_url(next_url):
        next_url = url_for("landing")

    error = None
    if request.method == "POST":
        username = request.form.get("username", "")
        password = request.form.get("password", "")
        username_ok = hmac.compare_digest(username, AUTH_USERNAME)
        password_ok = hmac.compare_digest(password, AUTH_PASSWORD)

        if username_ok and password_ok:
            session.clear()
            session["authenticated"] = True
            session["username"] = username
            return redirect(next_url)

        error = "Benutzername oder Passwort ist nicht korrekt."

    return render_template("login.html", error=error, next_url=next_url)


@app.route("/logout", methods=["POST"])
def logout():
    session.clear()
    return redirect(url_for("login"))


@app.route("/")
def landing():
    """Welcome page with entry points into the app."""
    return render_template("landing.html")


@app.route("/dogs", methods=["GET", "POST"])
def dog_search_home():
    """Compatibility route for the old dog search entry page."""
    query = request.values.get("q", "").strip()
    if query:
        return redirect(url_for("search_results", q=query, page=1))

    return redirect(url_for("search_results"))


@app.route("/info")
def info():
    return render_template("info.html", **population_stats_context())


@app.route("/compare")
def compare_watchlist():
    return render_template("compare.html")


@app.route("/dog_suggest")
def dog_suggest():
    ensure_pairing_search_columns()
    query = request.args.get("q", "").strip()
    sex = request.args.get("sex", "").strip()
    min_age = parse_int_filter(request.args.get("min_age"))
    max_age = parse_int_filter(request.args.get("max_age"))
    has_age_filter = min_age is not None or max_age is not None
    if len(query) < 2 and not has_age_filter:
        return jsonify([])

    q = query.lower()
    if len(query) >= 2:
        matches = MERGED_DF[
            MERGED_DF["_search_name"].str.contains(q, na=False, regex=False)
            | MERGED_DF["_search_zbnr"].str.contains(q, na=False, regex=False)
            | MERGED_DF["_search_zbnr_norm"].str.contains(q, na=False, regex=False)
        ]
    else:
        matches = MERGED_DF

    if sex in {"H", "R"}:
        matches = matches[matches["_sex_clean"] == sex]

    if sex == "R":
        matches = apply_age_filter(matches, min_age=min_age, max_age=max_age)

    suggestions = []
    for row in matches.head(20).to_dict(orient="records"):
        name = clean_text(row.get("Name")) or "unbekannt"
        zbnr = clean_text(row.get("ZBNr_norm")) or clean_text(row.get("ZBNr"))
        age = calculate_age_years(row)
        if not zbnr:
            continue
        age_label = f" · {age} Jahre" if age is not None else ""
        suggestions.append(
            {
                "label": f"{name}{age_label} | {zbnr}",
                "name": name,
                "zbnr": zbnr,
                "sex": clean_text(row.get("Geschlecht")),
                "age": age,
            }
        )

    return jsonify(suggestions)


@app.route("/pairing")
def pairing():
    sire_input = request.args.get("sire", "").strip()
    selected_sire = request.args.get("selected_sire", "").strip()
    dam_input = request.args.get("dam", "").strip()
    sire_min_age = request.args.get("sire_min_age", "").strip()
    sire_max_age = request.args.get("sire_max_age", "").strip()
    sire_max_ebv = request.args.get("sire_max_ebv", "").strip()
    sire_min_offspring = request.args.get("sire_min_offspring", "").strip()
    avoid_carrier_matches = request.args.get("avoid_carrier_matches", "").strip() == "1"
    excluded_ancestor_zbnrs = parse_excluded_ancestor_values(request.args.getlist("excluded_ancestor_zbnrs"))
    sire_search = request.args.get("sire_search", "").strip()
    sire_page = request.args.get("sire_page", "1").strip()
    sire_sort_by = request.args.get("sire_sort_by", "zuchtwert").strip().lower()
    sire_sort_dir = request.args.get("sire_sort_dir", "asc").strip().lower()
    min_age = parse_int_filter(sire_min_age)
    max_age = parse_int_filter(sire_max_age)
    max_ebv = parse_int_filter(sire_max_ebv)
    min_offspring = parse_int_filter(sire_min_offspring)
    try:
        sire_page = max(1, int(sire_page))
    except Exception:
        sire_page = 1
    if sire_sort_dir not in {"asc", "desc"}:
        sire_sort_dir = "asc"

    show_sire_results = sire_search == "1"
    sire_page_size = 15
    sire_candidates = []
    sire_total = 0
    sire_page_count = 0
    dam_preview = resolve_dog(dam_input, required_sex="H") if dam_input else None
    if show_sire_results:
        sire_df = get_sire_candidates(
            min_age=min_age,
            max_age=max_age,
            max_ebv=max_ebv,
            min_offspring=min_offspring,
            dam_row=dam_preview,
            avoid_carrier_matches=avoid_carrier_matches,
            excluded_ancestor_zbnrs=excluded_ancestor_zbnrs,
            query=sire_input,
            sort_by=sire_sort_by,
            sort_dir=sire_sort_dir,
        )
        sire_total = int(sire_df.shape[0])
        sire_page_count = max(1, math.ceil(sire_total / sire_page_size)) if sire_total else 0
        if sire_page_count and sire_page > sire_page_count:
            sire_page = sire_page_count
        start = (sire_page - 1) * sire_page_size
        sire_candidates = [
            dog_summary(row)
            for row in sire_df.iloc[start : start + sire_page_size].to_dict(orient="records")
        ]

    context = {
        "sire_input": sire_input,
        "selected_sire": selected_sire,
        "dam_input": dam_input,
        "dam_summary": None,
        "sire_min_age": sire_min_age,
        "sire_max_age": sire_max_age,
        "sire_max_ebv": sire_max_ebv,
        "sire_min_offspring": sire_min_offspring,
        "avoid_carrier_matches": avoid_carrier_matches,
        "excluded_ancestor_zbnrs": excluded_ancestor_zbnrs,
        "excluded_ancestors": excluded_ancestor_summaries(excluded_ancestor_zbnrs),
        "sire_search": sire_search,
        "sire_candidates": sire_candidates,
        "sire_total": sire_total,
        "sire_page": sire_page,
        "sire_page_count": sire_page_count,
        "sire_sort_by": sire_sort_by,
        "sire_sort_dir": sire_sort_dir,
        "result": None,
        "error": None,
    }

    if dam_preview is not None:
        context["dam_summary"] = dog_summary(dam_preview)

    if selected_sire or dam_input:
        sire = resolve_dog(selected_sire, required_sex="R") if selected_sire else None
        dam = dam_preview

        if sire is None or dam is None:
            if dam_input and dam is None:
                context["error"] = "Hündin nicht gefunden oder falsches Geschlecht."
            elif selected_sire and not dam_input:
                context["error"] = "Bitte zuerst eine Hündin auswählen."
            elif selected_sire and sire is None:
                context["error"] = "Rüde nicht gefunden oder falsches Geschlecht."
        else:
            if not dog_matches_age(sire, min_age=min_age, max_age=max_age):
                context["error"] = "Der ausgewählte Rüde passt nicht zum angegebenen Altersfilter."
                return render_template("pairing.html", **context)
            if not dog_matches_max_ebv(sire, max_ebv=max_ebv):
                context["error"] = "Der ausgewählte Rüde passt nicht zum angegebenen maximalen ED-Zuchtwert."
                return render_template("pairing.html", **context)
            if not dog_matches_min_offspring(sire, min_offspring=min_offspring):
                context["error"] = "Der ausgewählte Rüde passt nicht zur angegebenen Mindestanzahl an Nachkommen."
                return render_template("pairing.html", **context)
            carrier_conflicts = carrier_conflicts_with_dam(sire, dam) if avoid_carrier_matches else []
            if carrier_conflicts:
                context["error"] = "Der ausgewählte Rüde passt nicht zur Gentest-Regel: Träger × Träger bei " + ", ".join(carrier_conflicts) + "."
                return render_template("pairing.html", **context)
            if dog_has_excluded_ancestor(sire, excluded_ancestor_zbnrs):
                context["error"] = "Der ausgewählte Rüde hat mindestens einen ausgeschlossenen Hund in der Ahnentafel."
                return render_template("pairing.html", **context)

            planned_zbnr, pairing_index = make_pairing_index(sire, dam)
            max_gen = 5

            sire_ebv = dog_ebv_value(sire)
            dam_ebv = dog_ebv_value(dam)
            planned_ebv = (
                (sire_ebv + dam_ebv) / 2
                if sire_ebv is not None and dam_ebv is not None
                else None
            )

            coi = pt.calculate_coi_for_zbnr(
                pairing_index,
                planned_zbnr,
                max_generations=max_gen,
            )
            avk = pt.calculate_avk_for_zbnr(
                pairing_index,
                planned_zbnr,
                max_generations=max_gen,
            )
            pedigree = pt.create_pedigree_html_for_zbnr(
                df_or_index=pairing_index,
                start_zbnr=planned_zbnr,
                max_generations=max_gen,
                include_coi=False,
                include_avk=False,
            )

            context["result"] = {
                "sire": dog_summary(sire),
                "dam": dog_summary(dam),
                "planned_ebv": planned_ebv,
                "planned_ebv_display": (
                    f"{planned_ebv:.1f}".replace(".", ",")
                    if planned_ebv is not None
                    else "—"
                ),
                "coi_percent": coi.get("coi_percent"),
                "coi_display": format_percent_or_dash(coi.get("coi_percent")),
                "avk_percent": avk.get("avk_known_percent"),
                "avk_display": format_percent_or_dash(avk.get("avk_known_percent")),
                "complete_generation": avk.get("deepest_complete_generation_in_data"),
                "pedigree_html": extract_embeddable_html(pedigree.get("html", "")),
            }

    return render_template("pairing.html", **context)


@app.route("/search", methods=["GET"])
def search_results():
    """Search results page."""
    query = request.args.get("q", "").strip()
    page = request.args.get("page", "1")
    try:
        page = max(1, int(page))
    except ValueError:
        page = 1

    page_size = 10
    sort_by = request.args.get("sort_by", "name").lower()
    sort_dir = request.args.get("sort_dir", "asc").lower()
    if sort_dir not in {"asc", "desc"}:
        sort_dir = "asc"

    if not query:
        return render_template(
            "search_results.html",
            query="",
            results=[],
            page=1,
            page_count=0,
            total_matches=0,
            query_encoded="",
            sort_by=sort_by,
            sort_dir=sort_dir,
            no_results=False,
            search_started=False,
        )
    
    q = query.lower()
    df = MERGED_DF

    # search in Name and ZBNr columns
    mask = (
        df["Name"].fillna("").str.lower().str.contains(q, na=False)
        | df["ZBNr"].fillna("").str.lower().str.contains(q, na=False)
    )

    matches = df[mask].copy()
    
    # Build sort helper columns
    matches["sort_zbnr"] = (
        matches["ZBNr_norm"].fillna(matches["ZBNr"]) if "ZBNr_norm" in matches.columns else matches["ZBNr"]
    )
    matches["sort_hd"] = (
        matches["HD_Grad"].fillna(matches.get("HD", pd.Series([None] * len(matches))))
        if "HD_Grad" in matches.columns
        else matches.get("HD", pd.Series([None] * len(matches)))
    )
    ed_rechts = matches["ED_rechts"] if "ED_rechts" in matches.columns else pd.Series([None] * len(matches))
    ed_rechts_raw = matches["ED_rechts_raw"] if "ED_rechts_raw" in matches.columns else pd.Series([None] * len(matches))
    ed_links = matches["ED_links"] if "ED_links" in matches.columns else pd.Series([None] * len(matches))
    matches["sort_ed"] = ed_rechts.fillna(ed_rechts_raw).fillna(ed_links)
    matches["sort_zuchtwert"] = pd.to_numeric(
        matches.get("EBV", pd.Series([None] * len(matches))), errors="coerce"
    ).fillna(pd.to_numeric(matches.get("ed_zw_0_10_niedrig_gut", pd.Series([None] * len(matches))), errors="coerce"))
    matches["sort_konfidenz"] = pd.to_numeric(
        matches.get("Confidenz", pd.Series([None] * len(matches))), errors="coerce"
    ).fillna(pd.to_numeric(matches.get("reliability_prozent", pd.Series([None] * len(matches))), errors="coerce"))
    matches["sort_nachkommen"] = pd.to_numeric(
        matches.get("AnzNachkommen", pd.Series([None] * len(matches))), errors="coerce"
    )
    matches["sort_wurfdatum"] = matches.get("Wurfdatum", pd.Series([None] * len(matches)))

    def coalesce_text(series):
        if series is None:
            return pd.Series([pd.NA] * len(matches), index=matches.index)
        text = series.astype(str).str.strip().replace({"": pd.NA, "nan": pd.NA, "None": pd.NA, "none": pd.NA})
        return text.where(text.notna(), pd.NA)

    def first_nonempty(cols):
        result = pd.Series([pd.NA] * len(matches), index=matches.index)
        for col in cols:
            if col in matches.columns:
                candidate = coalesce_text(matches[col])
                result = result.fillna(candidate)
        return result

    matches["ed_status"] = first_nonempty(
        ["ED_rechts", "ED_rechts_raw", "ED_links", "ED_links_raw", "ED_geroentgt", "ED_ZWS"]
    )

    def extract_year(series):
        if series is None:
            return pd.Series([pd.NA] * len(matches), index=matches.index)
        year = series.astype(str).str.extract(r"(\d{4})")[0]
        return year.where(year.str.fullmatch(r"\d{4}"), pd.NA)

    if "geburtsjahr" in matches.columns:
        birth_year_source = matches["geburtsjahr"]
    elif "birthyear_clean" in matches.columns:
        birth_year_source = matches["birthyear_clean"]
    else:
        birth_year_source = matches.get("Wurfdatum")

    matches["birth_year"] = extract_year(birth_year_source)

    sort_column_map = {
        "name": "Name",
        "zbnr": "sort_zbnr",
        "wurfdatum": "sort_wurfdatum",
        "rkey": "Rkey",
        "hd": "sort_hd",
        "ed": "sort_ed",
        "zuchtwert": "sort_zuchtwert",
        "konfidenz": "sort_konfidenz",
        "nachkommen": "sort_nachkommen",
    }
    sort_column = sort_column_map.get(sort_by, "Name")
    ascending = sort_dir == "asc"
    if sort_column in matches.columns:
        matches = matches.sort_values(by=sort_column, ascending=ascending, na_position="last")

    total_matches = int(matches.shape[0])
    
    if total_matches == 0:
        return render_template(
            "search_results.html",
            query=query,
            results=[],
            page=page,
            page_count=0,
            total_matches=0,
            query_encoded=quote_plus(query),
            sort_by=sort_by,
            sort_dir=sort_dir,
            no_results=True,
            search_started=True,
        )
    
    page_count = max(1, math.ceil(total_matches / page_size))
    if page > page_count:
        page = page_count

    recs = matches.iloc[(page - 1) * page_size : page * page_size].to_dict(orient="records")

    results = []
    for r in recs:
        z = r.get("ZBNr_norm") or r.get("ZBNr")
        hd = clean_text(r.get("HD_Grad")) or clean_text(r.get("HD")) or None
        ed = clean_text(r.get("ED_rechts")) or clean_text(r.get("ED_rechts_raw")) or clean_text(r.get("ED_links")) or None
        zucht_raw = r.get("EBV") or r.get("ed_zw_0_10_niedrig_gut")
        wurfdatum = clean_text(r.get("Wurfdatum"))
        konf_raw = r.get("Confidenz") or r.get("reliability_prozent") or r.get("reliability")

        def to_int(v):
            try:
                return int(round(float(v)))
            except Exception:
                return None

        konf = to_int(konf_raw)
        zucht = to_int(zucht_raw)

        res = r.copy()
        res["zbnr_link"] = quote_plus(str(z)) if z else ""
        res["zbnr"] = z
        res["hd"] = hd
        for key, column in GENETIC_TEST_FIELDS:
            res[key] = clean_text(r.get(column))
        res["ed"] = ed
        res["konfidenz"] = konf
        res["zuchtwert"] = zucht
        res["anz_nachkommen"] = dog_offspring_count(r)
        res["wurfdatum"] = wurfdatum
        res["name"] = r.get("Name", "unbekannt")
        res["geschlecht"] = r.get("Geschlecht") or r.get("sex") or "unbekannt"
        res["vater"] = r.get("Vater") or "unbekannt"
        res["mutter"] = r.get("Mutter") or "unbekannt"
        res["birth_year"] = clean_text(r.get("birth_year"))
        
        # Classification for display
        res["zuchtwert_class"] = "" #get_breeding_value_classification(zucht)
        res["konfidenz_class"] = get_reliability_classification(konf)
        
        results.append(res)

    return render_template(
        "search_results.html",
        query=query,
        results=results,
        page=page,
        page_count=page_count,
        total_matches=total_matches,
        query_encoded=quote_plus(query),
        sort_by=sort_by,
        sort_dir=sort_dir,
        no_results=(total_matches == 0),
        search_started=True,
    )


@app.route("/pedigree")
def pedigree():
    zbnr = request.args.get("zbnr")
    if not zbnr:
        return redirect(url_for("search"))

    max_gen = int(request.args.get("gens", 5))

    res = pt.create_pedigree_html_for_zbnr(
        df_or_index=ZBNR_INDEX,
        start_zbnr=zbnr,
        max_generations=max_gen,
        include_coi=True,
        include_avk=True,
    )

    html = res.get("html", "<p>Keine Daten</p>")

    return Response(html, mimetype="text/html")


@app.route("/pedigree.json")
def pedigree_json():
    zbnr = request.args.get("zbnr")
    if not zbnr:
        return jsonify({"error": "no zbnr provided"}), 400

    max_gen = int(request.args.get("gens", 5))

    try:
        res = pt.create_pedigree_json_for_zbnr(
            df_or_index=ZBNR_INDEX,
            start_zbnr=zbnr,
            max_generations=max_gen,
            include_coi=True,
            include_avk=True,
        )
    except Exception as e:
        return jsonify({"error": str(e)}), 500

    return jsonify(res)


@app.route("/pedigree_metrics")
def pedigree_metrics():
    zbnr = request.args.get("zbnr")
    if not zbnr:
        return jsonify({"error": "no zbnr provided"}), 400

    max_gen = int(request.args.get("gens", 5))

    try:
        coi = pt.calculate_coi_for_zbnr(
            ZBNR_INDEX,
            zbnr,
            max_generations=max_gen,
        )
        avk = pt.calculate_avk_for_zbnr(
            ZBNR_INDEX,
            zbnr,
            max_generations=max_gen,
        )
    except Exception as e:
        return jsonify({"error": str(e)}), 500

    return jsonify(
        {
            "coi_percent": coi.get("coi_percent") if coi else None,
            "avk_known_percent": avk.get("avk_known_percent") if avk else None,
            "deepest_complete_generation_in_data": (
                avk.get("deepest_complete_generation_in_data") if avk else None
            ),
            "deepest_complete_generation_by_zbnr": (
                avk.get("deepest_complete_generation_by_zbnr") if avk else None
            ),
        }
    )


@app.route("/littermates")
def littermates():
    requested_zbnr = clean_text(request.args.get("zbnr"))
    if not requested_zbnr:
        return jsonify({"error": "no zbnr provided"}), 400

    zbnr = pt.normalize_zbnr(requested_zbnr) or requested_zbnr
    dog = ZBNR_INDEX.get(zbnr) or ZBNR_INDEX.get(requested_zbnr)
    if dog is None:
        return jsonify({"error": "dog not found"}), 404

    dog_zbnr = clean_text(dog.get("ZBNr_norm") or dog.get("ZBNr") or zbnr)
    dog_zbnr = pt.normalize_zbnr(dog_zbnr) or dog_zbnr
    father = clean_text(dog.get("vater_zbnr_norm") or dog.get("vater_zbnr"))
    mother = clean_text(dog.get("mutter_zbnr_norm") or dog.get("mutter_zbnr"))
    father = pt.normalize_zbnr(father) or father
    mother = pt.normalize_zbnr(mother) or mother
    litter_date = clean_text(dog.get("Wurfdatum") or dog.get("geburt"))

    def normalized_zbnr(value):
        text = clean_text(value)
        return pt.normalize_zbnr(text) or text

    father_series = MERGED_DF.get("vater_zbnr_norm", pd.Series([""] * len(MERGED_DF))).map(normalized_zbnr)
    mother_series = MERGED_DF.get("mutter_zbnr_norm", pd.Series([""] * len(MERGED_DF))).map(normalized_zbnr)
    date_series = MERGED_DF.get("Wurfdatum", pd.Series([""] * len(MERGED_DF))).map(clean_text)
    zbnr_series = (
        MERGED_DF["ZBNr_norm"].map(normalized_zbnr)
        if "ZBNr_norm" in MERGED_DF.columns
        else MERGED_DF["ZBNr"].map(normalized_zbnr)
    )

    offspring_mask = (father_series == dog_zbnr) | (mother_series == dog_zbnr)
    offspring = []
    for row in (
        MERGED_DF.loc[offspring_mask]
        .sort_values(by=["Wurfdatum", "Name"], na_position="last")
        .to_dict(orient="records")
    ):
        child_summary = dog_summary(row)
        child_father = normalized_zbnr(row.get("vater_zbnr_norm") or row.get("vater_zbnr"))
        child_mother = normalized_zbnr(row.get("mutter_zbnr_norm") or row.get("mutter_zbnr"))
        other_parent_zbnr = child_mother if child_father == dog_zbnr else child_father
        other_parent = parent_display_by_zbnr(other_parent_zbnr)
        child_summary["other_parent"] = other_parent["label"] if other_parent else ""
        child_summary["other_parent_name"] = other_parent["name"] if other_parent else ""
        child_summary["other_parent_zbnr"] = other_parent["zbnr"] if other_parent else ""
        offspring.append(child_summary)

    message = None
    if not father or not mother or not litter_date:
        message = "Für diesen Hund fehlen Vater, Mutter oder Wurfdatum. Wurfgeschwister können deshalb nicht sicher ermittelt werden."
        mask = pd.Series([False] * len(MERGED_DF), index=MERGED_DF.index)
    else:
        mask = (
            (father_series == father)
            & (mother_series == mother)
            & (date_series == litter_date)
            & (zbnr_series != dog_zbnr)
        )

    siblings = [
        dog_summary(row)
        for row in MERGED_DF.loc[mask].sort_values(by="Name", na_position="last").to_dict(orient="records")
    ]

    return jsonify(
        {
            "dog": dog_summary(dog),
            "parents": {
                "father_zbnr": father,
                "mother_zbnr": mother,
            },
            "litter_date": litter_date,
            "littermates": siblings,
            "offspring": offspring,
            "message": message,
        }
    )


@app.route("/pedigree_fragment")
def pedigree_fragment():
    zbnr = request.args.get("zbnr")
    if not zbnr:
        return "", 400

    max_gen = int(request.args.get("gens", 5))

    try:
        res = pt.create_pedigree_html_for_zbnr(
            df_or_index=ZBNR_INDEX,
            start_zbnr=zbnr,
            max_generations=max_gen,
            include_coi=False,
            include_avk=False,
        )

        html = res.get("html", "")
        
        if not html:
            return "<p>Keine Ahnentafel für diesen Hund verfügbar.</p>", 200

        # extract styles and body content to embed in page
        styles = "".join(re.findall(r"<style[^>]*>.*?</style>", html, re.S | re.I))
        m = re.search(r"<body[^>]*>(.*?)</body>", html, re.S | re.I)
        if m:
            body = m.group(1)
        else:
            body = html

        return Response(styles + body, mimetype="text/html")
    except Exception as e:
        import traceback
        print(f"Error loading pedigree for {zbnr}: {e}")
        traceback.print_exc()
        return f"<p>Fehler beim Laden der Ahnentafel: {str(e)}</p>", 500


if __name__ == "__main__":
    app.run(port=5000, debug=True)
