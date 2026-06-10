from pathlib import Path
from urllib.parse import quote_plus
from contextlib import contextmanager
from collections import defaultdict
import json
import logging
import math
from datetime import date
from datetime import datetime
import hmac
import os
import re
import tempfile
import threading
import time
import uuid

from flask import Flask, render_template, request, redirect, url_for, Response, jsonify, session, g

import pedigree_tools as pt
import pandas as pd

try:
    import fcntl
except ImportError:
    fcntl = None


APP_DIR = Path(__file__).parent
BASE_CSV = APP_DIR / "drc-Hunde-mit-eltern-rkey-gentest.csv"
ZWS_CSV = APP_DIR / "ed_zws_results_all_animals.csv"
SCORES_CSV = APP_DIR / "scores_bereinigt_mit_originalname.csv"
USER_DOGS_CSV = Path(os.environ.get("USER_DOGS_CSV", APP_DIR / "user_hunde.csv"))
USER_DOGS_LOCK_FILE = Path(os.environ.get("USER_DOGS_LOCK_FILE", f"{USER_DOGS_CSV}.lock"))
USER_DOGS_LOCK = threading.Lock()
PEDIGREE_IMPORT_STATES = {}
PEDIGREE_IMPORT_STATE_TTL_SECONDS = 30 * 60


app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY") or os.environ.get("FLASK_SECRET_KEY") or "dev-secret-change-me"

logging.basicConfig(level=os.environ.get("LOG_LEVEL", "INFO").upper())
app.logger.setLevel(os.environ.get("LOG_LEVEL", "INFO").upper())

AUTH_USERNAME = os.environ.get("APP_USERNAME", "admin")
AUTH_PASSWORD = os.environ.get("APP_PASSWORD", "admin")

USER_DOG_COLUMNS = [
    "ZBNr",
    "ZBNr_norm",
    "Name",
    "Rasse",
    "Wurfdatum",
    "Geschlecht",
    "HD_Grad",
    "ED_rechts",
    "ED_links",
    "AnzNachkommen",
    "EBV",
    "Confidenz",
    "Verlässlichkeit",
    "ED_ZWS",
    "prcd-PRA",
    "HNPK",
    "SD2",
    "CNM",
    "EIC",
    "ZS",
    "STGD_Status",
    "vater_name",
    "vater_zbnr",
    "vater_zbnr_norm",
    "mutter_name",
    "mutter_zbnr",
    "mutter_zbnr_norm",
    "Vater",
    "Mutter",
    "geburtsjahr",
    "pedigree_status",
    "father_found",
    "mother_found",
    "source",
    "created_at",
    "updated_at",
    "user_notes",
]


def is_authenticated():
    return session.get("authenticated") is True


def is_safe_next_url(value):
    return bool(value) and value.startswith("/") and not value.startswith("//")


def current_return_url():
    return request.full_path.rstrip("?")


def redirect_with_imported_count(return_to, imported_count):
    target = return_to if is_safe_next_url(return_to) else url_for("manage_user_dogs")
    separator = "&" if "?" in target else "?"
    return redirect(f"{target}{separator}imported={imported_count}")


def cleanup_pedigree_import_states():
    now = time.time()
    expired_tokens = [
        token
        for token, item in PEDIGREE_IMPORT_STATES.items()
        if now - item.get("created_at", now) > PEDIGREE_IMPORT_STATE_TTL_SECONDS
    ]
    for token in expired_tokens:
        PEDIGREE_IMPORT_STATES.pop(token, None)


def set_pedigree_import_state(**state):
    cleanup_pedigree_import_states()
    token = uuid.uuid4().hex
    PEDIGREE_IMPORT_STATES[token] = {
        "created_at": time.time(),
        "state": state,
    }
    session["pedigree_import_state_id"] = token


def pedigree_import_context(default_return_to=None):
    cleanup_pedigree_import_states()
    token = session.pop("pedigree_import_state_id", None)
    stored_state = PEDIGREE_IMPORT_STATES.pop(token, None) if token else None
    state = (stored_state or {}).get("state", {})
    return_to = (
        state.get("import_return_to")
        or default_return_to
        or current_return_url()
    )
    if not is_safe_next_url(return_to):
        return_to = url_for("manage_user_dogs")

    return {
        "imported_count": request.args.get("imported", ""),
        "import_errors": state.get("import_errors", []),
        "import_preview": state.get("import_preview", []),
        "import_data_json": state.get("import_data_json", ""),
        "import_modal_open": bool(state.get("import_modal_open") or request.args.get("import_open")),
        "import_root_sex": state.get("import_root_sex", ""),
        "import_text": state.get("import_text", ""),
        "import_return_to": return_to,
    }


SENSITIVE_LOG_KEYS = {
    "password",
    "passwort",
    "secret",
    "token",
    "csrf_token",
    "import_data",
    "pedigree_text",
}


def client_ip():
    forwarded_for = request.headers.get("X-Forwarded-For", "")
    if forwarded_for:
        return forwarded_for.split(",", 1)[0].strip()
    return request.remote_addr or ""


def truncate_log_value(value, max_length=160):
    value = clean_text(value)
    if len(value) <= max_length:
        return value
    return value[: max_length - 1] + "…"


def sanitized_multidict_values(values):
    data = {}
    for key in values.keys():
        if key.lower() in SENSITIVE_LOG_KEYS:
            data[key] = "[redacted]"
            continue

        items = values.getlist(key)
        cleaned = [truncate_log_value(item) for item in items if clean_text(item)]
        if not cleaned:
            continue
        data[key] = cleaned[0] if len(cleaned) == 1 else cleaned[:10]
    return data


def log_event(event, **fields):
    payload = {
        "event": event,
        "user": session.get("username") if has_request_context_safe() else None,
        "path": request.path if has_request_context_safe() else None,
        "endpoint": request.endpoint if has_request_context_safe() else None,
        "ip": client_ip() if has_request_context_safe() else None,
        **fields,
    }
    app.logger.info(json.dumps(payload, ensure_ascii=False, default=str))


def event_duration_ms(started_at):
    if started_at is None:
        return None
    try:
        return round((time.perf_counter() - started_at) * 1000, 1)
    except Exception:
        return None


def safe_float(value):
    if value is None:
        return None
    try:
        number = float(value)
    except Exception:
        return None
    if not math.isfinite(number):
        return None
    return number


def dog_log_identity(row):
    if row is None:
        return {"dog_name": None, "zbnr": None}
    return {
        "dog_name": clean_text(row.get("Name")) or None,
        "zbnr": clean_text(row.get("ZBNr_norm") or row.get("ZBNr")) or None,
    }


def dog_log_name(index, zbnr):
    normalized = pt.normalize_zbnr(zbnr) or clean_text(zbnr)
    row = index.get(normalized) or index.get(clean_text(zbnr)) or {}
    return clean_text(row.get("Name")) or None


def pedigree_completeness_percent(avk_result):
    if not avk_result:
        return None
    known = safe_float(avk_result.get("known_ancestor_positions"))
    possible = safe_float(avk_result.get("possible_ancestor_positions"))
    if known is None or possible in {None, 0}:
        return None
    return round(known / possible * 100, 2)


CLIENT_LOG_EVENTS = {
    "saved_pairing_created",
    "saved_pairing_loaded",
}


def sanitized_client_event_payload(payload):
    if not isinstance(payload, dict):
        return {}
    allowed = {
        "name",
        "defaultName",
        "url",
        "is_update",
        "saved_count",
        "source",
    }
    result = {}
    for key in allowed:
        if key in payload:
            value = payload.get(key)
            if isinstance(value, (bool, int, float)) or value is None:
                result[key] = value
            else:
                result[key] = truncate_log_value(value, max_length=220)
    return result


def has_request_context_safe():
    try:
        request.path
        return True
    except RuntimeError:
        return False


@app.before_request
def start_request_logging():
    g.request_started_at = time.perf_counter()


@app.before_request
def require_login():
    public_endpoints = {"login", "static"}
    if request.endpoint in public_endpoints:
        return None

    if is_authenticated():
        return None

    return redirect(url_for("login", next=request.full_path if request.query_string else request.path))


@app.after_request
def log_request(response):
    started_at = getattr(g, "request_started_at", None)
    duration_ms = (
        round((time.perf_counter() - started_at) * 1000, 1)
        if started_at is not None
        else None
    )
    log_event(
        "request",
        method=request.method,
        status=response.status_code,
        duration_ms=duration_ms,
        query=sanitized_multidict_values(request.args),
        form=sanitized_multidict_values(request.form) if request.method != "GET" else {},
        user_agent=truncate_log_value(request.headers.get("User-Agent", ""), max_length=220),
    )
    return response


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

    merged_df = append_user_dogs(merged_df)
    merged_df = attach_epi_scores(merged_df)
    index, duplicates = pt.build_zbnr_index(merged_df)

    return merged_df, index


def reload_data():
    global MERGED_DF, ZBNR_INDEX, PAIRING_SEARCH_CACHE_DATE
    MERGED_DF, ZBNR_INDEX = load_data()
    PAIRING_SEARCH_CACHE_DATE = None


def update_data_cache_with_user_records(records):
    """Ersetzt/ergänzt wenige User-Datensätze im Cache ohne kompletten CSV-Reload."""
    global MERGED_DF, ZBNR_INDEX, PAIRING_SEARCH_CACHE_DATE

    if not records:
        return

    records_df = pd.DataFrame(records).fillna("")
    if records_df.empty:
        return

    for column in records_df.columns:
        if column not in MERGED_DF.columns:
            MERGED_DF[column] = ""
    for column in MERGED_DF.columns:
        if column not in records_df.columns:
            records_df[column] = ""

    records_df = records_df[MERGED_DF.columns].fillna("")
    records_df = pt.normalize_zbnr_columns(records_df)
    records_df = attach_epi_scores(records_df)

    record_zbnrs = {
        pt.normalize_zbnr(value)
        for value in records_df.get("ZBNr_norm", pd.Series(dtype=str)).fillna("").astype(str)
        if pt.normalize_zbnr(value)
    }
    if not record_zbnrs:
        return

    current_zbnrs = MERGED_DF.get("ZBNr_norm", pd.Series([""] * len(MERGED_DF), index=MERGED_DF.index))
    keep_mask = ~current_zbnrs.fillna("").map(lambda value: pt.normalize_zbnr(value) in record_zbnrs)
    MERGED_DF = pd.concat([MERGED_DF.loc[keep_mask], records_df], ignore_index=True)

    for record in records_df.to_dict(orient="records"):
        zbnr = pt.normalize_zbnr(record.get("ZBNr_norm") or record.get("ZBNr"))
        if zbnr:
            record["ZBNr_norm"] = zbnr
            ZBNR_INDEX[zbnr] = record

    PAIRING_SEARCH_CACHE_DATE = None


def empty_user_dogs_df():
    return pd.DataFrame(columns=USER_DOG_COLUMNS)


def load_user_dogs_df():
    if not USER_DOGS_CSV.exists():
        return empty_user_dogs_df()

    try:
        df = pd.read_csv(USER_DOGS_CSV, dtype=str, encoding="utf-8-sig").fillna("")
    except Exception:
        return empty_user_dogs_df()

    for column in USER_DOG_COLUMNS:
        if column not in df.columns:
            df[column] = ""

    df = df[USER_DOG_COLUMNS].copy()
    df = pt.normalize_zbnr_columns(df)
    df["source"] = df["source"].replace("", "user")
    return df.fillna("")


def append_user_dogs(merged_df):
    user_df = load_user_dogs_df()
    if user_df.empty:
        return merged_df

    merged_df = merged_df.copy()
    for column in user_df.columns:
        if column not in merged_df.columns:
            merged_df[column] = ""
    for column in merged_df.columns:
        if column not in user_df.columns:
            user_df[column] = ""

    user_zbnrs = {
        pt.normalize_zbnr(value)
        for value in user_df.get("ZBNr_norm", pd.Series(dtype=str)).fillna("").astype(str)
        if pt.normalize_zbnr(value)
    }
    if user_zbnrs and "ZBNr_norm" in merged_df.columns:
        merged_df = merged_df[
            ~merged_df["ZBNr_norm"].fillna("").map(lambda value: pt.normalize_zbnr(value) in user_zbnrs)
        ].copy()

    combined = pd.concat([merged_df, user_df[merged_df.columns]], ignore_index=True)
    combined = pt.normalize_zbnr_columns(combined)
    return combined


@contextmanager
def locked_user_dogs_file():
    USER_DOGS_LOCK_FILE.parent.mkdir(parents=True, exist_ok=True)
    with USER_DOGS_LOCK_FILE.open("a+", encoding="utf-8") as lock_file:
        if fcntl is not None:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            if fcntl is not None:
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def normalize_dog_name_for_score(value):
    text = "" if value is None or pd.isna(value) else str(value)
    text = text.replace("\ufeff", "")
    text = re.sub(r"\s+", " ", text).strip()
    return text.casefold()


def load_epi_score_map():
    if not SCORES_CSV.exists():
        return {}

    try:
        score_df = pd.read_csv(SCORES_CSV, dtype=str, encoding="utf-8-sig")
    except Exception:
        return {}

    score_map = {}
    for row in score_df.to_dict(orient="records"):
        score = "" if row.get("Score") is None or pd.isna(row.get("Score")) else str(row.get("Score")).strip()
        if not score:
            continue
        for column in ("Hundename", "Original_Hundename"):
            key = normalize_dog_name_for_score(row.get(column))
            if key and key not in score_map:
                score_map[key] = score
    return score_map


def attach_epi_scores(df):
    score_map = load_epi_score_map()
    if not score_map or "Name" not in df.columns:
        return df

    df = df.copy()
    normalized_names = df["Name"].map(normalize_dog_name_for_score)
    df["EpiScore"] = normalized_names.map(score_map).fillna("")
    return df


def user_dog_path_label():
    return str(USER_DOGS_CSV)


def extract_birth_year(value):
    text = clean_text(value)
    match = re.search(r"\b(\d{4})\b", text)
    return match.group(1) if match else ""


def next_user_zbnr(user_df):
    highest = 0
    for value in user_df.get("ZBNr", pd.Series(dtype=str)).fillna("").astype(str):
        match = re.fullmatch(r"USER-(\d+)", value.strip().upper())
        if match:
            highest = max(highest, int(match.group(1)))
    return f"USER-{highest + 1:06d}"


def parent_from_form(value, required_sex):
    raw = clean_text(value)
    if not raw:
        return "", ""

    dog = resolve_dog(raw, required_sex=required_sex)
    if dog is not None:
        zbnr = clean_text(dog.get("ZBNr_norm") or dog.get("ZBNr"))
        name = clean_text(dog.get("Name"))
        return zbnr, name

    zbnr = parse_selected_zbnr(raw)
    if zbnr != raw:
        name = raw.rsplit("|", 1)[0].strip()
        return zbnr, name

    return raw, ""


def bool_text(value):
    return "True" if value else "False"


def clean_form_value(name):
    return clean_text(request.form.get(name, ""))


def user_dog_form_defaults():
    return {
        "zbnr": "",
        "name": "",
        "geschlecht": "",
        "rasse": "Labrador-Retriever",
        "wurfdatum": "",
        "vater": "",
        "mutter": "",
        "hd": "",
        "ed_rechts": "",
        "ed_links": "",
        "anz_nachkommen": "",
        "ebv": "",
        "confidenz": "",
        "verlaesslichkeit": "",
        "ed_zws": "",
        "prcd_pra": "",
        "hnpk": "",
        "sd2": "",
        "cnm": "",
        "eic": "",
        "zs": "",
        "stgd_status": "",
        "user_notes": "",
    }


def user_dog_form_from_request():
    values = user_dog_form_defaults()
    for key in values:
        values[key] = clean_form_value(key)
    return values


def build_user_dog_record(values, existing_user_df):
    zbnr = pt.normalize_zbnr(values.get("zbnr")) or next_user_zbnr(existing_user_df)
    zbnr_norm = pt.normalize_zbnr(zbnr) or zbnr
    name = clean_text(values.get("name"))
    geschlecht = clean_text(values.get("geschlecht")).upper()
    wurfdatum = clean_text(values.get("wurfdatum"))
    vater_zbnr, vater_name = parent_from_form(values.get("vater"), "R")
    mutter_zbnr, mutter_name = parent_from_form(values.get("mutter"), "H")
    now = datetime.now().isoformat(timespec="seconds")

    return {
        "ZBNr": zbnr,
        "ZBNr_norm": zbnr_norm,
        "Name": name,
        "Rasse": clean_text(values.get("rasse")) or "Labrador-Retriever",
        "Wurfdatum": wurfdatum,
        "Geschlecht": geschlecht,
        "HD_Grad": clean_text(values.get("hd")),
        "ED_rechts": clean_text(values.get("ed_rechts")),
        "ED_links": clean_text(values.get("ed_links")),
        "AnzNachkommen": clean_text(values.get("anz_nachkommen")),
        "EBV": clean_text(values.get("ebv")),
        "Confidenz": clean_text(values.get("confidenz")),
        "Verlässlichkeit": clean_text(values.get("verlaesslichkeit")),
        "ED_ZWS": clean_text(values.get("ed_zws")),
        "prcd-PRA": clean_text(values.get("prcd_pra")),
        "HNPK": clean_text(values.get("hnpk")),
        "SD2": clean_text(values.get("sd2")),
        "CNM": clean_text(values.get("cnm")),
        "EIC": clean_text(values.get("eic")),
        "ZS": clean_text(values.get("zs")),
        "STGD_Status": clean_text(values.get("stgd_status")),
        "vater_name": vater_name,
        "vater_zbnr": vater_zbnr,
        "vater_zbnr_norm": pt.normalize_zbnr(vater_zbnr) or "",
        "mutter_name": mutter_name,
        "mutter_zbnr": mutter_zbnr,
        "mutter_zbnr_norm": pt.normalize_zbnr(mutter_zbnr) or "",
        "Vater": vater_name or vater_zbnr,
        "Mutter": mutter_name or mutter_zbnr,
        "geburtsjahr": extract_birth_year(wurfdatum),
        "pedigree_status": "ok",
        "father_found": bool_text(bool(vater_zbnr and resolve_dog(vater_zbnr, required_sex="R") is not None)),
        "mother_found": bool_text(bool(mutter_zbnr and resolve_dog(mutter_zbnr, required_sex="H") is not None)),
        "source": "user",
        "created_at": now,
        "updated_at": now,
        "user_notes": clean_text(values.get("user_notes")),
    }


def validate_user_dog(values, record, existing_user_df):
    errors = []
    if not record["Name"]:
        errors.append("Bitte gib einen Namen ein.")
    if record["Geschlecht"] not in {"R", "H"}:
        errors.append("Bitte wähle das Geschlecht Rüde oder Hündin.")

    zbnr_norm = pt.normalize_zbnr(record["ZBNr_norm"] or record["ZBNr"])
    if not zbnr_norm:
        errors.append("Die ZBNr konnte nicht ermittelt werden.")
    elif zbnr_norm in ZBNR_INDEX:
        errors.append("Diese ZBNr existiert bereits im Datenbestand.")

    existing_user_zbnrs = {
        pt.normalize_zbnr(value)
        for value in existing_user_df.get("ZBNr_norm", pd.Series(dtype=str)).fillna("").astype(str)
        if pt.normalize_zbnr(value)
    }
    if zbnr_norm in existing_user_zbnrs:
        errors.append("Diese ZBNr existiert bereits in den manuell hinzugefügten Hunden.")

    if record["vater_zbnr_norm"] and record["vater_zbnr_norm"] == zbnr_norm:
        errors.append("Der Hund kann nicht sein eigener Vater sein.")
    if record["mutter_zbnr_norm"] and record["mutter_zbnr_norm"] == zbnr_norm:
        errors.append("Der Hund kann nicht seine eigene Mutter sein.")

    return errors


def write_user_dogs_df(df):
    USER_DOGS_CSV.parent.mkdir(parents=True, exist_ok=True)
    for column in USER_DOG_COLUMNS:
        if column not in df.columns:
            df[column] = ""
    df = df[USER_DOG_COLUMNS].fillna("")

    with tempfile.NamedTemporaryFile(
        "w",
        encoding="utf-8",
        newline="",
        delete=False,
        dir=USER_DOGS_CSV.parent,
        prefix=".user_hunde.",
        suffix=".tmp",
    ) as tmp:
        temp_path = Path(tmp.name)
        df.to_csv(tmp, index=False)

    temp_path.replace(USER_DOGS_CSV)


def preorder_pedigree_slots(max_generation=4):
    def walk(slot):
        generation = slot.bit_length() - 1
        if generation > max_generation:
            return []
        return [slot] + walk(slot * 2) + walk(slot * 2 + 1)

    return walk(1)


def imported_slot_sex(slot, root_sex=""):
    if slot == 1:
        return clean_text(root_sex).upper() if clean_text(root_sex).upper() in {"R", "H"} else ""
    return "R" if slot % 2 == 0 else "H"


def strip_label(value, label):
    text = clean_text(value)
    if text.lower().startswith(label.lower()):
        return text[len(label):].strip()
    return text


def parse_import_year(value):
    text = clean_text(value)
    match = re.search(r"\b(\d{4})\b", text)
    return match.group(1) if match else ""


def parse_import_elbow(value):
    text = strip_label(value, "Elbows:")
    ebv = ""
    confidence = ""

    ebv_match = re.search(r"\bEBV:\s*([-+]?\d+(?:[.,]\d+)?)", text, re.I)
    if ebv_match:
        ebv = ebv_match.group(1).replace(",", ".")

    confidence_match = re.search(r"\bConfidence:\s*(\d+(?:[.,]\d+)?)\s*%", text, re.I)
    if confidence_match:
        confidence = confidence_match.group(1).replace(",", ".")

    score = re.split(r",?\s*\bEBV:\s*", text, maxsplit=1, flags=re.I)[0].strip()
    if score.lower().endswith("bva/kc:"):
        score = ""
    return score, ebv, confidence


def parse_pedigree_text(text, root_sex=""):
    lines = [line.strip() for line in clean_text(text).splitlines() if line.strip()]
    entries = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith(("Hips:", "Elbows:")):
            i += 1
            continue

        entry = {
            "name": line,
            "year_line": "",
            "birth_year": "",
            "hips": "",
            "elbows": "",
            "ed": "",
            "ebv": "",
            "confidence": "",
        }
        i += 1

        if i < len(lines) and re.match(r"^\d{4}(?:\s*-.*)?$", lines[i]):
            entry["year_line"] = lines[i]
            entry["birth_year"] = parse_import_year(lines[i])
            i += 1

        while i < len(lines) and lines[i].startswith(("Hips:", "Elbows:")):
            if lines[i].startswith("Hips:"):
                entry["hips"] = strip_label(lines[i], "Hips:")
            elif lines[i].startswith("Elbows:"):
                entry["elbows"] = strip_label(lines[i], "Elbows:")
                entry["ed"], entry["ebv"], entry["confidence"] = parse_import_elbow(lines[i])
            i += 1

        entries.append(entry)

    slots = preorder_pedigree_slots(max_generation=4)
    if len(entries) != len(slots):
        raise ValueError(f"Erwartet wurden 31 Hunde, erkannt wurden {len(entries)}.")

    parsed = []
    for slot, entry in zip(slots, entries):
        generation = slot.bit_length() - 1
        item = dict(entry)
        item.update({
            "slot": slot,
            "generation": generation,
            "geschlecht": imported_slot_sex(slot, root_sex=root_sex),
            "father_slot": slot * 2 if generation < 4 else None,
            "mother_slot": slot * 2 + 1 if generation < 4 else None,
        })
        parsed.append(item)

    return parsed


def normalize_import_name(value):
    return re.sub(r"\s+", " ", clean_text(value)).strip().casefold()


def match_imported_dog(item):
    name_key = normalize_import_name(item.get("name"))
    if not name_key:
        return None

    candidates = MERGED_DF[
        MERGED_DF["Name"].fillna("").map(normalize_import_name) == name_key
    ].copy()
    if candidates.empty:
        return None

    birth_year = clean_text(item.get("birth_year"))
    if birth_year:
        year_source = candidates.get("geburtsjahr", pd.Series([""] * len(candidates), index=candidates.index)).fillna("")
        year_mask = year_source.astype(str).str.extract(r"(\d{4})")[0].fillna("") == birth_year
        year_matches = candidates[year_mask]
        if not year_matches.empty:
            candidates = year_matches

    row = candidates.iloc[0].to_dict()
    has_parents = bool(
        clean_text(row.get("vater_zbnr_norm") or row.get("vater_zbnr"))
        or clean_text(row.get("mutter_zbnr_norm") or row.get("mutter_zbnr"))
    )
    return {
        "zbnr": clean_text(row.get("ZBNr_norm") or row.get("ZBNr")),
        "name": clean_text(row.get("Name")),
        "birth_year": extract_birth_year(row.get("Wurfdatum") or row.get("geburtsjahr")),
        "geschlecht": clean_text(row.get("Geschlecht")),
        "has_parents": has_parents,
    }


def build_import_preview(parsed_items):
    preview = []
    for item in parsed_items:
        match = match_imported_dog(item)
        can_add_parent_links = bool(match) and not match.get("has_parents") and bool(item.get("father_slot") or item.get("mother_slot"))
        preview_item = dict(item)
        preview_item["match"] = match
        preview_item["status"] = "found" if match else "new"
        preview_item["selected"] = not bool(match) or can_add_parent_links
        preview_item["can_add_parent_links"] = can_add_parent_links
        preview.append(preview_item)
    return preview


def user_dog_record_from_import(item, zbnr, parent_refs, now):
    father = parent_refs.get(item.get("father_slot")) or {}
    mother = parent_refs.get(item.get("mother_slot")) or {}
    match = item.get("match") or {}
    return {
        "ZBNr": zbnr,
        "ZBNr_norm": zbnr,
        "Name": clean_text(item.get("name")),
        "Rasse": "Labrador-Retriever",
        "Wurfdatum": clean_text(item.get("birth_year")),
        "Geschlecht": clean_text(item.get("geschlecht")) or clean_text(match.get("geschlecht")),
        "HD_Grad": clean_text(item.get("hips")),
        "ED_rechts": clean_text(item.get("ed")),
        "ED_links": "",
        "AnzNachkommen": "",
        "EBV": clean_text(item.get("ebv")),
        "Confidenz": clean_text(item.get("confidence")),
        "Verlässlichkeit": "",
        "ED_ZWS": "",
        "prcd-PRA": "",
        "HNPK": "",
        "SD2": "",
        "CNM": "",
        "EIC": "",
        "ZS": "",
        "STGD_Status": "",
        "vater_name": clean_text(father.get("name")),
        "vater_zbnr": clean_text(father.get("zbnr")),
        "vater_zbnr_norm": pt.normalize_zbnr(father.get("zbnr")) or "",
        "mutter_name": clean_text(mother.get("name")),
        "mutter_zbnr": clean_text(mother.get("zbnr")),
        "mutter_zbnr_norm": pt.normalize_zbnr(mother.get("zbnr")) or "",
        "Vater": clean_text(father.get("name") or father.get("zbnr")),
        "Mutter": clean_text(mother.get("name") or mother.get("zbnr")),
        "geburtsjahr": clean_text(item.get("birth_year")),
        "pedigree_status": "ok",
        "father_found": bool_text(bool(father.get("zbnr"))),
        "mother_found": bool_text(bool(mother.get("zbnr"))),
        "source": "user_import_override" if match else "user_import",
        "created_at": now,
        "updated_at": now,
        "user_notes": "Import aus Text-Ahnentafel",
    }


def prepare_import_records(preview_items, selected_slots, user_df):
    selected_slots = {int(slot) for slot in selected_slots}
    slot_refs = {}
    next_number_df = user_df.copy()

    for item in sorted(preview_items, key=lambda dog: dog["slot"]):
        match = item.get("match")
        if match and match.get("zbnr"):
            slot_refs[item["slot"]] = {"zbnr": match["zbnr"], "name": match.get("name") or item.get("name")}
        elif item["slot"] in selected_slots:
            zbnr = next_user_zbnr(next_number_df)
            next_number_df = pd.concat([next_number_df, pd.DataFrame([{"ZBNr": zbnr, "ZBNr_norm": zbnr}])], ignore_index=True)
            slot_refs[item["slot"]] = {"zbnr": zbnr, "name": item.get("name")}

    now = datetime.now().isoformat(timespec="seconds")
    records = []
    for item in sorted(preview_items, key=lambda dog: dog["slot"]):
        if item["slot"] not in selected_slots:
            continue
        zbnr = slot_refs[item["slot"]]["zbnr"]
        records.append(user_dog_record_from_import(item, zbnr, slot_refs, now))

    return records


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


def kennel_club_health_url(zbnr, name):
    zbnr_text = clean_text(zbnr)
    if not zbnr_text.upper().startswith("KC"):
        return ""
    return (
        "https://www.royalkennelclub.com/search/health-test-results-finder/"
        f"?Filter={quote_plus(clean_text(name))}"
    )


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

    kc_health_url = kennel_club_health_url(zbnr, name)

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
    if clean_text(cached):
        try:
            return float(cached)
        except Exception:
            pass
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


def pedigree_metric_generation_depth(index, start_zbnr, minimum=5, maximum=10):
    slots = pt.build_positional_pedigree(
        index=index,
        start_zbnr=start_zbnr,
        max_generations=maximum,
    )
    found_generations = [
        entry["generation"]
        for entry in slots.values()
        if entry.get("generation", 0) > 0 and entry.get("found_in_data")
    ]
    deepest_found = max(found_generations, default=0)
    return max(minimum, min(maximum, deepest_found))


def repeated_ancestors_for_display(
    index,
    start_zbnr,
    max_generations=5,
    visible_generations=5,
    include_positions=False,
):
    slots = pt.build_positional_pedigree(
        index=index,
        start_zbnr=start_zbnr,
        max_generations=max_generations,
    )
    positions_by_zbnr = defaultdict(list)
    dog_by_zbnr = {}

    for slot_id, entry in slots.items():
        generation = entry.get("generation", 0)
        if generation <= 0:
            continue

        zbnr = pt.normalize_zbnr(entry.get("zbnr")) or clean_text(entry.get("zbnr"))
        if not zbnr:
            continue

        positions_by_zbnr[zbnr].append(
            {
                "slot": slot_id,
                "generation": generation,
                "role": pt.get_pedigree_role(slot_id),
                "path": pt.get_pedigree_path(slot_id),
            }
        )
        if zbnr not in dog_by_zbnr and entry.get("dog") is not None:
            dog_by_zbnr[zbnr] = entry["dog"]

    repeated = []
    for zbnr, positions in positions_by_zbnr.items():
        if len(positions) < 2:
            continue
        dog = dog_by_zbnr.get(zbnr) or index.get(zbnr) or {}
        generations = sorted({pos["generation"] for pos in positions})
        visible_positions = [
            pos for pos in positions
            if pos["generation"] <= visible_generations
        ]
        visible_generations_list = sorted({pos["generation"] for pos in visible_positions})
        visible = bool(visible_positions)
        has_hidden_positions = any(pos["generation"] > visible_generations for pos in positions)
        if visible and has_hidden_positions:
            visibility_label = "teilweise nicht sichtbar"
        elif has_hidden_positions:
            visibility_label = "nicht sichtbar"
        else:
            visibility_label = "sichtbar"
        item = {
            "zbnr": zbnr,
            "name": clean_text(dog.get("Name")) or zbnr,
            "count": len(positions),
            "generations": generations,
            "visible_count": len(visible_positions),
            "visible_generations": visible_generations_list,
            "visible": visible,
            "has_hidden_positions": has_hidden_positions,
            "visibility_label": visibility_label,
        }
        if include_positions:
            item["positions"] = positions
        repeated.append(item)

    repeated.sort(key=lambda item: (-item["count"], item["name"].casefold()))
    return repeated


def ancestor_contributors_for_display(index, start_zbnr, max_generations=10, limit=100):
    slots = pt.build_positional_pedigree(
        index=index,
        start_zbnr=start_zbnr,
        max_generations=max_generations,
    )
    contributors = {}

    for _slot_id, entry in slots.items():
        generation = entry.get("generation", 0)
        if generation <= 0:
            continue

        zbnr = pt.normalize_zbnr(entry.get("zbnr")) or clean_text(entry.get("zbnr"))
        if not zbnr:
            continue

        dog = entry.get("dog") or index.get(zbnr) or {}
        item = contributors.setdefault(
            zbnr,
            {
                "zbnr": zbnr,
                "name": clean_text(dog.get("Name")) or zbnr,
                "sex": clean_text(dog.get("Geschlecht") or dog.get("sex")),
                "count": 0,
                "blood_percent": 0.0,
                "generation_counts": {},
            },
        )
        item["count"] += 1
        item["blood_percent"] += 100 / (2 ** generation)
        generation_key = str(generation)
        item["generation_counts"][generation_key] = item["generation_counts"].get(generation_key, 0) + 1

    rows = sorted(
        contributors.values(),
        key=lambda item: (-item["blood_percent"], -item["count"], item["name"].casefold()),
    )
    return rows[:limit]


def avk_analysis_for_display(index, start_zbnr, max_generations=10, visible_generations=5):
    avk = pt.calculate_avk_for_zbnr(
        index,
        start_zbnr,
        max_generations=max_generations,
    )
    visible_avk = pt.calculate_avk_for_zbnr(
        index,
        start_zbnr,
        max_generations=visible_generations,
    )
    contributors = ancestor_contributors_for_display(
        index,
        start_zbnr,
        max_generations=max_generations,
    )
    repeated = repeated_ancestors_for_display(
        index,
        start_zbnr,
        max_generations=max_generations,
        visible_generations=visible_generations,
    )

    return {
        "max_generations": max_generations,
        "visible_generations": visible_generations,
        "visible_avk_known_percent": visible_avk.get("avk_known_percent"),
        "avk_known_percent": avk.get("avk_known_percent"),
        "possible_ancestor_positions": avk.get("possible_ancestor_positions"),
        "known_ancestor_positions": avk.get("known_ancestor_positions"),
        "unique_known_ancestors": avk.get("unique_known_ancestors"),
        "ancestor_loss_known": avk.get("ancestor_loss_known"),
        "deepest_complete_generation_in_data": avk.get("deepest_complete_generation_in_data"),
        "generation_rows": avk.get("generation_rows", []),
        "contributors": contributors,
        "repeated_ancestors": repeated,
    }


def coi_analysis_for_display(index, start_zbnr, min_generations=5, max_generations=10):
    rows = []
    start = max(1, int(min_generations or 1))
    end = max(start, int(max_generations or start))

    for generation in range(start, end + 1):
        result = pt.calculate_coi_for_zbnr(
            index,
            start_zbnr,
            max_generations=generation,
        )
        rows.append(
            {
                "generation": generation,
                "coi_percent": result.get("coi_percent"),
                "animals_in_calculation": result.get("animals_in_calculation"),
                "known_animals": result.get("known_animals"),
                "unknown_founders": result.get("unknown_founders"),
            }
        )

    return {
        "min_generations": start,
        "max_generations": end,
        "rows": rows,
        "note": (
            "Fehlende Ahnen werden in der COI-Berechnung als unbekannte, "
            "nicht verwandte Founder behandelt."
        ),
    }


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
            log_event("login_success", username=username, next_url=next_url)
            return redirect(next_url)

        log_event("login_failed", username=truncate_log_value(username), next_url=next_url)
        error = "Benutzername oder Passwort ist nicht korrekt."

    return render_template("login.html", error=error, next_url=next_url)


@app.route("/logout", methods=["POST"])
def logout():
    username = session.get("username")
    log_event("logout", username=username)
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
    log_event("comparison_opened")
    return render_template("compare.html")


@app.route("/client-event", methods=["POST"])
def client_event():
    payload = request.get_json(silent=True) or {}
    event = clean_text(payload.get("event"))
    if event not in CLIENT_LOG_EVENTS:
        return jsonify({"ok": False, "error": "unsupported event"}), 400

    log_event(event, **sanitized_client_event_payload(payload))
    return jsonify({"ok": True})


@app.route("/user-dogs", methods=["GET", "POST"])
def manage_user_dogs():
    errors = []
    saved_zbnr = request.args.get("saved", "")
    import_context = pedigree_import_context(default_return_to=url_for("manage_user_dogs"))
    form_values = user_dog_form_defaults()
    prefill_name = clean_text(request.args.get("prefill_name"))
    modal_open = bool(prefill_name)
    if prefill_name:
        form_values["name"] = prefill_name

    if request.method == "POST":
        form_values = user_dog_form_from_request()
        with USER_DOGS_LOCK:
            with locked_user_dogs_file():
                user_df = load_user_dogs_df()
                record = build_user_dog_record(form_values, user_df)
                errors = validate_user_dog(form_values, record, user_df)
                if not errors:
                    new_df = pd.concat([user_df, pd.DataFrame([record])], ignore_index=True)
                    write_user_dogs_df(new_df)
                    update_data_cache_with_user_records([record])
                    log_event(
                        "user_dog_created",
                        zbnr=record.get("ZBNr"),
                        name=record.get("Name"),
                        sex=record.get("Geschlecht"),
                    )
                    return redirect(url_for("manage_user_dogs", saved=record["ZBNr"]))
            modal_open = True

    user_dogs = load_user_dogs_df().to_dict(orient="records")
    user_dogs = sorted(user_dogs, key=lambda dog: clean_text(dog.get("created_at")), reverse=True)
    return render_template(
        "user_dogs.html",
        errors=errors,
        saved_zbnr=saved_zbnr,
        form_values=form_values,
        user_dogs=user_dogs,
        user_dogs_path=user_dog_path_label(),
        modal_open=modal_open,
        **import_context,
    )


@app.route("/user-dogs/import", methods=["POST"])
def preview_user_dog_import():
    import_errors = []
    root_sex = clean_text(request.form.get("root_sex")).upper()
    import_text = clean_text(request.form.get("pedigree_text"))
    return_to = clean_text(request.form.get("import_return_to")) or url_for("manage_user_dogs")
    if not is_safe_next_url(return_to):
        return_to = url_for("manage_user_dogs")
    uploaded = request.files.get("pedigree_file")
    if uploaded is not None and clean_text(uploaded.filename):
        try:
            import_text = uploaded.read().decode("utf-8-sig")
        except UnicodeDecodeError:
            uploaded.stream.seek(0)
            import_text = uploaded.read().decode("latin-1")

    log_event(
        "pedigree_import_preview_requested",
        root_sex=root_sex or "unknown",
        text_length=len(import_text),
        file_provided=bool(uploaded is not None and clean_text(uploaded.filename)),
        return_to=return_to,
    )

    import_preview = []
    import_data_json = ""
    if not clean_text(import_text):
        import_errors.append("Bitte füge Text ein oder lade eine Textdatei hoch.")
    else:
        try:
            parsed = parse_pedigree_text(import_text, root_sex=root_sex)
            import_preview = build_import_preview(parsed)
            import_data_json = json.dumps(import_preview, ensure_ascii=False)
        except Exception as exc:
            import_errors.append(str(exc))

    set_pedigree_import_state(
        import_errors=import_errors,
        import_preview=import_preview,
        import_data_json=import_data_json,
        import_modal_open=True,
        import_root_sex=root_sex,
        import_text=import_text,
        import_return_to=return_to,
    )
    log_event(
        "pedigree_import_preview_finished",
        root_sex=root_sex or "unknown",
        preview_items_count=len(import_preview),
        errors_count=len(import_errors),
        return_to=return_to,
    )
    return redirect(return_to)


@app.route("/user-dogs/import-confirm", methods=["POST"])
def confirm_user_dog_import():
    import_errors = []
    return_to = clean_text(request.form.get("import_return_to")) or url_for("manage_user_dogs")
    if not is_safe_next_url(return_to):
        return_to = url_for("manage_user_dogs")
    try:
        preview_items = json.loads(request.form.get("import_data", "[]"))
    except Exception:
        preview_items = []
        import_errors.append("Die Importdaten konnten nicht gelesen werden. Bitte erzeuge die Vorschau erneut.")

    selected_slots = request.form.getlist("import_slots")
    log_event(
        "pedigree_import_confirm_requested",
        selected_slots_count=len(selected_slots),
        preview_items_count=len(preview_items),
        return_to=return_to,
    )
    if not selected_slots:
        import_errors.append("Bitte wähle mindestens einen neuen Hund für den Import aus.")

    if import_errors:
        set_pedigree_import_state(
            import_errors=import_errors,
            import_preview=preview_items,
            import_data_json=json.dumps(preview_items, ensure_ascii=False),
            import_modal_open=True,
            import_root_sex="",
            import_text="",
            import_return_to=return_to,
        )
        return redirect(return_to)

    records = []
    with USER_DOGS_LOCK:
        with locked_user_dogs_file():
            user_df = load_user_dogs_df()
            records = prepare_import_records(preview_items, selected_slots, user_df)
            if records:
                record_zbnrs = {
                    pt.normalize_zbnr(record.get("ZBNr_norm") or record.get("ZBNr"))
                    for record in records
                    if pt.normalize_zbnr(record.get("ZBNr_norm") or record.get("ZBNr"))
                }
                if record_zbnrs:
                    user_df = user_df[
                        ~user_df.get("ZBNr_norm", pd.Series([""] * len(user_df), index=user_df.index))
                        .fillna("")
                        .map(lambda value: pt.normalize_zbnr(value) in record_zbnrs)
                    ].copy()
                new_df = pd.concat([user_df, pd.DataFrame(records)], ignore_index=True)
                write_user_dogs_df(new_df)
                update_data_cache_with_user_records(records)

    log_event(
        "pedigree_import_finished",
        selected_slots_count=len(selected_slots),
        imported_count=len(records),
        return_to=return_to,
    )
    return redirect_with_imported_count(return_to, len(records))


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
    sire_page_size = 10
    sire_candidates = []
    sire_total = 0
    sire_page_count = 0
    dam_preview = resolve_dog(dam_input, required_sex="H") if dam_input else None
    selected_sire_row = resolve_dog(selected_sire, required_sex="R") if selected_sire else None
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
        log_event(
            "pairing_sire_search",
            dam=dam_input,
            sire_query=sire_input,
            total_matches=sire_total,
            page=sire_page,
            page_size=sire_page_size,
            sort_by=sire_sort_by,
            sort_dir=sire_sort_dir,
            min_age=min_age,
            max_age=max_age,
            max_ebv=max_ebv,
            min_offspring=min_offspring,
            avoid_carrier_matches=avoid_carrier_matches,
            excluded_ancestors_count=len(excluded_ancestor_zbnrs),
        )

    context = {
        "sire_input": sire_input,
        "selected_sire": selected_sire,
        "dam_input": dam_input,
        "dam_summary": None,
        "selected_sire_summary": dog_summary(selected_sire_row) if selected_sire_row is not None else None,
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
        **pedigree_import_context(default_return_to=current_return_url()),
    }

    if dam_preview is not None:
        context["dam_summary"] = dog_summary(dam_preview)
        dam_identity = dog_log_identity(dam_preview)
        log_event(
            "pairing_dam_selected",
            dam_name=dam_identity.get("dog_name"),
            dam_zbnr=dam_identity.get("zbnr"),
            dam_input=truncate_log_value(dam_input),
        )

    if selected_sire_row is not None:
        sire_identity = dog_log_identity(selected_sire_row)
        log_event(
            "pairing_sire_selected",
            sire_name=sire_identity.get("dog_name"),
            sire_zbnr=sire_identity.get("zbnr"),
            sire_input=truncate_log_value(sire_input),
            selected_sire=truncate_log_value(selected_sire),
        )

    if selected_sire or dam_input:
        sire = selected_sire_row
        dam = dam_preview

        if sire is None or dam is None:
            if dam_input and dam is None:
                context["error"] = "Hündin nicht gefunden oder falsches Geschlecht."
            elif selected_sire and sire is None:
                context["error"] = "Rüde nicht gefunden oder falsches Geschlecht."
        else:
            pairing_result_started_at = time.perf_counter()
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
            display_max_gen = 5
            metric_max_gen = pedigree_metric_generation_depth(
                pairing_index,
                planned_zbnr,
                minimum=5,
                maximum=10,
            )

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
                max_generations=metric_max_gen,
            )
            avk = pt.calculate_avk_for_zbnr(
                pairing_index,
                planned_zbnr,
                max_generations=metric_max_gen,
            )
            avk_analysis = avk_analysis_for_display(
                pairing_index,
                planned_zbnr,
                max_generations=metric_max_gen,
                visible_generations=display_max_gen,
            )
            coi_analysis = coi_analysis_for_display(
                pairing_index,
                planned_zbnr,
                min_generations=display_max_gen,
                max_generations=metric_max_gen,
            )
            pedigree = pt.create_pedigree_html_for_zbnr(
                df_or_index=pairing_index,
                start_zbnr=planned_zbnr,
                max_generations=display_max_gen,
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
                "visible_avk_percent": avk_analysis.get("visible_avk_known_percent"),
                "visible_avk_display": format_percent_or_dash(avk_analysis.get("visible_avk_known_percent")),
                "complete_generation": avk.get("deepest_complete_generation_in_data"),
                "metric_generations": metric_max_gen,
                "display_generations": display_max_gen,
                "avk_analysis": avk_analysis,
                "coi_analysis": coi_analysis,
                "pedigree_html": extract_embeddable_html(pedigree.get("html", "")),
            }
            dam_identity = dog_log_identity(dam)
            sire_identity = dog_log_identity(sire)
            log_event(
                "pairing_result_rendered",
                dam_name=dam_identity.get("dog_name"),
                dam_zbnr=dam_identity.get("zbnr"),
                sire_name=sire_identity.get("dog_name"),
                sire_zbnr=sire_identity.get("zbnr"),
                coi=safe_float(coi.get("coi_percent")),
                avk=safe_float(avk.get("avk_known_percent")),
                pedigree_completeness=pedigree_completeness_percent(avk),
                complete_generation=avk.get("deepest_complete_generation_in_data"),
                generations=metric_max_gen,
                expected_ebv=safe_float(planned_ebv),
                offspring_zw=safe_float(planned_ebv),
                dam_ebv=safe_float(dam_ebv),
                sire_ebv=safe_float(sire_ebv),
                warnings_count=0,
                carrier_warning=False,
                duration_ms=event_duration_ms(pairing_result_started_at),
            )

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
            **pedigree_import_context(default_return_to=current_return_url()),
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
        log_event(
            "dog_search",
            query=query,
            total_matches=0,
            page=page,
            page_size=page_size,
            sort_by=sort_by,
            sort_dir=sort_dir,
        )
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
        res["kc_health_url"] = kennel_club_health_url(z, res["name"])
        res["geschlecht"] = r.get("Geschlecht") or r.get("sex") or "unbekannt"
        res["vater"] = r.get("Vater") or "unbekannt"
        res["mutter"] = r.get("Mutter") or "unbekannt"
        res["birth_year"] = clean_text(r.get("birth_year"))
        
        # Classification for display
        res["zuchtwert_class"] = "" #get_breeding_value_classification(zucht)
        res["konfidenz_class"] = get_reliability_classification(konf)
        
        results.append(res)

    log_event(
        "dog_search",
        query=query,
        total_matches=total_matches,
        page=page,
        page_size=page_size,
        sort_by=sort_by,
        sort_dir=sort_dir,
    )
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
        **pedigree_import_context(default_return_to=current_return_url()),
    )


@app.route("/pedigree")
def pedigree():
    zbnr = request.args.get("zbnr")
    if not zbnr:
        return redirect(url_for("search"))

    max_gen = int(request.args.get("gens", 5))
    started_at = time.perf_counter()

    res = pt.create_pedigree_html_for_zbnr(
        df_or_index=ZBNR_INDEX,
        start_zbnr=zbnr,
        max_generations=max_gen,
        include_coi=True,
        include_avk=True,
    )

    html = res.get("html", "<p>Keine Daten</p>")
    log_event(
        "pedigree_opened",
        zbnr=pt.normalize_zbnr(zbnr) or clean_text(zbnr),
        dog_name=dog_log_name(ZBNR_INDEX, zbnr),
        generations=max_gen,
        duration_ms=event_duration_ms(started_at),
    )

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

    started_at = time.perf_counter()
    try:
        requested_gens = clean_text(request.args.get("gens"))
        max_gen = (
            int(requested_gens)
            if requested_gens
            else pedigree_metric_generation_depth(
                ZBNR_INDEX,
                zbnr,
                minimum=5,
                maximum=10,
            )
        )
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
        avk_analysis = avk_analysis_for_display(
            ZBNR_INDEX,
            zbnr,
            max_generations=max_gen,
            visible_generations=5,
        )
        coi_analysis = coi_analysis_for_display(
            ZBNR_INDEX,
            zbnr,
            min_generations=5,
            max_generations=max_gen,
        )
    except Exception as e:
        return jsonify({"error": str(e)}), 500

    log_event(
        "pedigree_metrics_rendered",
        zbnr=pt.normalize_zbnr(zbnr) or clean_text(zbnr),
        dog_name=dog_log_name(ZBNR_INDEX, zbnr),
        coi=safe_float(coi.get("coi_percent") if coi else None),
        avk=safe_float(avk.get("avk_known_percent") if avk else None),
        completeness=pedigree_completeness_percent(avk),
        complete_generation=avk.get("deepest_complete_generation_in_data") if avk else None,
        generations=max_gen,
        duration_ms=event_duration_ms(started_at),
    )
    return jsonify(
        {
            "coi_percent": coi.get("coi_percent") if coi else None,
            "avk_known_percent": avk.get("avk_known_percent") if avk else None,
            "visible_avk_known_percent": (
                avk_analysis.get("visible_avk_known_percent") if avk_analysis else None
            ),
            "deepest_complete_generation_in_data": (
                avk.get("deepest_complete_generation_in_data") if avk else None
            ),
            "deepest_complete_generation_by_zbnr": (
                avk.get("deepest_complete_generation_by_zbnr") if avk else None
            ),
            "metric_generations": max_gen,
            "visible_generations": 5,
            "repeated_ancestors": avk_analysis.get("repeated_ancestors", []),
            "avk_analysis": avk_analysis,
            "coi_analysis": coi_analysis,
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
    started_at = time.perf_counter()

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

        log_event(
            "pedigree_opened",
            zbnr=pt.normalize_zbnr(zbnr) or clean_text(zbnr),
            dog_name=dog_log_name(ZBNR_INDEX, zbnr),
            generations=max_gen,
            duration_ms=event_duration_ms(started_at),
        )
        return Response(styles + body, mimetype="text/html")
    except Exception as e:
        import traceback
        print(f"Error loading pedigree for {zbnr}: {e}")
        traceback.print_exc()
        return f"<p>Fehler beim Laden der Ahnentafel: {str(e)}</p>", 500


if __name__ == "__main__":
    app.run(port=5000, debug=True)
