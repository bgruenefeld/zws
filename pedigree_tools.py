"""
pedigree_tools.py

Werkzeuge für:
- Merge Hundedaten + ZWS-Datei
- HTML-Ahnentafel über ZBNr
- pedigreebasierten COI
- Ahnenverlustkoeffizient und Ahnentafel-Vollständigkeit

Voraussetzungen:
    pip install pandas
"""

from __future__ import annotations

import html
import math
import re
from pathlib import Path
from typing import Any
from urllib.parse import quote

import pandas as pd


# ============================================================
# Hilfsfunktionen
# ============================================================

def make_json_serializable(value: Any):
    """
    Hilfsfunktion für json.dump().
    Konvertiert pandas/numpy-nahe Werte in normale Python-Werte.
    """
    if value is None:
        return None

    try:
        if pd.isna(value):
            return None
    except TypeError:
        pass

    if hasattr(value, "item"):
        return value.item()

    return str(value)


def to_float_or_none(value: Any) -> float | None:
    """
    Konvertiert einen Wert robust nach float oder None.
    """
    if value is None or pd.isna(value):
        return None

    try:
        return float(value)
    except ValueError:
        return None


def to_int_or_none(value: Any) -> int | None:
    """
    Konvertiert einen Wert robust nach int oder None.
    """
    if value is None or pd.isna(value):
        return None

    try:
        f = float(value)
        if f.is_integer():
            return int(f)
        return None
    except ValueError:
        return None


def dog_to_json_record(
    dog: dict[str, Any],
    lookup_zbnr: str | None = None,
) -> dict[str, Any]:
    """
    Reduziert einen Hundedatensatz auf frontend-taugliche JSON-Felder.

    Die Originaldatei kann sehr viele Spalten enthalten.
    Für das Frontend ist eine bereinigte, stabile Struktur meist besser.
    """
    zbnr = clean(dog.get("ZBNr_norm") or dog.get("ZBNr") or lookup_zbnr)

    birth_year = first_existing_value(
        dog,
        ["geburtsjahr", "birthyear_clean"],
    )

    birth_year_int = to_int_or_none(birth_year)

    birth_date = first_existing_value(
        dog,
        ["geburt", "Wurfdatum"],
    )

    sex = first_existing_value(
        dog,
        ["Geschlecht", "geschlecht", "sex_clean"],
    )

    ed_right = first_existing_value(
        dog,
        ["ED_rechts", "ED_rechts_raw"],
    )

    ed_left = first_existing_value(
        dog,
        ["ED_links", "ED_links_raw"],
    )

    ebv = to_float_or_none(dog.get("EBV"))
    confidence = to_float_or_none(dog.get("Confidenz"))
    reliability = clean(dog.get("Verlässlichkeit"))

    father_zbnr = normalize_parent_zbnr(
        dog.get("vater_zbnr_norm") or dog.get("vater_zbnr")
    )

    mother_zbnr = normalize_parent_zbnr(
        dog.get("mutter_zbnr_norm") or dog.get("mutter_zbnr")
    )

    return {
        "rkey": normalize_id(dog.get("Rkey")),
        "zbnr": zbnr,
        "name": clean(dog.get("Name")),
        "breed": clean(dog.get("Rasse")),
        "sex": sex,
        "birth_date": birth_date,
        "birth_year": birth_year_int,

        "health": {
            "hd": clean(dog.get("HD_Grad")),
            "ed_right": ed_right,
            "ed_left": ed_left,
            "ed_phenotyped": parse_bool(dog.get("ED_geroentgt")),
        },

        "ebv": {
            "value": ebv,
            "confidence_percent": confidence,
            "reliability_class": reliability,
        },

        "parents": {
            "father_zbnr": father_zbnr,
            "mother_zbnr": mother_zbnr,
        },

        "pedigree": {
            "status": clean(dog.get("pedigree_status")),
            "error": clean(dog.get("pedigree_error")),
            "father_found": parse_bool(dog.get("father_found")),
            "mother_found": parse_bool(dog.get("mother_found")),
        },
    }


def parse_bool(value: Any) -> bool | None:
    """
    Robuste bool-Konvertierung für Werte aus CSV.
    """
    if value is None or pd.isna(value):
        return None

    s = str(value).strip().lower()

    if s in {"true", "1", "yes", "ja", "y"}:
        return True

    if s in {"false", "0", "no", "nein", "n"}:
        return False

    return None


def get_pedigree_role(slot_id: int) -> str:
    """
    Gibt die unmittelbare Rolle der Position zurück.

    Beispiele:
        1 -> proband
        gerade Slotnummer -> father
        ungerade Slotnummer -> mother
    """
    if slot_id == 1:
        return "proband"

    return "father" if slot_id % 2 == 0 else "mother"


def get_pedigree_path(slot_id: int) -> str:
    """
    Erstellt einen Pfad aus V/M-Schritten.

    Beispiele:
        1  -> ""
        2  -> "V"
        3  -> "M"
        4  -> "VV"
        5  -> "VM"
        6  -> "MV"
        7  -> "MM"

    Achtung:
        Der Pfad beschreibt die Ahnenposition vom Probanden aus.
    """
    if slot_id == 1:
        return ""

    steps = []
    current = slot_id

    while current > 1:
        if current % 2 == 0:
            steps.append("V")
        else:
            steps.append("M")

        current = current // 2

    return "".join(reversed(steps))


def normalize_zbnr(value: Any) -> str | None:
    """
    Vereinheitlicht Zuchtbuchnummern für den Lookup.
    Erhält auch ausländische Nummern wie 'LCD 12/T 1692'.
    """
    if value is None or pd.isna(value):
        return None

    s = str(value).strip()

    if s == "" or s.lower() == "nan":
        return None

    if s.endswith(".0") and s[:-2].isdigit():
        s = s[:-2]

    return s


def normalize_id(value: Any) -> str | None:
    """
    Vereinheitlicht numerische IDs wie Rkey oder animal_id.

    Beispiele:
        72674.0   -> '72674'
        '72674.0' -> '72674'
        ' 72674 ' -> '72674'
    """
    if value is None or pd.isna(value):
        return None

    s = str(value).strip()

    if s == "" or s.lower() == "nan":
        return None

    try:
        f = float(s)
        if f.is_integer():
            return str(int(f))
        return str(f)
    except ValueError:
        return s


def clean(value: Any) -> str | None:
    """
    Liefert None für leere Werte, sonst einen bereinigten String.
    """
    if value is None or pd.isna(value):
        return None

    s = str(value).strip()

    if s == "" or s.lower() == "nan":
        return None

    return s


def format_number(value: Any, decimals: int = 0) -> str | None:
    """
    Formatiert Zahlen robust für die HTML-Ausgabe.
    """
    if value is None or pd.isna(value):
        return None

    try:
        return f"{float(value):.{decimals}f}"
    except ValueError:
        return str(value)


def first_existing_value(record: dict[str, Any], columns: list[str]) -> str | None:
    """
    Gibt den ersten vorhandenen Wert aus einer Liste möglicher Spalten zurück.
    """
    for col in columns:
        value = clean(record.get(col))
        if value is not None:
            return value
    return None


def safe_filename_part(value: Any, max_length: int = 120) -> str:
    """
    Erzeugt aus einer ZBNr oder einem Namen einen sicheren Dateinamen-Bestandteil.

    Beispiele:
        'LCD 12/T 1692'  -> 'LCD_12_T_1692'
        'DKK 23644/2008' -> 'DKK_23644_2008'
    """
    if value is None:
        return "unbekannt"

    s = str(value).strip()

    if s == "" or s.lower() == "nan":
        return "unbekannt"

    s = re.sub(r'[<>:"/\\|?*\n\r\t]+', "_", s)
    s = re.sub(r"\s+", "_", s)
    s = re.sub(r"_+", "_", s)
    s = s.strip(" ._")

    if not s:
        s = "unbekannt"

    return s[:max_length]


def is_unknown_parent_id(value: Any) -> bool:
    """
    Erkennt Platzhalter für unbekannte Eltern.
    """
    z = normalize_zbnr(value)

    if z is None:
        return True

    zl = z.lower().strip()

    if zl in {"?", "??", "unbekannt", "unknown", "none", "null"}:
        return True

    return False


def normalize_parent_zbnr(value: Any) -> str | None:
    """
    Normalisiert Eltern-ZBNr und behandelt Platzhalter als None.
    """
    z = normalize_zbnr(value)

    if is_unknown_parent_id(z):
        return None

    return z


def normalize_zbnr_columns(df: pd.DataFrame) -> pd.DataFrame:
    """
    Normalisiert die relevanten ZBNr-Spalten eines DataFrames.
    """
    df = df.copy()

    for col in [
        "ZBNr",
        "ZBNr_norm",
        "vater_zbnr",
        "mutter_zbnr",
        "vater_zbnr_norm",
        "mutter_zbnr_norm",
    ]:
        if col in df.columns:
            df[col] = df[col].map(normalize_zbnr)

    return df


# ============================================================
# 1. Merge Hundedaten + ZWS
# ============================================================

def load_base_dog_file(base_csv_path: str | Path) -> pd.DataFrame:
    """
    Lädt die ursprüngliche Hundedatei mit Stammdaten, Gesundheitsdaten
    und Elterninformationen.
    """
    df = pd.read_csv(base_csv_path, dtype=str)

    if "Rkey" not in df.columns:
        raise ValueError("In der Eingangsdatei fehlt die Spalte 'Rkey'.")

    df["Rkey_join"] = df["Rkey"].map(normalize_id)
    df = normalize_zbnr_columns(df)

    return df


def load_ebv_file(ebv_csv_path: str | Path) -> pd.DataFrame:
    """
    Lädt die ZWS-Datei und übernimmt die relevanten Spalten:

        reliability_prozent       -> Confidenz
        sicherheitsklasse         -> Verlässlichkeit
        ed_zw_0_10_niedrig_gut    -> EBV
    """
    zws = pd.read_csv(ebv_csv_path, dtype=str)

    required_cols = [
        "animal_id",
        "reliability_prozent",
        "sicherheitsklasse",
        "ed_zw_0_10_niedrig_gut",
    ]

    missing = [col for col in required_cols if col not in zws.columns]
    if missing:
        raise ValueError(f"In der ZWS-Datei fehlen diese Spalten: {missing}")

    zws["Rkey_join"] = zws["animal_id"].map(normalize_id)

    zws_small = zws[
        [
            "Rkey_join",
            "reliability_prozent",
            "sicherheitsklasse",
            "ed_zw_0_10_niedrig_gut",
        ]
    ].copy()

    zws_small = zws_small.rename(
        columns={
            "reliability_prozent": "Confidenz",
            "sicherheitsklasse": "Verlässlichkeit",
            "ed_zw_0_10_niedrig_gut": "EBV",
        }
    )

    zws_small["Confidenz"] = pd.to_numeric(
        zws_small["Confidenz"],
        errors="coerce",
    )

    zws_small["EBV"] = pd.to_numeric(
        zws_small["EBV"],
        errors="coerce",
    )

    zws_small["Verlässlichkeit"] = zws_small["Verlässlichkeit"].map(clean)

    zws_small = zws_small.drop_duplicates(
        subset=["Rkey_join"],
        keep="first",
    )

    return zws_small


def merge_dog_data_with_ebv(
    base_csv_path: str | Path,
    ebv_csv_path: str | Path,
    out_csv_path: str | Path | None = None,
) -> tuple[pd.DataFrame, dict[str, Any]]:
    """
    Führt Hundedatendatei und ZWS-Datei zusammen.

    Join:
        Hundedatei.Rkey == ZWS-Datei.animal_id

    Rückgabe:
        merged_df, report
    """
    base = load_base_dog_file(base_csv_path)
    ebv = load_ebv_file(ebv_csv_path)

    merged = base.merge(
        ebv,
        how="left",
        on="Rkey_join",
        validate="many_to_one",
    )

    report = {
        "base_records": len(base),
        "ebv_records": len(ebv),
        "merged_records": len(merged),
        "records_with_ebv": int(merged["EBV"].notna().sum()),
        "records_with_confidence": int(merged["Confidenz"].notna().sum()),
        "records_with_reliability_class": int(merged["Verlässlichkeit"].notna().sum()),
        "records_without_ebv": int(merged["EBV"].isna().sum()),
    }

    if out_csv_path is not None:
        Path(out_csv_path).parent.mkdir(parents=True, exist_ok=True)
        merged.to_csv(out_csv_path, index=False)

    return merged, report


def load_merged_dog_file(merged_csv_path: str | Path) -> pd.DataFrame:
    """
    Lädt eine bereits gemergte Datei.
    """
    df = pd.read_csv(merged_csv_path, dtype=str)
    df = normalize_zbnr_columns(df)

    if "Rkey" in df.columns:
        df["Rkey_join"] = df["Rkey"].map(normalize_id)

    if "Confidenz" in df.columns:
        df["Confidenz"] = pd.to_numeric(df["Confidenz"], errors="coerce")

    if "EBV" in df.columns:
        df["EBV"] = pd.to_numeric(df["EBV"], errors="coerce")

    if "Verlässlichkeit" in df.columns:
        df["Verlässlichkeit"] = df["Verlässlichkeit"].map(clean)

    return df


# ============================================================
# ZBNr-Index
# ============================================================

def build_zbnr_index(df: pd.DataFrame) -> tuple[dict[str, dict[str, Any]], list[str]]:
    """
    Baut einen Index:

        ZBNr_norm -> Hundedatensatz

    Die Ahnentafel wird über diesen Index rekonstruiert.
    """
    index: dict[str, dict[str, Any]] = {}
    duplicates = set()

    for _, row in df.iterrows():
        record = row.to_dict()

        zbnr = normalize_zbnr(record.get("ZBNr_norm") or record.get("ZBNr"))
        if not zbnr:
            continue

        record["ZBNr_norm"] = zbnr

        if zbnr in index:
            duplicates.add(zbnr)

            prev = index[zbnr]
            prev_ok = clean(prev.get("pedigree_status")) == "ok"
            curr_ok = clean(record.get("pedigree_status")) == "ok"

            if not prev_ok and curr_ok:
                index[zbnr] = record
        else:
            index[zbnr] = record

    return index, sorted(duplicates)


# ============================================================
# 2. HTML-Ahnentafel
# ============================================================

def build_ancestor_slots(
    index: dict[str, dict[str, Any]],
    start_zbnr: str,
    max_generations: int = 5,
) -> dict[int, dict[str, Any]]:
    """
    Erstellt die Ahnentafel in klassischer Nummerierung:

        1 = Hund selbst
        2 = Vater
        3 = Mutter
        4 = Vater des Vaters
        5 = Mutter des Vaters
        usw.
    """
    start_zbnr = normalize_parent_zbnr(start_zbnr)
    max_slot = 2 ** (max_generations + 1) - 1
    slots: dict[int, dict[str, Any]] = {}

    def recurse(current_zbnr: str | None, slot: int, generation: int) -> None:
        if slot > max_slot:
            return

        current_zbnr = normalize_parent_zbnr(current_zbnr)
        dog = index.get(current_zbnr) if current_zbnr else None

        slots[slot] = {
            "lookup_zbnr": current_zbnr,
            "dog": dog,
            "generation": generation,
        }

        if generation >= max_generations:
            return

        if dog is not None:
            father = normalize_parent_zbnr(
                dog.get("vater_zbnr_norm") or dog.get("vater_zbnr")
            )
            mother = normalize_parent_zbnr(
                dog.get("mutter_zbnr_norm") or dog.get("mutter_zbnr")
            )
        else:
            father = None
            mother = None

        recurse(father, slot * 2, generation + 1)
        recurse(mother, slot * 2 + 1, generation + 1)

    recurse(start_zbnr, 1, 0)

    return slots


def compute_layout(
    max_generations: int,
    card_width: int = 230,
    card_height: int = 82,
    col_gap: int = 58,
    row_gap: int = 10,
    margin_x: int = 24,
    margin_y: int = 24,
) -> tuple[dict[int, dict[str, float]], int, int]:
    """
    Berechnet die Positionen der Hundekarten.
    Kompakte Variante für 4 bis 6 Generationen.
    """
    leaf_count = 2 ** max_generations
    slot_height = card_height + row_gap
    content_height = leaf_count * slot_height

    positions: dict[int, dict[str, float]] = {}
    max_slot = 2 ** (max_generations + 1) - 1

    for n in range(1, max_slot + 1):
        generation = int(math.log2(n))
        idx_in_generation = n - 2 ** generation

        x = margin_x + generation * (card_width + col_gap)
        cy = margin_y + (idx_in_generation + 0.5) * (
            content_height / (2 ** generation)
        )
        y = cy - card_height / 2

        positions[n] = {
            "x": x,
            "y": y,
            "cy": cy,
        }

    total_width = (
        margin_x * 2
        + (max_generations + 1) * card_width
        + max_generations * col_gap
    )
    total_height = content_height + margin_y * 2

    return positions, total_width, total_height


def get_generation_layout(max_generations: int) -> dict[int, dict[str, int]]:
    """
    Gibt pro Generation kompaktere Kartengroessen zurueck.
    Entfernte Generationen brauchen weniger Hoehe, damit 5 Generationen
    auf einem normalen Bildschirm zusammen sichtbar bleiben.
    """
    presets = [
        {"width": 280, "height": 104},
        {"width": 270, "height": 96},
        {"width": 260, "height": 86},
        {"width": 245, "height": 68},
        {"width": 235, "height": 56},
        {"width": 230, "height": 46},
    ]

    return {
        generation: presets[min(generation, len(presets) - 1)]
        for generation in range(max_generations + 1)
    }


def compute_compact_layout(
    max_generations: int,
    generation_layout: dict[int, dict[str, int]],
    col_gap: int = 14,
    leaf_slot_height: int = 30,
    margin_x: int = 12,
    margin_y: int = 10,
) -> tuple[dict[int, dict[str, float]], int, int]:
    """
    Berechnet Positionen mit variabler Kartengroesse je Generation.
    Die letzte Generation definiert die vertikale Rasterhoehe.
    """
    leaf_count = 2 ** max_generations
    content_height = leaf_count * leaf_slot_height

    generation_x: dict[int, float] = {}
    x = float(margin_x)
    for generation in range(max_generations + 1):
        generation_x[generation] = x
        x += generation_layout[generation]["width"] + col_gap

    positions: dict[int, dict[str, float]] = {}
    max_slot = 2 ** (max_generations + 1) - 1

    for n in range(1, max_slot + 1):
        generation = int(math.log2(n))
        idx_in_generation = n - 2 ** generation
        card_height = generation_layout[generation]["height"]

        cy = margin_y + (idx_in_generation + 0.5) * (
            content_height / (2 ** generation)
        )
        y = cy - card_height / 2

        positions[n] = {
            "x": generation_x[generation],
            "y": y,
            "cy": cy,
        }

    total_width = int(
        margin_x * 2
        + sum(generation_layout[g]["width"] for g in range(max_generations + 1))
        + max_generations * col_gap
    )
    total_height = content_height + margin_y * 2

    return positions, total_width, total_height


def render_card(entry: dict[str, Any], generation: int = 0, max_generations: int = 5) -> str:
    """
    Rendert eine kompakte Hundekarte.
    """
    dog = entry["dog"]
    lookup_zbnr = entry["lookup_zbnr"]

    if dog is None:
        zbnr = lookup_zbnr or ""
        subline = f"ZBNr {html.escape(zbnr)}" if zbnr else "keine Daten"
        zbnr_attr = html.escape(zbnr, quote=True)

        return f"""
        <div class="card missing gen-{generation}" data-zbnr="{zbnr_attr}" title="{subline}">
            <div class="name">Unbekannt</div>
            <div class="subline">{subline}</div>
        </div>
        """

    name = clean(dog.get("Name")) or "Ohne Namen"
    zbnr = clean(dog.get("ZBNr_norm") or dog.get("ZBNr") or lookup_zbnr)
    zbnr_attr = html.escape(zbnr or "", quote=True)
    father_zbnr = normalize_parent_zbnr(
        dog.get("vater_zbnr_norm") or dog.get("vater_zbnr")
    )
    mother_zbnr = normalize_parent_zbnr(
        dog.get("mutter_zbnr_norm") or dog.get("mutter_zbnr")
    )
    missing_direct_ancestor = generation < max_generations and (
        not father_zbnr or not mother_zbnr
    )

    birth = first_existing_value(
        dog,
        ["geburtsjahr", "birthyear_clean", "geburt", "Wurfdatum"],
    )

    if birth:
        try:
            birth_float = float(birth)
            if birth_float.is_integer():
                birth = str(int(birth_float))
        except ValueError:
            pass

    sex = first_existing_value(
        dog,
        ["Geschlecht", "geschlecht", "sex_clean"],
    )

    hd = clean(dog.get("HD_Grad"))

    ed_r = first_existing_value(
        dog,
        ["ED_rechts", "ED_rechts_raw"],
    )
    ed_l = first_existing_value(
        dog,
        ["ED_links", "ED_links_raw"],
    )

    ebv_value = to_float_or_none(dog.get("EBV"))
    ebv = format_number(ebv_value, decimals=0)
    confidence = format_number(dog.get("Confidenz"), decimals=0)
    reliability_class = clean(dog.get("Verlässlichkeit"))
    card_classes = f"card gen-{generation}"
    warning_title = ""
    if ebv_value is not None and ebv_value > 0:
        card_classes += " ebv-unfavorable"
        warning_title = " | Ungünstiger ED-EBV (> 0)"

    epi_score = clean(dog.get("EpiScore"))
    epi_score_html = ""
    if epi_score:
        card_classes += " epi-score-match"
        epi_score_html = (
            '<span class="epi-score" title="Score">'
            '<span class="epi-score-dot" aria-hidden="true"></span>'
            f'{html.escape(epi_score)}'
            '</span>'
        )

    info_parts = []

    if zbnr:
        info_parts.append(f"ZBNr {html.escape(zbnr)}")
    if birth:
        info_parts.append(html.escape(birth))
    if sex:
        info_parts.append(html.escape(sex))

    info_line = " · ".join(info_parts)

    health_parts = []

    if hd:
        health_parts.append(f"HD {html.escape(hd)}")

    if ed_r or ed_l:
        health_parts.append(
            f"ED {html.escape(ed_r or '-')}/{html.escape(ed_l or '-')}"
        )

    health_line = " · ".join(health_parts)

    zws_parts = []

    if ebv is not None:
        zws_parts.append(f"EBV {html.escape(ebv)}")
    if confidence is not None:
        zws_parts.append(f"C {html.escape(confidence)}%")
    if reliability_class:
        zws_parts.append(html.escape(reliability_class))

    zws_line = " · ".join(zws_parts)

    detail_lines = [name, f"Score {epi_score}" if epi_score else "", info_line, health_line, zws_line]
    title = html.escape(" | ".join(line for line in detail_lines if line) + warning_title, quote=True)
    k9_link_html = ""
    if missing_direct_ancestor:
        k9_url = (
            "https://k9-data.org/search"
            f"?registeredName={quote(name)}&breed=2"
        )
        k9_link_html = (
            f' <a class="k9-link" href="{html.escape(k9_url, quote=True)}" '
            'target="_blank" rel="noopener noreferrer" '
            'title="Bei k9-data suchen">k9</a>'
        )

    drilldown_html = ""
    if zbnr:
        drilldown_html = f"""
        <button
            type="button"
            class="pedigree-drilldown"
            data-zbnr="{zbnr_attr}"
            title="Ahnentafel dieses Hundes anzeigen"
            aria-label="Ahnentafel von {html.escape(name, quote=True)} anzeigen"
        >
            <svg viewBox="0 0 24 24" aria-hidden="true" focusable="false">
                <path d="M12 5v14"></path>
                <path d="M6 9h12"></path>
                <path d="M6 15h12"></path>
                <circle cx="12" cy="5" r="2"></circle>
                <circle cx="6" cy="9" r="2"></circle>
                <circle cx="18" cy="9" r="2"></circle>
                <circle cx="6" cy="15" r="2"></circle>
                <circle cx="18" cy="15" r="2"></circle>
            </svg>
        </button>
        """

    name_html = f'<div class="name">{html.escape(name)}{drilldown_html}{epi_score_html}{k9_link_html}</div>'

    if generation >= 5:
        compact_parts = []
        if birth:
            compact_parts.append(html.escape(birth))
        if ed_r or ed_l:
            compact_parts.append(f"ED {html.escape(ed_r or '-')}/{html.escape(ed_l or '-')}")
        if ebv is not None:
            compact_parts.append(f"EBV {html.escape(ebv)}")

        compact_line = " · ".join(compact_parts)
        compact_html = f'<div class="subline">{compact_line}</div>' if compact_line else ""

        return f"""
        <div class="{card_classes}" data-zbnr="{zbnr_attr}" title="{title}">
            {name_html}
            {compact_html}
        </div>
        """

    if generation >= 4:
        compact_info_parts = []
        if birth:
            compact_info_parts.append(html.escape(birth))
        if sex:
            compact_info_parts.append(html.escape(sex))
        if hd:
            compact_info_parts.append(f"HD {html.escape(hd)}")
        if ed_r or ed_l:
            compact_info_parts.append(f"ED {html.escape(ed_r or '-')}/{html.escape(ed_l or '-')}")
        if ebv is not None:
            compact_info_parts.append(f"EBV {html.escape(ebv)}")

        compact_line = " · ".join(compact_info_parts)
        compact_html = f'<div class="subline">{compact_line}</div>' if compact_line else ""

        return f"""
        <div class="{card_classes}" data-zbnr="{zbnr_attr}" title="{title}">
            {name_html}
            {compact_html}
        </div>
        """

    if generation >= 3:
        combined_line = " · ".join(line for line in [health_line, zws_line] if line)
        info_html = f'<div class="subline">{info_line}</div>' if info_line else ""
        combined_html = f'<div class="zws-line">{combined_line}</div>' if combined_line else ""

        return f"""
        <div class="{card_classes}" data-zbnr="{zbnr_attr}" title="{title}">
            {name_html}
            {info_html}
            {combined_html}
        </div>
        """

    info_html = f'<div class="subline">{info_line}</div>' if info_line else ""
    health_html = f'<div class="subline">{health_line}</div>' if health_line else ""
    zws_html = f'<div class="zws-line">{zws_line}</div>' if zws_line else ""

    return f"""
    <div class="{card_classes}" data-zbnr="{zbnr_attr}" title="{title}">
        {name_html}
        {info_html}
        {health_html}
        {zws_html}
    </div>
    """


def render_pedigree_html(
    index: dict[str, dict[str, Any]],
    start_zbnr: str,
    max_generations: int = 5,
    coi_result: dict[str, Any] | None = None,
    avk_result: dict[str, Any] | None = None,
) -> str:
    """
    Erzeugt den HTML-Inhalt der Ahnentafel als String.
    """
    slots = build_ancestor_slots(
        index=index,
        start_zbnr=start_zbnr,
        max_generations=max_generations,
    )

    leaf_count = 2 ** max_generations
    row_height = 44
    column_widths = [250, 255, 260, 270, 270]
    active_widths = column_widths[:max_generations]
    total_width = sum(active_widths)
    total_height = leaf_count * row_height

    cells_html = []

    for slot, entry in slots.items():
        generation = entry["generation"]
        if generation == 0:
            continue
        idx_in_generation = slot - 2 ** generation
        row_span = 2 ** (max_generations - generation)
        row_start = idx_in_generation * row_span + 1
        row_end = row_start + row_span

        cells_html.append(
            f"""
            <div class="pedigree-cell"
                 style="grid-column:{generation}; grid-row:{row_start} / {row_end};">
                {render_card(entry, generation=generation, max_generations=max_generations)}
            </div>
            """
        )

    title_text = f"Ahnentafel für {html.escape(str(start_zbnr))}"

    subtitle_parts = []

    if coi_result is not None:
        subtitle_parts.append(f"COI: {coi_result['coi_percent']:.2f} %")

    if avk_result is not None:
        subtitle_parts.append(
            f"AVK: {avk_result['avk_known_percent']:.2f} %"
            if avk_result["avk_known_percent"] is not None
            else "AVK: n. b."
        )
        subtitle_parts.append(
            f"vollständig bis Gen. {avk_result['deepest_complete_generation_in_data']}"
        )

    subtitle_html = ""
    if subtitle_parts:
        subtitle_html = f'<div class="page-subtitle">{" · ".join(subtitle_parts)}</div>'

    html_doc = f"""
<!DOCTYPE html>
<html lang="de">
<head>
    <meta charset="utf-8" />
    <title>{title_text}</title>

    <style>
        .pedigree-document {{
            box-sizing: border-box;
            font-family: "Segoe UI", Arial, Helvetica, sans-serif;
            background: #f5f7fa;
            color: #1f2937;
            min-width: fit-content;
        }}

        .page-subtitle {{
            font-size: 12px;
            color: #667085;
            margin: 0;
            padding: 14px 16px 10px;
        }}

        .canvas-wrap {{
            display: flex;
            justify-content: center;
            overflow: visible;
            background: #f5f7fa;
            padding: 12px;
        }}

        .canvas {{
            display: grid;
            grid-template-columns: {" ".join(f"{width}px" for width in active_widths)};
            grid-template-rows: repeat({leaf_count}, {row_height}px);
            width: {total_width}px;
            height: {total_height}px;
            background: #ffffff;
            border-left: 1px solid #d8dee6;
            border-top: 1px solid #d8dee6;
        }}

        .pedigree-cell {{
            background: #fbfcfe;
            border-bottom: 1px solid #d8dee6;
            border-right: 1px solid #d8dee6;
            box-sizing: border-box;
            min-height: 0;
        }}

        .card {{
            align-content: center;
            background: transparent;
            border: 0;
            border-radius: 0;
            box-shadow: none;
            box-sizing: border-box;
            cursor: pointer;
            display: grid;
            gap: 3px;
            height: 100%;
            overflow: hidden;
            padding: 9px 12px;
            position: relative;
            width: 100%;
        }}

        .card:hover {{
            background: #f1f6fb;
        }}

        .card.ebv-unfavorable {{
            box-shadow: inset 4px 0 0 #d46b08;
        }}

        .card.ebv-unfavorable .zws-line {{
            color: #8a4b08;
        }}

        .card.ebv-unfavorable .subline {{
            color: #8a4b08;
        }}

        .card.missing {{
            color: #7f8b99;
            opacity: 0.75;
        }}

        .pedigree-drilldown {{
            align-items: center;
            background: #fff;
            border: 1px solid #cfd8e3;
            border-radius: 999px;
            color: #2563eb;
            cursor: pointer;
            display: inline-flex;
            height: 18px;
            justify-content: center;
            margin-left: 5px;
            opacity: 0;
            padding: 0;
            transform: translateY(2px);
            transition: opacity 0.12s ease, background 0.12s ease, border-color 0.12s ease;
            width: 18px;
        }}

        .card:hover .pedigree-drilldown,
        .card:focus-within .pedigree-drilldown,
        .pedigree-drilldown:focus-visible {{
            opacity: 1;
        }}

        .pedigree-drilldown:hover,
        .pedigree-drilldown:focus-visible {{
            background: #e8f2ff;
            border-color: #9ec5fe;
            outline: none;
        }}

        .pedigree-drilldown svg {{
            fill: none;
            height: 12px;
            stroke: currentColor;
            stroke-linecap: round;
            stroke-linejoin: round;
            stroke-width: 2;
            width: 12px;
        }}

        .name {{
            color: #1f3a52;
            font-size: 13px;
            font-weight: 800;
            line-height: 1.2;
            display: -webkit-box;
            -webkit-line-clamp: 2;
            -webkit-box-orient: vertical;
            overflow: hidden;
        }}

        .epi-score {{
            align-items: center;
            color: #b42318;
            display: inline-flex;
            font-size: 11px;
            font-weight: 800;
            gap: 4px;
            margin-left: 6px;
            white-space: nowrap;
        }}

        .epi-score-dot {{
            background: #d92d20;
            border-radius: 50%;
            display: inline-block;
            flex: 0 0 auto;
            height: 8px;
            width: 8px;
        }}

        .k9-link {{
            color: #2563eb;
            display: inline;
            font-size: 10px;
            font-weight: 800;
            margin-left: 6px;
            text-decoration: none;
            white-space: nowrap;
        }}

        .k9-link:hover {{
            text-decoration: underline;
        }}

        .subline {{
            color: #667085;
            font-size: 11px;
            line-height: 1.25;
            white-space: normal;
            overflow: hidden;
            overflow-wrap: anywhere;
        }}

        .zws-line {{
            color: #334158;
            font-size: 10px;
            line-height: 1.2;
            font-weight: 600;
            white-space: normal;
            overflow: hidden;
            overflow-wrap: anywhere;
        }}

        .card.gen-2 {{
            padding: 8px 11px;
        }}

        .card.gen-2 .name {{
            font-size: 12.5px;
            line-height: 1.15;
        }}

        .card.gen-2 .subline,
        .card.gen-2 .zws-line {{
            font-size: 10.5px;
            line-height: 1.15;
        }}

        .card.gen-3 {{
            padding: 7px 10px;
        }}

        .card.gen-3 .name {{
            font-size: 12px;
            line-height: 1.15;
            -webkit-line-clamp: 2;
        }}

        .card.gen-3 .subline,
        .card.gen-3 .zws-line {{
            font-size: 10px;
            line-height: 1.15;
        }}

        .card.gen-4 {{
            padding: 6px 10px;
        }}

        .card.gen-4 .name {{
            font-size: 11.5px;
            line-height: 1.15;
            -webkit-line-clamp: 2;
        }}

        .card.gen-4 .subline {{
            font-size: 9.5px;
            line-height: 1.15;
            white-space: nowrap;
            text-overflow: ellipsis;
        }}

        .card.gen-5 {{
            padding: 5px 10px;
        }}

        .card.gen-5 .name {{
            font-size: 11px;
            line-height: 1.15;
            -webkit-line-clamp: 2;
        }}

        .card.gen-5 .subline {{
            font-size: 9px;
            line-height: 1.15;
            white-space: nowrap;
            text-overflow: ellipsis;
        }}
    </style>
</head>

<body>
    <div class="pedigree-document">
        {subtitle_html}

        <div class="canvas-wrap">
            <div class="canvas">
                {"".join(cells_html)}
            </div>
        </div>
    </div>
</body>
</html>
"""

    return html_doc


def create_pedigree_html_for_zbnr(
    df_or_index: pd.DataFrame | dict[str, dict[str, Any]],
    start_zbnr: str,
    out_html_path: str | Path | None = None,
    max_generations: int = 5,
    include_coi: bool = True,
    include_avk: bool = True,
) -> dict[str, Any]:
    """
    Erzeugt eine HTML-Ahnentafel für eine ZBNr.

    Parameter:
        df_or_index:
            entweder ein DataFrame oder ein bereits gebauter ZBNr-Index

        out_html_path:
            wenn gesetzt, wird die HTML-Datei geschrieben.
            wenn None, wird nur der HTML-String zurückgegeben.

    Rückgabe:
        dict mit html, path, coi, avk
    """
    if isinstance(df_or_index, pd.DataFrame):
        index, duplicates = build_zbnr_index(df_or_index)
    else:
        index = df_or_index
        duplicates = []

    coi_result = (
        calculate_coi_for_zbnr(index, start_zbnr, max_generations=max_generations)
        if include_coi
        else None
    )

    avk_result = (
        calculate_avk_for_zbnr(index, start_zbnr, max_generations=max_generations)
        if include_avk
        else None
    )

    html_string = render_pedigree_html(
        index=index,
        start_zbnr=start_zbnr,
        max_generations=max_generations,
        coi_result=coi_result,
        avk_result=avk_result,
    )

    saved_path = None

    if out_html_path is not None:
        out_path = Path(out_html_path)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(html_string, encoding="utf-8")
        saved_path = str(out_path)

    return {
        "html": html_string,
        "path": saved_path,
        "coi": coi_result,
        "avk": avk_result,
        "duplicates": duplicates,
    }


def create_pedigree_json_for_zbnr(
    df_or_index: pd.DataFrame | dict[str, dict[str, Any]],
    start_zbnr: str,
    max_generations: int = 5,
    include_coi: bool = True,
    include_avk: bool = True,
    out_json_path: str | Path | None = None,
) -> dict[str, Any]:
    """
    Erzeugt eine positionsbasierte Ahnentafel als JSON-kompatibles dict.

    Die Struktur ist für Frontend-Darstellungen gedacht.

    Rückgabe:
        {
            "start_zbnr": ...,
            "max_generations": ...,
            "nodes": [...],
            "edges": [...],
            "generations": {...},
            "coi": {...} oder None,
            "avk": {...} oder None,
            "duplicates": [...]
        }

    Hinweise:
        - Jeder Node entspricht einer Position in der Ahnentafel.
        - Wenn derselbe Hund mehrfach vorkommt, gibt es mehrere Nodes
          mit derselben ZBNr, aber unterschiedlicher slot_id.
        - slot_id folgt der klassischen Ahnentafelnummerierung:
              1 = Proband
              2 = Vater
              3 = Mutter
              4 = Vater des Vaters
              5 = Mutter des Vaters
              usw.
    """
    if isinstance(df_or_index, pd.DataFrame):
        index, duplicates = build_zbnr_index(df_or_index)
    else:
        index = df_or_index
        duplicates = []

    start_zbnr_norm = normalize_parent_zbnr(start_zbnr)

    if not start_zbnr_norm:
        raise ValueError("Keine gültige Start-ZBNr angegeben.")

    slots = build_ancestor_slots(
        index=index,
        start_zbnr=start_zbnr_norm,
        max_generations=max_generations,
    )

    nodes = []
    edges = []
    generations: dict[str, list[int]] = {}

    for slot_id in sorted(slots.keys()):
        entry = slots[slot_id]

        generation = entry["generation"]
        lookup_zbnr = entry["lookup_zbnr"]
        dog = entry["dog"]

        generation_key = str(generation)
        generations.setdefault(generation_key, []).append(slot_id)

        if dog is None:
            node = {
                "slot_id": slot_id,
                "generation": generation,
                "position_in_generation": slot_id - 2 ** generation,
                "role": get_pedigree_role(slot_id),
                "path": get_pedigree_path(slot_id),
                "known": False,
                "found_in_data": False,
                "lookup_zbnr": lookup_zbnr,
                "dog": None,
            }
        else:
            node = {
                "slot_id": slot_id,
                "generation": generation,
                "position_in_generation": slot_id - 2 ** generation,
                "role": get_pedigree_role(slot_id),
                "path": get_pedigree_path(slot_id),
                "known": True,
                "found_in_data": True,
                "lookup_zbnr": lookup_zbnr,
                "dog": dog_to_json_record(dog, lookup_zbnr=lookup_zbnr),
            }

        nodes.append(node)

        if slot_id > 1:
            parent_slot_id = slot_id // 2
            relation = "father" if slot_id % 2 == 0 else "mother"

            edges.append(
                {
                    "from": parent_slot_id,
                    "to": slot_id,
                    "relation": relation,
                }
            )

    coi_result = (
        calculate_coi_for_zbnr(
            df_or_index=index,
            start_zbnr=start_zbnr_norm,
            max_generations=max_generations,
        )
        if include_coi
        else None
    )

    avk_result = (
        calculate_avk_for_zbnr(
            df_or_index=index,
            start_zbnr=start_zbnr_norm,
            max_generations=max_generations,
        )
        if include_avk
        else None
    )

    result = {
        "start_zbnr": start_zbnr_norm,
        "max_generations": max_generations,
        "node_count": len(nodes),
        "edge_count": len(edges),
        "nodes": nodes,
        "edges": edges,
        "generations": generations,
        "coi": coi_result,
        "avk": avk_result,
        "duplicates": duplicates,
    }

    if out_json_path is not None:
        import json

        out_path = Path(out_json_path)
        out_path.parent.mkdir(parents=True, exist_ok=True)

        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(
                result,
                f,
                ensure_ascii=False,
                indent=2,
                default=make_json_serializable,
            )

    return result


# ============================================================
# 3. COI
# ============================================================

def collect_pedigree_for_coi(
    index: dict[str, dict[str, Any]],
    start_zbnr: str,
    max_generations: int = 10,
) -> dict[str, dict[str, Any]]:
    """
    Sammelt alle Ahnen bis max_generations.

    Nicht vorhandene Ahnen werden als unbekannte Founder behandelt.
    Tiere in der letzten betrachteten Generation werden ebenfalls als Founder behandelt.
    """
    pedigree: dict[str, dict[str, Any]] = {}
    visiting = set()

    def recurse(zbnr: str | None, generation: int) -> None:
        zbnr = normalize_parent_zbnr(zbnr)

        if not zbnr:
            return

        if generation > max_generations:
            return

        if zbnr in visiting:
            raise ValueError(
                f"Zyklische Abstammung entdeckt bei ZBNr '{zbnr}'."
            )

        if zbnr in pedigree:
            return

        visiting.add(zbnr)

        dog = index.get(zbnr)

        if dog is None:
            pedigree[zbnr] = {
                "sire": None,
                "dam": None,
                "found_in_data": False,
            }
            visiting.remove(zbnr)
            return

        if generation >= max_generations:
            pedigree[zbnr] = {
                "sire": None,
                "dam": None,
                "found_in_data": True,
            }
            visiting.remove(zbnr)
            return

        sire = normalize_parent_zbnr(
            dog.get("vater_zbnr_norm") or dog.get("vater_zbnr")
        )
        dam = normalize_parent_zbnr(
            dog.get("mutter_zbnr_norm") or dog.get("mutter_zbnr")
        )

        pedigree[zbnr] = {
            "sire": sire,
            "dam": dam,
            "found_in_data": True,
        }

        recurse(sire, generation + 1)
        recurse(dam, generation + 1)

        visiting.remove(zbnr)

    recurse(start_zbnr, 0)

    return pedigree


def ensure_all_referenced_parents_exist_as_founders(
    pedigree: dict[str, dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    """
    Ergänzt referenzierte, aber fehlende Eltern als Founder.
    """
    changed = True

    while changed:
        changed = False
        referenced = set()

        for entry in pedigree.values():
            sire = normalize_parent_zbnr(entry.get("sire"))
            dam = normalize_parent_zbnr(entry.get("dam"))

            if sire:
                referenced.add(sire)
            if dam:
                referenced.add(dam)

        missing = referenced - set(pedigree.keys())

        for zbnr in missing:
            pedigree[zbnr] = {
                "sire": None,
                "dam": None,
                "found_in_data": False,
            }
            changed = True

    return pedigree


def order_pedigree_parents_before_offspring(
    pedigree: dict[str, dict[str, Any]],
) -> list[str]:
    """
    Sortiert Tiere so, dass Eltern vor Nachkommen stehen.
    """
    pedigree = ensure_all_referenced_parents_exist_as_founders(pedigree)

    ordered = []
    visited = set()
    visiting = set()

    def visit(zbnr: str | None) -> None:
        zbnr = normalize_parent_zbnr(zbnr)

        if zbnr is None:
            return

        if zbnr not in pedigree:
            pedigree[zbnr] = {
                "sire": None,
                "dam": None,
                "found_in_data": False,
            }

        if zbnr in visited:
            return

        if zbnr in visiting:
            raise ValueError(f"Zyklische Abstammung entdeckt bei ZBNr '{zbnr}'.")

        visiting.add(zbnr)

        entry = pedigree[zbnr]
        visit(entry.get("sire"))
        visit(entry.get("dam"))

        visiting.remove(zbnr)
        visited.add(zbnr)
        ordered.append(zbnr)

    for zbnr in list(pedigree.keys()):
        visit(zbnr)

    return ordered


def calculate_relationship_matrix(
    pedigree: dict[str, dict[str, Any]],
) -> tuple[list[str], list[list[float]]]:
    """
    Berechnet die additive Verwandtschaftsmatrix A.

    A[i, i] = 1 + F_i
    A[i, j] = additive Verwandtschaft zwischen Tier i und j
    """
    pedigree = ensure_all_referenced_parents_exist_as_founders(pedigree)

    ordered = order_pedigree_parents_before_offspring(pedigree)
    pos = {zbnr: i for i, zbnr in enumerate(ordered)}

    n = len(ordered)
    A = [[0.0 for _ in range(n)] for _ in range(n)]

    for i, animal in enumerate(ordered):
        entry = pedigree[animal]

        sire = normalize_parent_zbnr(entry.get("sire"))
        dam = normalize_parent_zbnr(entry.get("dam"))

        sire_idx = pos.get(sire)
        dam_idx = pos.get(dam)

        for j in range(i):
            value = 0.0

            if sire_idx is not None:
                value += 0.5 * A[sire_idx][j]

            if dam_idx is not None:
                value += 0.5 * A[dam_idx][j]

            A[i][j] = value
            A[j][i] = value

        if sire_idx is not None and dam_idx is not None:
            A[i][i] = 1.0 + 0.5 * A[sire_idx][dam_idx]
        else:
            A[i][i] = 1.0

    return ordered, A


def calculate_coi_for_zbnr(
    df_or_index: pd.DataFrame | dict[str, dict[str, Any]],
    start_zbnr: str,
    max_generations: int = 10,
) -> dict[str, Any]:
    """
    Berechnet den pedigreebasierten Inzuchtkoeffizienten für eine ZBNr.

    Rückgabe:
        dict mit COI, COI %, Eltern-ZBNr und Berechnungsumfang.
    """
    if isinstance(df_or_index, pd.DataFrame):
        index, _ = build_zbnr_index(df_or_index)
    else:
        index = df_or_index

    start_zbnr = normalize_parent_zbnr(start_zbnr)

    if not start_zbnr:
        raise ValueError("Keine gültige Start-ZBNr angegeben.")

    pedigree = collect_pedigree_for_coi(
        index=index,
        start_zbnr=start_zbnr,
        max_generations=max_generations,
    )

    pedigree = ensure_all_referenced_parents_exist_as_founders(pedigree)

    if start_zbnr not in pedigree:
        raise ValueError(f"ZBNr '{start_zbnr}' konnte nicht verarbeitet werden.")

    ordered, A = calculate_relationship_matrix(pedigree)
    pos = {zbnr: i for i, zbnr in enumerate(ordered)}

    dog_entry = pedigree[start_zbnr]

    sire = normalize_parent_zbnr(dog_entry.get("sire"))
    dam = normalize_parent_zbnr(dog_entry.get("dam"))

    sire_idx = pos.get(sire)
    dam_idx = pos.get(dam)

    if sire_idx is not None and dam_idx is not None:
        sire_dam_relationship = A[sire_idx][dam_idx]
        coi = 0.5 * sire_dam_relationship
    else:
        sire_dam_relationship = None
        coi = 0.0

    known_animals = sum(
        1 for entry in pedigree.values()
        if entry.get("found_in_data") is True
    )

    unknown_founders = sum(
        1 for entry in pedigree.values()
        if entry.get("found_in_data") is False
    )

    return {
        "zbnr": start_zbnr,
        "coi": coi,
        "coi_percent": coi * 100,
        "sire_zbnr": sire,
        "dam_zbnr": dam,
        "sire_dam_relationship": sire_dam_relationship,
        "animals_in_calculation": len(pedigree),
        "known_animals": known_animals,
        "unknown_founders": unknown_founders,
        "max_generations": max_generations,
        "note": (
            "Pedigreebasierter COI. Fehlende Ahnen und Platzhalter wurden "
            "als unbekannte, nicht verwandte Founder behandelt."
        ),
    }


# ============================================================
# 4. AVK und Vollständigkeit
# ============================================================

def build_positional_pedigree(
    index: dict[str, dict[str, Any]],
    start_zbnr: str,
    max_generations: int = 10,
) -> dict[int, dict[str, Any]]:
    """
    Baut eine positionsbasierte Ahnentafel.

    Doppelt vorkommende Ahnen bleiben mehrfach als Position erhalten.
    Das ist für den Ahnenverlustkoeffizienten notwendig.
    """
    start_zbnr = normalize_parent_zbnr(start_zbnr)

    max_slot = 2 ** (max_generations + 1) - 1
    slots: dict[int, dict[str, Any]] = {}

    def recurse(current_zbnr: str | None, slot: int, generation: int) -> None:
        if slot > max_slot:
            return

        current_zbnr = normalize_parent_zbnr(current_zbnr)
        dog = index.get(current_zbnr) if current_zbnr else None

        slots[slot] = {
            "slot": slot,
            "generation": generation,
            "zbnr": current_zbnr,
            "dog": dog,
            "known_zbnr": current_zbnr is not None,
            "found_in_data": dog is not None,
        }

        if generation >= max_generations:
            return

        if dog is not None:
            father = normalize_parent_zbnr(
                dog.get("vater_zbnr_norm") or dog.get("vater_zbnr")
            )
            mother = normalize_parent_zbnr(
                dog.get("mutter_zbnr_norm") or dog.get("mutter_zbnr")
            )
        else:
            father = None
            mother = None

        recurse(father, slot * 2, generation + 1)
        recurse(mother, slot * 2 + 1, generation + 1)

    recurse(start_zbnr, 1, 0)

    return slots


def calculate_avk_for_zbnr(
    df_or_index: pd.DataFrame | dict[str, dict[str, Any]],
    start_zbnr: str,
    max_generations: int = 10,
) -> dict[str, Any]:
    """
    Berechnet Ahnenverlustkoeffizient und Vollständigkeit der Ahnentafel.

    AVK-Definition hier:
        AVK = (bekannte Ahnenpositionen - verschiedene bekannte Ahnen)
              / bekannte Ahnenpositionen

    Zusätzlich wird je Generation ausgegeben:
        - erwartete Ahnenpositionen
        - bekannte ZBNr-Positionen
        - Positionen mit Datensatz in der Datei
        - kumulativer AVK
    """
    if isinstance(df_or_index, pd.DataFrame):
        index, _ = build_zbnr_index(df_or_index)
    else:
        index = df_or_index

    slots = build_positional_pedigree(
        index=index,
        start_zbnr=start_zbnr,
        max_generations=max_generations,
    )

    generation_rows = []

    deepest_complete_generation_by_zbnr = 0
    deepest_complete_generation_in_data = 0

    cumulative_known_positions = []
    cumulative_found_positions = []

    for generation in range(1, max_generations + 1):
        expected = 2 ** generation

        gen_slots = [
            entry for entry in slots.values()
            if entry["generation"] == generation
        ]

        known_zbnr_entries = [
            entry for entry in gen_slots
            if entry["known_zbnr"]
        ]

        found_entries = [
            entry for entry in gen_slots
            if entry["found_in_data"]
        ]

        known_count = len(known_zbnr_entries)
        found_count = len(found_entries)

        complete_by_zbnr = known_count == expected
        complete_in_data = found_count == expected

        if complete_by_zbnr:
            deepest_complete_generation_by_zbnr = generation

        if complete_in_data:
            deepest_complete_generation_in_data = generation

        cumulative_known_positions.extend(
            entry["zbnr"] for entry in known_zbnr_entries
            if entry["zbnr"] is not None
        )

        cumulative_found_positions.extend(
            entry["zbnr"] for entry in found_entries
            if entry["zbnr"] is not None
        )

        known_total = len(cumulative_known_positions)
        unique_known = len(set(cumulative_known_positions))
        ancestor_loss_known = known_total - unique_known
        avk_known = ancestor_loss_known / known_total if known_total > 0 else None

        found_total = len(cumulative_found_positions)
        unique_found = len(set(cumulative_found_positions))
        ancestor_loss_found = found_total - unique_found
        avk_found = ancestor_loss_found / found_total if found_total > 0 else None

        generation_rows.append(
            {
                "generation": generation,
                "expected_positions": expected,
                "known_zbnr_positions": known_count,
                "found_in_data_positions": found_count,
                "complete_by_zbnr": complete_by_zbnr,
                "complete_in_data": complete_in_data,
                "cumulative_known_positions": known_total,
                "cumulative_unique_known_ancestors": unique_known,
                "cumulative_ancestor_loss_known": ancestor_loss_known,
                "avk_known": avk_known,
                "avk_known_percent": avk_known * 100 if avk_known is not None else None,
                "cumulative_found_positions": found_total,
                "cumulative_unique_found_ancestors": unique_found,
                "cumulative_ancestor_loss_found": ancestor_loss_found,
                "avk_found": avk_found,
                "avk_found_percent": avk_found * 100 if avk_found is not None else None,
            }
        )

    all_known_ancestors = [
        entry["zbnr"]
        for entry in slots.values()
        if entry["generation"] > 0
        and entry["known_zbnr"]
        and entry["zbnr"] is not None
    ]

    all_found_ancestors = [
        entry["zbnr"]
        for entry in slots.values()
        if entry["generation"] > 0
        and entry["found_in_data"]
        and entry["zbnr"] is not None
    ]

    possible_total = sum(2 ** g for g in range(1, max_generations + 1))

    known_total = len(all_known_ancestors)
    unique_known_total = len(set(all_known_ancestors))
    ancestor_loss_known_total = known_total - unique_known_total
    avk_known_total = (
        ancestor_loss_known_total / known_total
        if known_total > 0
        else None
    )

    found_total = len(all_found_ancestors)
    unique_found_total = len(set(all_found_ancestors))
    ancestor_loss_found_total = found_total - unique_found_total
    avk_found_total = (
        ancestor_loss_found_total / found_total
        if found_total > 0
        else None
    )

    return {
        "zbnr": normalize_parent_zbnr(start_zbnr),
        "max_generations": max_generations,
        "possible_ancestor_positions": possible_total,

        "deepest_complete_generation_by_zbnr": deepest_complete_generation_by_zbnr,
        "deepest_complete_generation_in_data": deepest_complete_generation_in_data,

        "known_ancestor_positions": known_total,
        "unique_known_ancestors": unique_known_total,
        "ancestor_loss_known": ancestor_loss_known_total,
        "avk_known": avk_known_total,
        "avk_known_percent": avk_known_total * 100 if avk_known_total is not None else None,

        "found_ancestor_positions": found_total,
        "unique_found_ancestors": unique_found_total,
        "ancestor_loss_found": ancestor_loss_found_total,
        "avk_found": avk_found_total,
        "avk_found_percent": avk_found_total * 100 if avk_found_total is not None else None,

        "generation_rows": generation_rows,

        "note": (
            "AVK bezogen auf bekannte Ahnenpositionen. Bei unvollständigen "
            "Ahnentafeln sollte die Vollständigkeit je Generation mit angegeben werden."
        ),
    }


# ============================================================
# Beispiel für lokale Nutzung
# ============================================================

if __name__ == "__main__":
    # 1. Einmalig mergen
    merged_df, merge_report = merge_dog_data_with_ebv(
        base_csv_path="hunde.csv",
        ebv_csv_path="zws.csv",
        out_csv_path="hunde_mit_zws.csv",
    )

    print("Merge-Report:")
    print(merge_report)
    print()

    # Alternativ später direkt die gemergte Datei laden:
    # merged_df = load_merged_dog_file("hunde_mit_zws.csv")

    index, duplicates = build_zbnr_index(merged_df)

    start_zbnr = "LCD 12/T 1692"
    safe_zbnr = safe_filename_part(start_zbnr)

    # 2. HTML-Ahnentafel
    result_html = create_pedigree_html_for_zbnr(
        df_or_index=index,
        start_zbnr=start_zbnr,
        out_html_path=Path("ahnentafeln") / f"ahnentafel_{safe_zbnr}.html",
        max_generations=5,
        include_coi=True,
        include_avk=True,
    )

    print("HTML gespeichert unter:")
    print(result_html["path"])
    print()

    # 3. COI separat
    coi = calculate_coi_for_zbnr(
        df_or_index=index,
        start_zbnr=start_zbnr,
        max_generations=10,
    )

    print("COI:")
    print(coi)
    print()

    # 4. AVK separat
    avk = calculate_avk_for_zbnr(
        df_or_index=index,
        start_zbnr=start_zbnr,
        max_generations=10,
    )

    print("AVK:")
    print({
        "zbnr": avk["zbnr"],
        "avk_known_percent": avk["avk_known_percent"],
        "deepest_complete_generation_by_zbnr": avk["deepest_complete_generation_by_zbnr"],
        "deepest_complete_generation_in_data": avk["deepest_complete_generation_in_data"],
    })
