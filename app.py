from pathlib import Path
from urllib.parse import quote_plus
import math

from flask import Flask, render_template, request, redirect, url_for, Response, jsonify
import re

import pedigree_tools as pt
import pandas as pd


APP_DIR = Path(__file__).parent
BASE_CSV = APP_DIR / "drc-Hunde-mit-eltern-rkey.csv"
ZWS_CSV = APP_DIR / "ed_zws_results_all_animals.csv"


app = Flask(__name__)


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

    return {
        "name": clean_text(row.get("Name")) or "unbekannt",
        "zbnr": clean_text(row.get("ZBNr_norm")) or clean_text(row.get("ZBNr")),
        "wurfdatum": clean_text(row.get("Wurfdatum")) or clean_text(row.get("geburt")),
        "geschlecht": clean_text(row.get("Geschlecht")) or clean_text(row.get("sex")),
        "hd": clean_text(row.get("HD_Grad")) or clean_text(row.get("HD")),
        "ed": ed,
        "zuchtwert": ebv,
        "konfidenz": confidence,
    }


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


@app.route("/", methods=["GET", "POST"])
def home():
    """Home/landing page with search box."""
    # If there's a query, redirect to /search
    query = request.values.get("q", "").strip()
    if query:
        return redirect(url_for("search_results", q=query, page=1))
    
    # Render home page with population stats
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
        
        # Calculate röntgenquote for display
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

        # build distribution of ED_ZWS per birth year (exclude 2025)
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
                    is_significant = p_value < 0.05
                    stats_ed23_analysis = {
                        "is_significant": is_significant,
                        "p_value": p_value,
                        "interpretation": "Der Anteil schwererer ED-Befunde zeigt im betrachteten Zeitraum keinen statistisch gesicherten Trend."
                    }
    else:
        stats_ed_evaluated = 0
        stats_ed_percent = 0.0
        roentgen_quote = 0.0
    
    return render_template(
        "home.html",
        stats_total=stats_total,
        stats_ed_evaluated=stats_ed_evaluated,
        stats_ed_percent=stats_ed_percent,
        roentgen_quote=roentgen_quote,
        stats_ed_distribution=stats_ed_distribution,
        stats_ed23_analysis=stats_ed23_analysis,
    )


@app.route("/info")
def info():
    return render_template("info.html")


@app.route("/search", methods=["GET"])
def search_results():
    """Search results page."""
    query = request.args.get("q", "").strip()
    if not query:
        return redirect(url_for("home"))
    
    q = query.lower()
    df = MERGED_DF

    # search in Name and ZBNr columns
    mask = (
        df["Name"].fillna("").str.lower().str.contains(q, na=False)
        | df["ZBNr"].fillna("").str.lower().str.contains(q, na=False)
    )

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
        )
    
    page_count = max(1, math.ceil(total_matches / page_size))
    if page > page_count:
        page = page_count

    recs = matches.iloc[(page - 1) * page_size : page * page_size].to_dict(orient="records")

    results = []
    for r in recs:
        z = r.get("ZBNr_norm") or r.get("ZBNr")
        hd = r.get("HD_Grad") or r.get("HD") or None
        ed = r.get("ED_rechts") or r.get("ED_rechts_raw") or r.get("ED_links") or None
        zucht_raw = r.get("EBV") or r.get("ed_zw_0_10_niedrig_gut")
        wurfdatum = r.get("Wurfdatum")
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
        res["ed"] = ed
        res["konfidenz"] = konf
        res["zuchtwert"] = zucht
        res["wurfdatum"] = wurfdatum
        res["name"] = r.get("Name", "unbekannt")
        res["geschlecht"] = r.get("Geschlecht") or r.get("sex") or "unbekannt"
        res["vater"] = r.get("Vater") or "unbekannt"
        res["mutter"] = r.get("Mutter") or "unbekannt"
        
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
    zbnr = clean_text(request.args.get("zbnr"))
    if not zbnr:
        return jsonify({"error": "no zbnr provided"}), 400

    dog = ZBNR_INDEX.get(zbnr)
    if dog is None:
        return jsonify({"error": "dog not found"}), 404

    father = clean_text(dog.get("vater_zbnr_norm") or dog.get("vater_zbnr"))
    mother = clean_text(dog.get("mutter_zbnr_norm") or dog.get("mutter_zbnr"))
    litter_date = clean_text(dog.get("Wurfdatum") or dog.get("geburt"))

    if not father or not mother or not litter_date:
        return jsonify(
            {
                "dog": dog_summary(dog),
                "littermates": [],
                "message": "Für diesen Hund fehlen Vater, Mutter oder Wurfdatum.",
            }
        )

    father_series = MERGED_DF.get("vater_zbnr_norm", pd.Series([""] * len(MERGED_DF))).map(clean_text)
    mother_series = MERGED_DF.get("mutter_zbnr_norm", pd.Series([""] * len(MERGED_DF))).map(clean_text)
    date_series = MERGED_DF.get("Wurfdatum", pd.Series([""] * len(MERGED_DF))).map(clean_text)
    zbnr_series = (
        MERGED_DF["ZBNr_norm"].map(clean_text)
        if "ZBNr_norm" in MERGED_DF.columns
        else MERGED_DF["ZBNr"].map(clean_text)
    )

    mask = (
        (father_series == father)
        & (mother_series == mother)
        & (date_series == litter_date)
        & (zbnr_series != zbnr)
    )

    siblings = [
        dog_summary(row)
        for row in MERGED_DF.loc[mask].sort_values(by="Name", na_position="last").to_dict(orient="records")
    ]

    offspring_mask = (father_series == zbnr) | (mother_series == zbnr)
    offspring = [
        dog_summary(row)
        for row in MERGED_DF.loc[offspring_mask]
        .sort_values(by=["Wurfdatum", "Name"], na_position="last")
        .to_dict(orient="records")
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
