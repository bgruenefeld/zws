Lokale Flask-Webapp zur Anzeige von Ahnentafeln

Kurz:
- Starte die App lokal: `python app.py`
- Öffne `http://localhost:5000` im Browser

Voraussetzungen:
- Python 3.8+
- Installiere Abhängigkeiten: `pip install -r requirements.txt`

Die App nutzt `pedigree_tools.py` aus demselben Verzeichnis und die CSV-Dateien:
- `drc-Hunde-mit-eltern-rkey.csv`
- `ed_zws_results_all_animals.csv`

Funktionalität:
- Suche nach Hundename oder ZBNr
- Trefferliste anzeigen
- Ahnentafel als HTML anzeigen (erstellt durch `pedigree_tools.create_pedigree_html_for_zbnr`)
