Lokale Flask-Webapp zur Anzeige von Ahnentafeln

Kurz:
- Starte die App lokal: `python app.py`
- Öffne `http://localhost:5000` im Browser
- Lokaler Login-Fallback: Benutzer `admin`, Passwort `admin`

Voraussetzungen:
- Python 3.8+
- Installiere Abhängigkeiten: `pip install -r requirements.txt`

Konfiguration:
- `APP_USERNAME`: Benutzername fuer den Login
- `APP_PASSWORD`: Passwort fuer den Login
- `SECRET_KEY`: geheimer Schluessel fuer Flask-Sessions

Beispiel lokal:
`APP_USERNAME=bernd APP_PASSWORD=geheim SECRET_KEY=dev-secret python app.py`

Die App nutzt `pedigree_tools.py` aus demselben Verzeichnis und die CSV-Dateien:
- `drc-Hunde-mit-eltern-rkey.csv`
- `ed_zws_results_all_animals.csv`

Funktionalität:
- Suche nach Hundename oder ZBNr
- Trefferliste anzeigen
- Ahnentafel als HTML anzeigen (erstellt durch `pedigree_tools.create_pedigree_html_for_zbnr`)
