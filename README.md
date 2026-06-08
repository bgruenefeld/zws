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
- `USER_DOGS_CSV`: Pfad zur CSV-Datei fuer manuell hinzugefuegte Hunde
- `USER_DOGS_LOCK_FILE`: optionaler Pfad zur Lock-Datei fuer Schreibzugriffe

Beispiel lokal:
`APP_USERNAME=bernd APP_PASSWORD=geheim SECRET_KEY=dev-secret python app.py`

Beispiel Render mit Persistent Disk:
`USER_DOGS_CSV=/var/data/user_hunde.csv`

Die Datei `user_hunde.csv` wird automatisch angelegt, sobald der erste eigene Hund gespeichert wird. Auf Render sollte der Pfad auf die gemountete Persistent Disk zeigen, nicht in das normale App-Verzeichnis.
Die Lock-Datei wird standardmaessig daneben angelegt, z. B. `/var/data/user_hunde.csv.lock`.

Die App nutzt `pedigree_tools.py` aus demselben Verzeichnis und die CSV-Dateien:
- `drc-Hunde-mit-eltern-rkey.csv`
- `ed_zws_results_all_animals.csv`
- optional `user_hunde.csv` fuer eigene Hunde

Funktionalität:
- Suche nach Hundename oder ZBNr
- Trefferliste anzeigen
- Ahnentafel als HTML anzeigen (erstellt durch `pedigree_tools.create_pedigree_html_for_zbnr`)
