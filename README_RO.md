# Vicious Bee Farm

Macro pentru automatizarea cautarii Vicious Bee in Bee Swarm Simulator. Aplicatia cauta servere publice, detecteaza incarcarea jocului si noaptea, revendica un hive liber, ruleaza traseele configurate si monitorizeaza lupta.

## Descarcare si rulare

1. Descarca arhiva portabila din pagina **Releases**.
2. Extrage arhiva complet. Nu porni executabilul direct din arhiva.
3. Porneste `ViciousBeeFarm.exe`.
4. Seteaza viteza de miscare a contului si celelalte optiuni necesare.
5. Foloseste `F1` pentru pornire si `F2` pentru oprire.

Butonul `Update Macro` descarca ultima versiune din GitHub Release, pastreaza `config.json` si modificarile locale din `paths`, instaleaza update-ul dupa inchiderea aplicatiei si redeschide executabilul.

Pachetul Release include runtime-ul Python, OpenCV, ONNX Runtime, modelele, template-urile, pathurile si Tesseract OCR portabil. Nu este necesara instalarea Python, rularea `pip` sau instalarea separata a Tesseract.

Configuratia si detectia sunt calibrate pentru Windows pe rezolutia `1366x768`, cu scalarea ecranului la `100%`. Roblox trebuie sa fie instalat, autentificat si vizibil pe ecran. Viteza de miscare trebuie setata pentru fiecare cont.

## Build din sursa

```powershell
python -m venv .venv
.\.venv\Scripts\pip install -r requirements.txt
Copy-Item config.example.json config.json
.\.venv\Scripts\python.exe -m PyInstaller --noconfirm --clean ViciousBeeFarmOnedir.spec
```

Resursele externe din `models`, `paths`, `templates` si `vic find` trebuie pastrate langa executabilul construit.

## Observatii

- Detectia Haste si Bear Morph ajusteaza automat timpul pathurilor in functie de viteza efectiva.
- Functionarea prin Remote Desktop necesita ca sesiunea Roblox sa ramana activa si randata.
- Proiect independent, neafiliat cu Roblox sau Bee Swarm Simulator.
