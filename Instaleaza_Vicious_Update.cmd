@echo off
setlocal
title Instalare Vicious Macro Update

set "DOWNLOAD_URL=https://github.com/flaviu09/ViciousBeeFarm/releases/latest/download/ViciousBeeFarm_latest.exe"
set "HASH_URL=https://github.com/flaviu09/ViciousBeeFarm/releases/latest/download/ViciousBeeFarm_latest.exe.sha256"
set "SOURCE=C:\Users\Public\Documents\ViciousBeeFarm_latest.exe"
set "SOURCE_DOWNLOAD=%SOURCE%.download"
set "HASH_DOWNLOAD=%SOURCE%.sha256.download"
set "TARGET=C:\Users\macro1\Documents\ViciousBeeFarm_onedir_optimized\ViciousBeeFarm_onedir_optimized\ViciousBeeFarm.exe"

echo Inchide ViciousBeeFarm.exe inainte de instalare.
echo.

tasklist /FI "IMAGENAME eq ViciousBeeFarm.exe" 2>nul | find /I "ViciousBeeFarm.exe" >nul
if not errorlevel 1 (
    echo EROARE: ViciousBeeFarm.exe este deschis. Inchide-l si ruleaza din nou acest fisier.
    pause
    exit /b 1
)

if not exist "C:\Users\Public\Documents" mkdir "C:\Users\Public\Documents"
if not exist "%TARGET%" (
    echo EROARE: Nu gasesc folderul macroului la:
    echo %TARGET%
    pause
    exit /b 1
)

echo Descarc ultima versiune de pe GitHub...
powershell.exe -NoProfile -ExecutionPolicy Bypass -Command "$ProgressPreference='SilentlyContinue'; Invoke-WebRequest -UseBasicParsing -Uri '%DOWNLOAD_URL%' -OutFile '%SOURCE_DOWNLOAD%'; Invoke-WebRequest -UseBasicParsing -Uri '%HASH_URL%' -OutFile '%HASH_DOWNLOAD%'"
if errorlevel 1 (
    echo EROARE: Downloadul update-ului a esuat.
    del /q "%SOURCE_DOWNLOAD%" "%HASH_DOWNLOAD%" 2>nul
    pause
    exit /b 1
)

echo Verific integritatea update-ului...
powershell.exe -NoProfile -ExecutionPolicy Bypass -Command "$expected=((Get-Content -LiteralPath '%HASH_DOWNLOAD%' -Raw).Trim() -split '\s+')[0]; $actual=(Get-FileHash -Algorithm SHA256 -LiteralPath '%SOURCE_DOWNLOAD%').Hash; if ($actual -ne $expected) { Write-Error ('SHA256 diferit: ' + $actual); exit 1 }"
if errorlevel 1 (
    echo EROARE: Verificarea SHA-256 a esuat. Fisierul nu va fi instalat.
    del /q "%SOURCE_DOWNLOAD%" "%HASH_DOWNLOAD%" 2>nul
    pause
    exit /b 1
)

move /Y "%SOURCE_DOWNLOAD%" "%SOURCE%" >nul
copy /Y "%SOURCE%" "%TARGET%" >nul
if errorlevel 1 (
    echo EROARE: Nu am putut inlocui EXE-ul.
    pause
    exit /b 1
)

del /q "%HASH_DOWNLOAD%" 2>nul
echo.
echo Update instalat cu succes.
start "" "%TARGET%"
timeout /t 2 /nobreak >nul
exit /b 0
