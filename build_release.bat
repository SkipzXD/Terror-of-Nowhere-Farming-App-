@echo off
setlocal enabledelayedexpansion
cd /d "%~dp0"
REM ============================================================
REM  PUBLIC build of ToN Toolkit - everything except the AFK Helper.
REM    dist\ToNToolkit\              the app, ready to run
REM    release\ToNToolkit-vX.X.zip   attach this to a GitHub release
REM
REM  Includes the terror picker with all its data:
REM    terror_names.json, terror_icons.png, terror_icons_unbound.png
REM  Never includes, whatever is in your working folder:
REM    personal.txt      (would turn the AFK Helper on)
REM    ton_toolkit.json  (your own settings)
REM ============================================================

set "PY=C:\Users\Owner\AppData\Local\Python\pythoncore-3.14-64\python.exe"
if not exist "%PY%" set "PY=python"

REM Version comes from ton_toolkit.py (APP_VERSION); this is only a fallback.
set "VERSION=1.1"
for /f "usebackq delims=" %%V in (`call "%PY%" -c "import re;s=open('ton_toolkit.py',encoding='utf-8').read();m=re.search('APP_VERSION = .([0-9.]+).',s);print(m.group(1) if m else '')"`) do (
  if not "%%V"=="" set "VERSION=%%V"
)

echo ============================================================
echo  ToN Toolkit  v%VERSION%   (public build)
echo ============================================================
echo.

REM ---- 1. check the pieces are here -------------------------
set "MISSING="
for %%F in (ton_toolkit.py icon.ico LICENSE release_check.py terror_names.json terror_icons.png terror_icons_unbound.png) do (
  if not exist "%%F" set "MISSING=!MISSING! %%F"
)
if defined MISSING (
  echo  ERROR: missing:!MISSING!
  echo  Put them in this folder ^(beside build_release.bat^) and run again.
  pause
  exit /b 1
)
if not exist "Sounds" echo   NOTE: no Sounds folder - alerts will be silent
findstr /c:"<YOUR NAME" LICENSE >nul 2>&1
if not errorlevel 1 (
  echo   WARNING: LICENSE still has the name placeholder in it.
)
echo  [1/6] files present

REM ---- 2. build tools ---------------------------------------
"%PY%" -m pip install --upgrade --quiet pyinstaller python-osc zeroconf
if errorlevel 1 (echo  ERROR: could not install build tools & pause & exit /b 1)
echo  [2/6] build tools ready

REM ---- 3. clean ---------------------------------------------
rmdir /s /q build dist release 2>nul
del /q ToNToolkit.spec 2>nul
echo  [3/6] cleaned

REM ---- 4. build ---------------------------------------------
echo  [4/6] building, this takes a minute...
"%PY%" -m PyInstaller --noconfirm --clean --windowed --name ToNToolkit ^
    --icon "icon.ico" ^
    --add-data "icon.ico;." ^
    --add-data "Sounds;Sounds" ^
    --add-data "terror_names.json;." ^
    --add-data "terror_icons.png;." ^
    --add-data "terror_icons_unbound.png;." ^
    --add-data "LICENSE;." ^
    --add-data "DISCLAIMER.md;." ^
    --collect-all zeroconf ^
    ton_toolkit.py >build_log.txt 2>&1
if not exist "dist\ToNToolkit\ToNToolkit.exe" (
  echo  BUILD FAILED - last 25 lines:
  powershell -NoProfile -Command "Get-Content build_log.txt -Tail 25"
  pause
  exit /b 1
)

REM ---- 5. files beside the exe --------------------------------
REM Only the documents go beside the exe. The icons, terror data, sounds
REM and app icon are already packed inside _internal by the build.
copy /y "LICENSE" "dist\ToNToolkit\" >nul
if exist "DISCLAIMER.md" copy /y "DISCLAIMER.md" "dist\ToNToolkit\" >nul
if exist "README.md"     copy /y "README.md"     "dist\ToNToolkit\" >nul
REM Never ship anything personal, even if it was sitting in this folder.
for /r "dist\ToNToolkit" %%F in (personal.txt ton_toolkit.json) do (
  if exist "%%F" del /q "%%F"
)
"%PY%" release_check.py "dist\ToNToolkit"
if errorlevel 1 (
  pause
  exit /b 1
)
echo  [5/6] files copied and checked

REM ---- 6. zip for the release page --------------------------
mkdir release 2>nul
powershell -NoProfile -Command ^
  "Compress-Archive -Path 'dist\ToNToolkit\*' -DestinationPath 'release\ToNToolkit-v%VERSION%.zip' -Force"
echo  [6/6] packaged

echo.
echo ============================================================
echo  DONE  (public build v%VERSION%)
echo.
echo  Run it       : dist\ToNToolkit\ToNToolkit.exe
echo  Upload this  : release\ToNToolkit-v%VERSION%.zip
echo.
echo  The first log line should read: ToN Toolkit %VERSION%
echo  (no "personal build", and no AFK Helper on the TON Helper tab)
echo ============================================================
echo.
pause
