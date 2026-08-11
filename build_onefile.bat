@echo off
setlocal

cd /d "%~dp0"

echo Building single-file SportsApe V2 Checker EXE...
python -m PyInstaller --noconfirm --clean SportsApeV2Checker.spec
if errorlevel 1 (
    echo.
    echo Build failed.
    exit /b %errorlevel%
)

echo.
echo Build complete:
echo %cd%\dist\SportsApeV2Checker.exe
