@echo off
setlocal

cd /d "%~dp0"

echo Building single-file Winbetin Balance Checker v2 EXE...
python -m PyInstaller --noconfirm --clean WinbetinBalanceChecker_v2.spec
if errorlevel 1 (
    echo.
    echo Build failed.
    exit /b %errorlevel%
)

echo.
echo Build complete:
echo %cd%\dist\WinbetinBalanceChecker_v2.exe
