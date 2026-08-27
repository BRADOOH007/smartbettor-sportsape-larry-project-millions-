@echo off
setlocal

cd /d "%~dp0"

echo Building single-file Winbetin Balance Checker EXE...
python -m PyInstaller --noconfirm --clean WinbetinBalanceChecker.spec
if errorlevel 1 (
    echo.
    echo Build failed.
    exit /b %errorlevel%
)

echo.
echo Build complete:
echo %cd%\dist\WinbetinBalanceChecker.exe
