@echo off
setlocal

cd /d "%~dp0"

echo Building safer one-folder Winbetin Balance Checker v2...
python -m PyInstaller --noconfirm --clean WBC_v2_safe.spec
if errorlevel 1 (
    echo.
    echo Build failed.
    exit /b %errorlevel%
)

echo.
echo Build complete:
echo %cd%\dist\WBC_v2_safe\
echo Run:
echo %cd%\dist\WBC_v2_safe\WBC_v2_safe.exe
