@echo off
setlocal

cd /d "%~dp0"

echo Building safer one-folder SportsApe V2 Checker...
python -m PyInstaller --noconfirm --clean SportsApeV2_safe.spec
if errorlevel 1 (
    echo.
    echo Build failed.
    exit /b %errorlevel%
)

echo.
echo Build complete:
echo %cd%\dist\SportsApeV2_safe\
echo Run:
echo %cd%\dist\SportsApeV2_safe\SportsApeV2_safe.exe
