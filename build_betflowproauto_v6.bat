@echo off
setlocal
cd /d "%~dp0"

echo ============================================================
echo  Building: BetflowProAutoV6.exe  (v6.1.0 portfolio release)
echo  - PORTFOLIO LAYER: shared bankroll + risk budget across all
echo    accounts, per-account 40%% drawdown freeze, portfolio 20%%
echo    halt (catches every account bleeding at once)
echo  - CROSS-ACCOUNT CORRELATION: one game = one account, league
echo    spread cap, market concentration cap across the fleet
echo  - VARIANCE-SCALED FRACTIONAL KELLY replaces flat 20/10:
echo    1/5 Kelly, scaled down by each account's own volatility,
echo    hard-capped at 5%% of balance and of the whole portfolio
echo  - CLV tracking: snapshots the price taken, re-reads the line
echo    near kick-off, reports average closing-line value by market
echo  - HARD 6-LEG CAP (14/25-leg shapes returned -100%%)
echo  - SYSTEMATIC CASH-OUT keyed to STAKE recovery, not to a
echo    fraction of a possible-win that no longer exists
echo  - REAL/SHADOW LEARNING SPLIT: shadow slips can no longer
echo    unlock the bandit or dilute real-money ROI
echo  - LOSING-RECIPE VETO: shapes proven bad on real money stop
echo  - REFUSAL COUNTERS + weekly portfolio digest
echo  - keeps v6.0: slip EV gate, bankroll share, signed market
echo    weights, confidence-first DC, fresh-slip clear
echo  - does NOT touch or remove V4/V5/V56 or SportsApeV2Checker_v2.exe
echo ============================================================
echo.

python -m PyInstaller --noconfirm --clean --log-level=WARN BetflowProAutoV6.spec
if errorlevel 1 (
    echo.
    echo  BUILD FAILED.
    exit /b %errorlevel%
)

echo.
echo  Build COMPLETE:
echo  %cd%\dist\BetflowProAutoV6.exe
if exist "%cd%\dist\BetflowProAutoV6.exe" (
    echo.
    echo  SUCCESS - V6 EXE is ready:
    dir /b "%cd%\dist\BetflowProAutoV6.exe"
) else (
    echo.
    echo  WARNING: EXE not found at expected path.
)
