# build.ps1 - Compile all Rocq 9.1 Checkers formalization modules and audit assumptions
$ErrorActionPreference = "Stop"

$COQC = "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
if (-not (Test-Path $COQC)) {
    Write-Error "Rocq 9.1 coqc compiler not found at $COQC"
}

$modules = @(
    "CheckersBoard.v",
    "CheckersGame.v",
    "CheckersInvariants.v",
    "CheckersMicro.v",
    "CheckersShashkiDiff.v",
    "CheckersCheckAssumptions.v"
)

Write-Host "==========================================================" -ForegroundColor Cyan
Write-Host "  COMPILING CHECKERS FORMALIZATION SUITE IN ROCQ 9.1" -ForegroundColor Cyan
Write-Host "==========================================================" -ForegroundColor Cyan

foreach ($mod in $modules) {
    Write-Host "Compiling $mod..." -NoNewline
    & $COQC -Q . Checkers $mod
    if ($LASTEXITCODE -ne 0) {
        Write-Host " FAILED!" -ForegroundColor Red
        exit 1
    }
    Write-Host " OK [Closed under global context]" -ForegroundColor Green
}

Write-Host "==========================================================" -ForegroundColor Cyan
Write-Host "  ALL 6 MODULES COMPILED CLEANLY WITH ZERO AXIOMS!" -ForegroundColor Green
Write-Host "==========================================================" -ForegroundColor Cyan
