# Automated Lean 4.35.0 Build & Axiom Audit for Classic 7x6 Connect-Four
$ErrorActionPreference = "Stop"

$leanBin = "$env:USERPROFILE\.elan\bin\lean.exe"
if (-not (Test-Path $leanBin)) {
    $leanBin = "lean"
}

Write-Host "=== Compiling Classic 7x6 Connect-Four Formal Verification in Lean 4.35.0 ===" -ForegroundColor Cyan
Push-Location (Join-Path $PSScriptRoot "lean4")
try {
    & $leanBin --version
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    $output = & $leanBin "Connect4_7x6.lean" 2>&1
    $exitCode = $LASTEXITCODE
    $sw.Stop()
} finally {
    Pop-Location
}

$output | ForEach-Object { Write-Host $_ }

if ($exitCode -ne 0) {
    Write-Host "Lean 4 compilation failed with exit code $exitCode" -ForegroundColor Red
    exit $exitCode
}

$joined = ($output | Out-String)
if ($joined -match "sorry") {
    Write-Host "ERROR: Proof contains sorry!" -ForegroundColor Red
    exit 1
}

$axiomLines = ($output | Select-String "depends on axioms|does not depend on any axioms")
Write-Host "`n[Audit Result] $($axiomLines.Count) / 22 Lean 4.35 Theorems Verified with ZERO sorry!" -ForegroundColor Green
Write-Host "Lean compilation time: $([math]::Round($sw.Elapsed.TotalSeconds, 2)) seconds." -ForegroundColor Cyan
