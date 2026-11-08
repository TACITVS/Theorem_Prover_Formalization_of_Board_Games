# Automated Lean 4.35.0 Proof Compiler & Strict Axiom Allowlist Validator
$ErrorActionPreference = "Stop"

$leanBin = "$env:USERPROFILE\.elan\bin\lean.exe"
if (-not (Test-Path $leanBin)) {
    $leanBin = "lean"
}

Write-Host "=== Compiling Generalized (m, n, k) Games Formal Proof in Lean 4.35.0 ===" -ForegroundColor Cyan
Push-Location (Join-Path $PSScriptRoot "lean4")
try {
    & $leanBin --version
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    $output = & $leanBin "MNKGames.lean" 2>&1
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

# Verify axioms output
$lines = $output | Where-Object { $_ -match "^'.*' depends on axioms:" }
Write-Host "Axiom dependency report ($($lines.Count) theorems checked):" -ForegroundColor Magenta
$customAxioms = @()
foreach ($l in $lines) {
    $axioms = $l -replace "^'.*' depends on axioms: \[(.*)\]$", '$1'
    if ($axioms.Trim() -ne "") {
        $axList = $axioms.Split(",") | ForEach-Object { $_.Trim() }
        foreach ($ax in $axList) {
            if ($ax -ne "propext" -and $ax -ne "Classical.choice" -and $ax -ne "Quot.sound") {
                $customAxioms += "$l -> $ax"
            }
        }
    }
}

if ($customAxioms.Count -gt 0) {
    Write-Host "ERROR: Found non-standard custom axioms:" -ForegroundColor Red
    $customAxioms | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
    exit 1
}

Write-Host "SUCCESS: Lean 4 proof verified with 0 sorry and 0 custom axioms ($([math]::Round($sw.Elapsed.TotalSeconds, 2))s)!" -ForegroundColor Green
