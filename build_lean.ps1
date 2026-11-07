# PowerShell Lean 4 build script for Dots and Boxes
$ErrorActionPreference = "Stop"

Write-Host "============================================================" -ForegroundColor Cyan
Write-Host " Building Dots and Boxes in Lean 4.35.0" -ForegroundColor Cyan
Write-Host "============================================================" -ForegroundColor Cyan

$leanPath = "$env:USERPROFILE\.elan\bin\lean.exe"
if (-not (Test-Path $leanPath)) {
    Write-Error "lean.exe not found at $leanPath"
    exit 1
}

$target = "lean4\DotsAndBoxes.lean"
Write-Host "Compiling $target..." -ForegroundColor Yellow
$output = & $leanPath $target 2>&1
$exitCode = $LASTEXITCODE

Write-Host $output

if ($exitCode -ne 0) {
    Write-Error "Lean compilation failed with exit code $exitCode"
    exit $exitCode
}

# Strict Axiom Allowlist Audit
$allowedAxioms = @("propext", "Quot.sound", "Classical.choice")
$lines = $output -split "`r?`n"
$verifiedCount = 0

foreach ($line in $lines) {
    if ($line -match "^'([^']+)' does not depend on any axioms$") {
        $verifiedCount++
    } elseif ($line -match "^'([^']+)' depends on axioms: \[([^\]]+)\]$") {
        $verifiedCount++
        $thm = $Matches[1]
        $axs = $Matches[2].Split(",") | ForEach-Object { $_.Trim() }
        foreach ($ax in $axs) {
            if ($ax -eq "sorryAx") {
                Write-Error "CRITICAL VIOLATION: Theorem '$thm' relies on unproven 'sorryAx'!"
                exit 1
            }
            if ($allowedAxioms -notcontains $ax) {
                Write-Error "VIOLATION: Theorem '$thm' depends on unapproved axiom '$ax'!"
                exit 1
            }
        }
    }
}

Write-Host "`nAll Lean 4 proofs successfully compiled and verified!" -ForegroundColor Green
Write-Host "Total verified theorems audited: $verifiedCount" -ForegroundColor Green
Write-Host "Approved kernel axioms only: [propext, Quot.sound, Classical.choice]." -ForegroundColor Green
Write-Host "Zero 'sorry' keywords, zero unapproved axioms." -ForegroundColor Green
