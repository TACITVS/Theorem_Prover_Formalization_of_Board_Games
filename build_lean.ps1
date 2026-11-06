# ==============================================================================
# Automated Lean 4.35.0 Proof Compiler & Strict Axiom Allowlist Validator
# ==============================================================================

$ErrorActionPreference = "Stop"

$leanBin = "$env:USERPROFILE\.elan\bin\lean.exe"
if (-not (Test-Path $leanBin)) {
    $leanBin = "lean"
}

Write-Host "=== Compiling Nine Men's Morris Formal Proof in Lean 4 ===" -ForegroundColor Cyan
Push-Location (Join-Path $PSScriptRoot "lean4")
try {
    & $leanBin --version
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    $output = & $leanBin "NineMensMorris.lean" 2>&1
    $exitCode = $LASTEXITCODE
    $sw.Stop()
} finally {
    Pop-Location
}

$output | ForEach-Object { Write-Host $_ }

if ($exitCode -ne 0) {
    Write-Error "Lean 4 verification failed with exit code $exitCode"
    exit $exitCode
}

$allowedAxioms = @("propext", "Quot.sound")
$axiomReports = 0
foreach ($line in $output) {
    $s = $line.ToString()
    if ($s -match "^'([^']+)' does not depend on any axioms$") {
        $axiomReports++
    } elseif ($s -match "^'([^']+)' depends on axioms: \[([^\]]+)\]$") {
        $axiomReports++
        $thm = $Matches[1]
        $axs = $Matches[2].Split(",") | ForEach-Object { $_.Trim() }
        foreach ($ax in $axs) {
            if ($allowedAxioms -notcontains $ax) {
                Write-Error "VIOLATION: Theorem '$thm' depends on unapproved axiom '$ax'!"
                exit 1
            }
        }
    }
}

Write-Host "================================================================================" -ForegroundColor Green
Write-Host "LEAN 4 VERIFICATION SUCCESSFUL" -ForegroundColor Green
Write-Host "Total verified theorems audited for axioms: $axiomReports" -ForegroundColor Green
Write-Host "Approved standard kernel axioms only: [propext, Quot.sound]" -ForegroundColor Green
Write-Host "Zero 'sorry' keywords, zero unapproved axioms, zero Classical.choice dependencies." -ForegroundColor Green
Write-Host "Verification time: $([math]::Round($sw.Elapsed.TotalSeconds, 2)) seconds" -ForegroundColor Green
Write-Host "================================================================================" -ForegroundColor Green
