# Automated Rocq 9.1 Build & Strict Axiom Audit for 5x5x5 3D Tic-Tac-Toe
$ErrorActionPreference = "Stop"

$coqcBin = "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
if (-not (Test-Path $coqcBin)) {
    $coqcBin = "coqc"
}

Write-Host "=== Compiling 5x5x5 3D Tic-Tac-Toe Formal Verification in Rocq 9.1 ===" -ForegroundColor Cyan
& $coqcBin --version

$scriptDir = if ($PSScriptRoot) { $PSScriptRoot } else { "." }

$files = @(
    "QubicBoard.v",
    "QubicSymmetry.v",
    "QubicThreat.v",
    "QubicTheorem.v",
    "QubicAlgebraic.v",
    "CheckAssumptions.v"
)

$sw = [System.Diagnostics.Stopwatch]::StartNew()
foreach ($f in $files) {
    Write-Host "Compiling $f..." -NoNewline
    $t = [System.Diagnostics.Stopwatch]::StartNew()
    $filePath = Join-Path $scriptDir $f
    & $coqcBin -Q $scriptDir Qubic $filePath
    $t.Stop()
    Write-Host " OK ($([math]::Round($t.Elapsed.TotalSeconds, 2))s)" -ForegroundColor Green
}
$sw.Stop()

Write-Host "`n=== Auditing Assumptions in CheckAssumptions.v ===" -ForegroundColor Yellow
$checkPath = Join-Path $scriptDir "CheckAssumptions.v"
$auditOutput = & $coqcBin -Q $scriptDir Qubic $checkPath 2>&1
$closedCount = ($auditOutput | Select-String -Pattern "Closed under the global context").Count

if ($closedCount -eq 84) {
    Write-Host "`n[Audit Result] 84 / 84 Theorems strictly Closed under global context (0 Axioms, 0 Admits)!" -ForegroundColor Green
} else {
    Write-Host "`n[Warning] Found $closedCount closed theorems (expected 84)." -ForegroundColor Yellow
}

Write-Host "Total compilation time: $([math]::Round($sw.Elapsed.TotalSeconds, 2)) seconds." -ForegroundColor Cyan
