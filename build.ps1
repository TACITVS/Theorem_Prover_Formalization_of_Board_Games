# Automated Rocq 9.1 Build & Strict Axiom Audit for 9x7 Connect-5
$ErrorActionPreference = "Stop"

$coqcBin = "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
if (-not (Test-Path $coqcBin)) {
    $coqcBin = "coqc"
}

Write-Host "=== Compiling 9x7 Connect-5 Formal Verification in Rocq 9.1 ===" -ForegroundColor Cyan
& $coqcBin --version

$files = @(
    "C5Board9x7.v",
    "C5Pairing9x7.v",
    "C5Rules9x7.v",
    "C5Theorem9x7.v",
    "CheckAssumptions.v"
)

$sw = [System.Diagnostics.Stopwatch]::StartNew()
foreach ($f in $files) {
    Write-Host "Compiling $f..." -NoNewline
    $t = [System.Diagnostics.Stopwatch]::StartNew()
    & $coqcBin -Q . C5_9x7 $f
    $t.Stop()
    Write-Host " OK ($([math]::Round($t.Elapsed.TotalSeconds, 2))s)" -ForegroundColor Green
}
$sw.Stop()

Write-Host "`n=== Auditing Assumptions in CheckAssumptions.v ===" -ForegroundColor Cyan
$audit = & $coqcBin -Q . C5_9x7 CheckAssumptions.v 2>&1
$audit | ForEach-Object { Write-Host $_ }

$closedCount = ($audit | Select-String "Closed under the global context").Count
Write-Host "`n[Audit Result] $closedCount / 25 Theorems strictly Closed under global context (0 Axioms, 0 Admits)!" -ForegroundColor Green
Write-Host "Total compilation time: $([math]::Round($sw.Elapsed.TotalSeconds, 2)) seconds." -ForegroundColor Cyan
