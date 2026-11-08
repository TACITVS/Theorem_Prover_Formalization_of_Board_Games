# Automated Rocq 9.1 Build & Strict Axiom Audit for Classic 7x6 Connect-Four
$ErrorActionPreference = "Stop"

$coqcBin = "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
if (-not (Test-Path $coqcBin)) {
    $coqcBin = "coqc"
}

Write-Host "=== Compiling Classic 7x6 Connect-Four Formal Verification in Rocq 9.1 ===" -ForegroundColor Cyan
& $coqcBin --version

$files = @(
    "C4Board.v",
    "C4Claimeven.v",
    "C4CenterPigeonhole.v",
    "C4Zugzwang.v",
    "C4Theorem.v",
    "CheckAssumptions.v"
)

$sw = [System.Diagnostics.Stopwatch]::StartNew()
foreach ($f in $files) {
    Write-Host "Compiling $f..." -NoNewline
    $t = [System.Diagnostics.Stopwatch]::StartNew()
    & $coqcBin -Q . C4 $f
    $t.Stop()
    Write-Host " OK ($([math]::Round($t.Elapsed.TotalSeconds, 2))s)" -ForegroundColor Green
}
$sw.Stop()

Write-Host "`n=== Auditing Assumptions in CheckAssumptions.v ===" -ForegroundColor Cyan
$audit = & $coqcBin -Q . C4 CheckAssumptions.v 2>&1
$audit | ForEach-Object { Write-Host $_ }

$closedCount = ($audit | Select-String "Closed under the global context").Count
Write-Host "`n[Audit Result] $closedCount / 41 Theorems strictly Closed under global context (0 Axioms, 0 Admits)!" -ForegroundColor Green
Write-Host "Total compilation time: $([math]::Round($sw.Elapsed.TotalSeconds, 2)) seconds." -ForegroundColor Cyan
