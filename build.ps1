# Build and verify script for Rocq 9.1 Nine Men's Morris formal proof
$ErrorActionPreference = "Stop"

$rocq = "C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe"
if (-not (Test-Path $rocq)) {
    $cmd = Get-Command rocq -ErrorAction SilentlyContinue
    if ($cmd) { $rocq = $cmd.Source }
    else { throw "rocq executable not found in PATH or C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe" }
}

$files = @(
    "NMMGraph.v",
    "NMMGame.v",
    "NMMInvariants.v",
    "NMMBitboard.v",
    "NMMStrategy.v",
    "NMMRetrograde.v",
    "NMMCertChecker.v",
    "CheckAssumptions.v"
)

Write-Host "=== Compiling Nine Men's Morris Formal Mathematical Proof in Rocq 9.1 ===" -ForegroundColor Cyan
$assumptionsOutput = @()
foreach ($f in $files) {
    Write-Host "Compiling $f..." -NoNewline
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    $out = & $rocq compile -Q . NMM $f 2>&1
    if ($LASTEXITCODE -ne 0) {
        Write-Host " FAILED!" -ForegroundColor Red
        $out | ForEach-Object { Write-Host $_ }
        exit $LASTEXITCODE
    }
    $sw.Stop()
    Write-Host " OK ($([math]::Round($sw.Elapsed.TotalSeconds, 2))s)" -ForegroundColor Green
    if ($f -eq "CheckAssumptions.v") {
        $assumptionsOutput = $out
    }
}

$assumptionsOutput | ForEach-Object { Write-Host $_ }
$joined = ($assumptionsOutput | Out-String)
if ($joined -match "Axioms:") {
    Write-Host "ERROR: Proof relies on unproven axioms!" -ForegroundColor Red
    exit 1
} else {
    Write-Host "ALL THEOREMS FULLY VERIFIED (0 AXIOMS / CLOSED UNDER GLOBAL CONTEXT)" -ForegroundColor Green
}
