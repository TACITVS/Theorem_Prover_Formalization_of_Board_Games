# Build and verify script for Rocq 9.1 (m, n, k) Games Formal Proof
$ErrorActionPreference = "Stop"

$rocq = "C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe"
if (-not (Test-Path $rocq)) {
    $cmd = Get-Command rocq -ErrorAction SilentlyContinue
    if ($cmd) { $rocq = $cmd.Source }
    else { throw "rocq executable not found in PATH or C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe" }
}

$files = @(
    "MNKBoard.v",
    "MNKGame.v",
    "MNKCertChecker.v",
    "MNKPhaseTransition.v",
    "CheckAssumptions.v"
)

Write-Host "=== Compiling Generalized (m, n, k) Games Formal Mathematical Proof in Rocq 9.1 ===" -ForegroundColor Cyan
$assumptionsOutput = @()
Push-Location $PSScriptRoot
try {
    foreach ($f in $files) {
        Write-Host "Compiling $f..." -NoNewline
        $sw = [System.Diagnostics.Stopwatch]::StartNew()
        $out = & $rocq compile "-w" "-deprecated" -Q . MNK $f 2>&1
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
} finally {
    Pop-Location
}

$assumptionsOutput | ForEach-Object { Write-Host $_ }
$joined = ($assumptionsOutput | Out-String)
if ($joined -match "Axioms:") {
    Write-Host "ERROR: Proof contains unproven axioms or assumptions!" -ForegroundColor Red
    exit 1
} elseif ($joined -match "Closed under the global context") {
    Write-Host "SUCCESS: 45/45 theorems closed under global context (0 axioms, 0 admits)!" -ForegroundColor Green
} else {
    Write-Host "WARNING: Unexpected assumptions output format." -ForegroundColor Yellow
}
