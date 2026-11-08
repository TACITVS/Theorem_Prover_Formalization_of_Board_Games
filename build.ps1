# Build and verify script for Rocq 9.1 Connect-5 formal proof
$ErrorActionPreference = "Stop"

$rocq = "C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe"
if (-not (Test-Path $rocq)) {
    $cmd = Get-Command rocq -ErrorAction SilentlyContinue
    if ($cmd) { $rocq = $cmd.Source }
    else { throw "rocq executable not found in PATH or C:\Rocq-Platform~9.1~2026.01\bin\rocq.exe" }
}

$files = @(
    "C5Game.v",
    "C5Board.v",
    "C5Principle.v",
    "C5Rules.v",
    "C5Certificate.v",
    "C5CertChecker.v",
    "CheckAssumptions.v"
)

Write-Host "=== Compiling Connect-5 (8x8) Formal Mathematical Proof in Rocq 9.1 ===" -ForegroundColor Cyan
$assumptionsOutput = @()
Push-Location $PSScriptRoot
try {
    foreach ($f in $files) {
        Write-Host "Compiling $f..." -NoNewline
        $sw = [System.Diagnostics.Stopwatch]::StartNew()
        $out = & $rocq compile -Q . C5 $f 2>&1
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
$closedMatches = ([regex]::Matches($joined, "Closed under the global context")).Count
if ($joined -match "Axioms:") {
    Write-Error "Verification failed: unexpected Axioms reported by CheckAssumptions.v!"
    exit 1
}
if ($closedMatches -ne 26) {
    Write-Error "Verification failed: expected 26 'Closed under the global context' reports, got $closedMatches"
    exit 1
}

Write-Host "`nAll 6 foundational theory files and all 26 theorems verified (" -NoNewline -ForegroundColor Cyan
Write-Host "$closedMatches/26 Closed under the global context, 0 Axioms, 0 Admits" -NoNewline -ForegroundColor Green
Write-Host ")!" -ForegroundColor Cyan

