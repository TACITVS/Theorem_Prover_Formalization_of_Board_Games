# build.ps1: Build script for Dots and Boxes Formal Proof in Rocq 9.1
$ErrorActionPreference = "Stop"

$rocq_bin = "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
if (-not (Test-Path $rocq_bin)) {
    Write-Error "Rocq compiler not found at $rocq_bin"
    exit 1
}

Write-Host "=== Compiling Dots and Boxes Formal Mathematical Proof in Rocq 9.1 ===" -ForegroundColor Cyan

$files = @(
    "DABUniversal.v",
    "DAB16Graph.v",
    "DABGame.v",
    "DABCheckAssumptions.v"
)

foreach ($f in $files) {
    Write-Host "Compiling $f..." -NoNewline
    $output = & $rocq_bin -Q . DAB $f 2>&1
    if ($LASTEXITCODE -ne 0) {
        Write-Host " FAILED!" -ForegroundColor Red
        Write-Host $output
        exit 1
    }
    Write-Host " OK" -ForegroundColor Green
    if ($f -eq "DABCheckAssumptions.v") {
        $closed_count = ($output | Select-String "Closed under the global context").Count
        $expected_count = (Select-String -Path "DABCheckAssumptions.v" -Pattern "^Print Assumptions").Count
        Write-Host "Closed under the global context ($closed_count/$expected_count theorems audited)" -ForegroundColor Yellow
        if ($closed_count -ne $expected_count) {
            Write-Error "Expected $expected_count closed theorems, got $closed_count"
            exit 1
        }
    }
}

Write-Host "ALL THEOREMS FULLY VERIFIED (0 AXIOMS / CLOSED UNDER GLOBAL CONTEXT)" -ForegroundColor Green
