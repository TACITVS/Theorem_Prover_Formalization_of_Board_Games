# run_cuda_verification.ps1 - Launch high-performance CUDA Bitboard solver on RTX 4060
$ErrorActionPreference = "Stop"

$env:CUDA_HOME = "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5"
$env:CUDA_PATH = "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5"

Write-Host "==========================================================" -ForegroundColor Cyan
Write-Host "  LAUNCHING CUDA CORE BITBOARD ENGINE ON NVIDIA RTX 4060" -ForegroundColor Cyan
Write-Host "==========================================================" -ForegroundColor Cyan

python cuda/checkers_cuda_solver.py
if ($LASTEXITCODE -ne 0) {
    Write-Error "CUDA verification failed with exit code $LASTEXITCODE"
}
