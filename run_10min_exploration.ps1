Write-Host "==========================================================" -ForegroundColor Cyan
Write-Host "  CHECKERS 8x8 HIGH-PERFORMANCE CUDA STATE SPACE EXPLORER" -ForegroundColor Cyan
Write-Host "  HARD LIMITS: 10 MINUTES WALL-CLOCK | 1% STORAGE BUDGET" -ForegroundColor Cyan
Write-Host "==========================================================" -ForegroundColor Cyan

$env:CUDA_HOME = "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5"
$env:CUDA_PATH = "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5"

python cuda\checkers_space_explorer.py --time-limit 600 --checkpoint-dir checkpoints_8x8 --max-storage-mb 100 --mode unified
