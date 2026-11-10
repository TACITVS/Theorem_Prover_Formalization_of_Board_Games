foreach ($line in Get-Content positions_cert.txt) {
  $p = $line -split ' '
  $tag = "game$($p[0])@$($p[1])"
  & .\hybrid.exe --seeds 22 --threads 22 --seconds 60 --white $p[2] --black $p[3] --ckdir "hybrid_c_$tag" --tag $tag | Select-String 'hybrid.c|DONE|INTERRUPTED'
}
