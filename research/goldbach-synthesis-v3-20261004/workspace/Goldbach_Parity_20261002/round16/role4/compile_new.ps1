param([Parameter(Mandatory=$true)][int]$Attempt)
$ErrorActionPreference = 'Stop'
$taskRolePath = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round16\role4'
$taskPackages = 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages'
$taskLean = 'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe'
$taskLibs = @('aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq') | ForEach-Object { Join-Path $taskPackages ($_ + '\.lake\build\lib') }
$env:LEAN_PATH = $taskLibs -join ';'
$taskSnapshot = Join-Path $taskRolePath ('attempt' + $Attempt + '.lean')
$taskLog = Join-Path $taskRolePath ('attempt' + $Attempt + '.log')
if (Test-Path -LiteralPath $taskSnapshot) { throw 'Attempt snapshot already exists' }
Copy-Item -LiteralPath (Join-Path $taskRolePath 'LeastMissingPrimeMargin.lean') -Destination $taskSnapshot
$taskStarted = [DateTime]::UtcNow.ToString('o')
Push-Location $taskRolePath
try {
  $taskOutput = & $taskLean -o LeastMissingPrimeMargin.olean LeastMissingPrimeMargin.lean 2>&1
  $taskExit = $LASTEXITCODE
} finally { Pop-Location }
$taskOutput | Set-Content -LiteralPath $taskLog -Encoding utf8
$taskReceipt = [ordered]@{ attempt=$Attempt; started_utc=$taskStarted; completed_utc=[DateTime]::UtcNow.ToString('o'); exit_code=$taskExit; source_sha256=(Get-FileHash -LiteralPath $taskSnapshot -Algorithm SHA256).Hash.ToLowerInvariant(); log_sha256=(Get-FileHash -LiteralPath $taskLog -Algorithm SHA256).Hash.ToLowerInvariant(); lean_sha256=(Get-FileHash -LiteralPath $taskLean -Algorithm SHA256).Hash.ToLowerInvariant(); command='lean.exe -o LeastMissingPrimeMargin.olean LeastMissingPrimeMargin.lean'; producer_rebuild='new_module_only'; mathlib_commit='9837ca9d65d9de6fad1ef4381750ca688774e608' }
if ($taskExit -eq 0) { $taskReceipt['olean_sha256'] = (Get-FileHash -LiteralPath (Join-Path $taskRolePath 'LeastMissingPrimeMargin.olean') -Algorithm SHA256).Hash.ToLowerInvariant() }
$taskReceipt | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath (Join-Path $taskRolePath ('attempt' + $Attempt + '_receipt.json')) -Encoding utf8
$taskOutput
exit $taskExit
