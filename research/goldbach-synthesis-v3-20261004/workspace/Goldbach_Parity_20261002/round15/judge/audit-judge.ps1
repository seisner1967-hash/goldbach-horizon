param([string]$Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
$ErrorActionPreference = 'Stop'
& $Python -B (Join-Path $PSScriptRoot 'run-audit.py')
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
Write-Output 'Score: 0'
