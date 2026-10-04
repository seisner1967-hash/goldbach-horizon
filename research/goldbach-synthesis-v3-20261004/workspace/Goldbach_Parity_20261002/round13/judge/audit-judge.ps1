param(
    [string]$Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
)
$ErrorActionPreference = 'Stop'
& $Python -B -X utf8 (Join-Path $PSScriptRoot 'run-audit.py')
if ($LASTEXITCODE -ne 0) {
    throw 'Round13 independent frozen-input audit or fresh compilation failed; dependent steps stopped.'
}
Write-Output 'Round13 numerical receipts audited read-only and new Lean rebuilt freshly; 514 old artifacts preserved.'
Write-Output 'Score: 0'
