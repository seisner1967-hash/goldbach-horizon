param(
    [string]$Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
)
$ErrorActionPreference = 'Stop'
$AuditPath = Join-Path $PSScriptRoot 'run-audit.py'
& $Python -B -X utf8 $AuditPath
if ($LASTEXITCODE -ne 0) {
    throw 'Round12 read-only Judge audit failed; dependent steps stopped.'
}
Write-Output 'Round12 frozen receipts and preservation audited without producer replay or Lean.'
Write-Output 'Score: 0'
