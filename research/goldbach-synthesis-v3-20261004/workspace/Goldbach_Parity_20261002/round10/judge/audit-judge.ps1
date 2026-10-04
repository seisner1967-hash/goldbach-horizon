param([string] $Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
$ErrorActionPreference = 'Stop'
$Before = & (Join-Path $PSScriptRoot 'verify-frozen.ps1') -Python $Python
if ($Before.status -ne 'PRESERVED') { throw 'Preservation failed before replay' }
& $Python (Join-Path $PSScriptRoot 'run-judge.py')
$JudgeExit = $LASTEXITCODE
if ($JudgeExit -ne 0) { throw "Independent round10 audit failed with exit $JudgeExit" }
$After = & (Join-Path $PSScriptRoot 'verify-frozen.ps1') -Python $Python
if ($After.status -ne 'PRESERVED') { throw 'Preservation failed after replay' }
Write-Output 'Round10 independent numerical replay and fresh Lean audit completed; previous 341 artifacts preserved.'
Write-Output 'Score: 0'
