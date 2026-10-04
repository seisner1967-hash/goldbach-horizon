param([string] $Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
$ErrorActionPreference = 'Stop'
$RoundRoot = Split-Path -Parent $PSScriptRoot
$ResearchRoot = Split-Path -Parent $RoundRoot
$ManifestPath = Join-Path $RoundRoot 'previous_artifacts_sha256.json'
$Manifest = Get-Content -LiteralPath $ManifestPath -Raw | ConvertFrom-Json -AsHashtable
if ($Manifest.file_count -ne 341 -or $Manifest.sha256.Count -ne 341) { throw 'Unexpected frozen inventory size' }
$BaselineHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $ManifestPath).Hash.ToLowerInvariant()
if ($BaselineHash -ne '39210db5693d97ad22ffe54bfb3e21c238de207b7cb4f73262aae1e0d3a4f9cb') { throw 'Unexpected round10 registry hash' }
foreach ($Entry in $Manifest.sha256.GetEnumerator()) {
    $ArtifactPath = Join-Path $ResearchRoot $Entry.Key
    if (-not (Test-Path -LiteralPath $ArtifactPath -PathType Leaf)) { throw "Frozen artifact missing: $ArtifactPath" }
    $Observed = (Get-FileHash -Algorithm SHA256 -LiteralPath $ArtifactPath).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Frozen artifact changed: $ArtifactPath" }
}
$VerifyCode = @'
import sys
sys.dont_write_bytecode = True
import importlib.util, json
spec = importlib.util.spec_from_file_location('judge_round10_preservation', sys.argv[1])
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
print(json.dumps(module.verify()))
'@
$RawOutput = & $Python -c $VerifyCode (Join-Path $RoundRoot 'conservation.py') 2>&1
$VerifyExit = $LASTEXITCODE
if ($VerifyExit -ne 0) { throw "Explicit conservation helper failed (exit $VerifyExit): $RawOutput" }
$Result = ($RawOutput -join "`n") | ConvertFrom-Json -AsHashtable
if ($Result.status -ne 'PRESERVED' -or $Result.files -ne 341 -or $Result.baseline_sha256 -ne $BaselineHash) { throw 'Explicit helper returned unexpected preservation state' }
[ordered]@{
    status = 'PRESERVED'; files = 341; round9_files = $Result.round9_files
    baseline_sha256 = $BaselineHash; original_sources = $Result.original_sources
    round9_controller_sha256 = $Result.round9_controller_sha256
    explicit_round10_helper = $true; earlier_inventory_additions_checked = $true
    future_round_directories_excluded_by_parsed_number = $true
}
