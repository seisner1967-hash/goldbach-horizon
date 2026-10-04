param([string] $Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
$ErrorActionPreference = 'Stop'
$RoundRoot = Split-Path -Parent $PSScriptRoot
$ResearchRoot = Split-Path -Parent $RoundRoot
$ManifestPath = Join-Path $RoundRoot 'previous_artifacts_sha256.json'
$Manifest = Get-Content -LiteralPath $ManifestPath -Raw | ConvertFrom-Json -AsHashtable
if ($Manifest.file_count -ne 307 -or $Manifest.sha256.Count -ne 307) { throw 'Unexpected earlier-artifact manifest size' }
$BaselineHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $ManifestPath).Hash.ToLowerInvariant()
if ($BaselineHash -ne '4a637dc44cd1fe2d7ae5850b4999ab052c069084143d69aa52484f66e250fe0f') {
    throw 'Earlier-artifact baseline differs from the announced round-9 registry'
}
foreach ($Entry in $Manifest.sha256.GetEnumerator()) {
    $ArtifactPath = Join-Path $ResearchRoot $Entry.Key
    if (-not (Test-Path -LiteralPath $ArtifactPath -PathType Leaf)) { throw "Frozen artifact missing: $ArtifactPath" }
    $Observed = (Get-FileHash -Algorithm SHA256 -LiteralPath $ArtifactPath).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Frozen artifact changed: $ArtifactPath" }
}
# The explicit round-9 helper additionally rejects added earlier files.
$VerifyCode = @'
import sys
sys.dont_write_bytecode = True
import importlib.util, json
spec = importlib.util.spec_from_file_location('judge_round9_preservation', sys.argv[1])
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
print(json.dumps(module.verify()))
'@
$RawOutput = & $Python -c $VerifyCode (Join-Path $RoundRoot 'conservation.py') 2>&1
$VerifyExit = $LASTEXITCODE
if ($VerifyExit -ne 0) { throw "Explicit conservation helper failed (exit $VerifyExit): $RawOutput" }
$Result = ($RawOutput -join "`n") | ConvertFrom-Json -AsHashtable
if ($Result.status -ne 'PRESERVED' -or $Result.files -ne 307 -or $Result.baseline_sha256 -ne $BaselineHash) {
    throw 'Explicit conservation helper selected an unexpected registry'
}
[ordered]@{
    status = 'PRESERVED'; files = 307; round8_files = $Result.round8_files
    manifest = $ManifestPath; baseline_sha256 = $BaselineHash
    explicit_round9_helper = $true; earlier_inventory_additions_checked = $true
}
