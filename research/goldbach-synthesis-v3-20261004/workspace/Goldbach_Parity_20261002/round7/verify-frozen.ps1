$ErrorActionPreference = 'Stop'
$ResearchRoot = Split-Path -Parent $PSScriptRoot
$ManifestPath = Join-Path $PSScriptRoot 'previous_artifacts_sha256.json'
$Manifest = Get-Content -LiteralPath $ManifestPath -Raw | ConvertFrom-Json -AsHashtable
if ($Manifest.file_count -ne 190 -or $Manifest.sha256.Count -ne 190) {
    throw 'Unexpected frozen-artifact manifest size'
}
foreach ($Entry in $Manifest.sha256.GetEnumerator()) {
    $ArtifactPath = Join-Path $ResearchRoot $Entry.Key
    if (-not (Test-Path -LiteralPath $ArtifactPath -PathType Leaf)) {
        throw "Frozen artifact missing: $ArtifactPath"
    }
    $Observed = (Get-FileHash -Algorithm SHA256 -LiteralPath $ArtifactPath).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Frozen artifact changed: $ArtifactPath" }
}
[ordered]@{
    status = 'PRESERVED'; files = 190
    manifest = $ManifestPath
    baseline_sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $ManifestPath).Hash.ToLowerInvariant()
}
