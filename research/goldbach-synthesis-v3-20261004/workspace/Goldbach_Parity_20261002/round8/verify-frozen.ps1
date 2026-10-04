$ErrorActionPreference = 'Stop'
$ResearchRoot = Split-Path -Parent $PSScriptRoot
$ManifestPath = Join-Path $PSScriptRoot 'previous_artifacts_sha256.json'
$Manifest = Get-Content -LiteralPath $ManifestPath -Raw | ConvertFrom-Json -AsHashtable
if ($Manifest.file_count -ne 227 -or $Manifest.sha256.Count -ne 227) { throw 'Unexpected frozen-artifact manifest size' }
$BaselineHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $ManifestPath).Hash.ToLowerInvariant()
if ($BaselineHash -ne 'b973b6ea8ce1fdef2a704e1e0bcc977ee7ac5b140e71d17cc3d90c165317243a') {
    throw 'Frozen-artifact baseline differs from the announced round-8 registry'
}
foreach ($Entry in $Manifest.sha256.GetEnumerator()) {
    $ArtifactPath = Join-Path $ResearchRoot $Entry.Key
    if (-not (Test-Path -LiteralPath $ArtifactPath -PathType Leaf)) { throw "Frozen artifact missing: $ArtifactPath" }
    $Observed = (Get-FileHash -Algorithm SHA256 -LiteralPath $ArtifactPath).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Frozen artifact changed: $ArtifactPath" }
}
[ordered]@{ status = 'PRESERVED'; files = 227; manifest = $ManifestPath; baseline_sha256 = $BaselineHash }
