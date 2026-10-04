$ErrorActionPreference = 'Stop'
$basePath = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$utf8Encoding = New-Object Text.UTF8Encoding($false)
$inputManifestPath = Join-Path $PSScriptRoot 'input_manifest.json'
$inputManifest = Get-Content -LiteralPath $inputManifestPath -Raw | ConvertFrom-Json
$bindings = [ordered]@{}
foreach ($entry in $inputManifest.bindings.PSObject.Properties) {
    $path = Join-Path $basePath $entry.Name
    $sha = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLower()
    if ($sha -ne $entry.Value.sha256) { throw ('Observed input changed before feedback freeze: ' + $entry.Name) }
    $bindings[$entry.Name] = $sha
}
$lateObservation = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'late_role3_observation.json') -Raw | ConvertFrom-Json
foreach ($entry in $lateObservation.input_bindings_sha256.PSObject.Properties) {
    $sha = (Get-FileHash -LiteralPath (Join-Path $basePath $entry.Name) -Algorithm SHA256).Hash.ToLower()
    if ($sha -ne $entry.Value) { throw ('Late observed input changed: ' + $entry.Name) }
    $bindings[$entry.Name] = $sha
}
$ownedFiles = @(
    'round20/ideation_failure_feedback20_final.md',
    'round20/role12_feedback/input_manifest.json',
    'round20/role12_feedback/stored_projection.json',
    'round20/role12_feedback/capture_readonly_metadata.ps1',
    'round20/role12_feedback/finalize_readonly_feedback.ps1',
    'round20/role12_feedback/late_role3_observation.json',
    'round20/role12_feedback/capture_late_role3_metadata.ps1'
)
foreach ($rel in $ownedFiles) {
    $bindings[$rel] = (Get-FileHash -LiteralPath (Join-Path $basePath $rel) -Algorithm SHA256).Hash.ToLower()
}
function WriteExclusiveJson($name, $value) {
    $path = Join-Path $PSScriptRoot $name
    $bytes = $utf8Encoding.GetBytes(($value | ConvertTo-Json -Depth 12) + "`n")
    $stream = [IO.File]::Open($path, [IO.FileMode]::CreateNew, [IO.FileAccess]::Write)
    try { $stream.Write($bytes, 0, $bytes.Length) } finally { $stream.Dispose() }
}
WriteExclusiveJson 'final_manifest.json' ([ordered]@{
    round=20; role='CONCEPTUAL_FAILURE_FEEDBACK_FOR_IDEATION_ROLES_1_2';
    created_utc=[DateTime]::UtcNow.ToString('o'); bindings=$bindings;
    binding_count=$bindings.Count; observed_inputs_verified_unchanged=$true;
    metadata_only=$true; new_mathematical_claim=$false; victory=$false
})
$finalManifestSha = (Get-FileHash -LiteralPath (Join-Path $PSScriptRoot 'final_manifest.json') -Algorithm SHA256).Hash.ToLower()
WriteExclusiveJson 'final_receipt.json' ([ordered]@{
    round=20; status='FINAL_READ_ONLY_CONCEPTUAL_FEEDBACK_NO_WIN';
    frozen_utc=[DateTime]::UtcNow.ToString('o'); role3_cutoff_attempt=14;
    role3_observed_real_passes=6; role3_observed_real_technical_failures=8;
    role4_including_source_geometry_observed_author_modules=10;
    scope='SOURCE_BUDGET_PARTIAL_AND_ACTUAL_TECHNICAL_FAILURES_THROUGH_ROLE3_ATTEMPT14';
    reviewed_input_count=(@($inputManifest.bindings.PSObject.Properties).Count + @($lateObservation.input_bindings_sha256.PSObject.Properties).Count);
    final_binding_count=$bindings.Count; final_manifest_sha256=$finalManifestSha;
    report_sha256=$bindings['round20/ideation_failure_feedback20_final.md'];
    stored_projection_sha256=$bindings['round20/role12_feedback/stored_projection.json'];
    input_manifest_sha256=$bindings['round20/role12_feedback/input_manifest.json'];
    unchanged_observed_inputs=$true; own_new_Python_math_invocations=0;
    own_new_Lean_invocations=0; own_Judge_invocations=0; old_producer_replays=0;
    idea_tree_mutations=0; new_theorems=0; score_assigned=$false; victory=$false
})
Write-Output ('Frozen feedback metadata: ' + $bindings.Count + ' bindings; 0 changed inputs; no mathematical execution.')
