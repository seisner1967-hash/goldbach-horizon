$ErrorActionPreference = 'Stop'
$basePath = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$outputPath = [IO.Path]::GetFullPath($PSScriptRoot)
$utf8Encoding = New-Object Text.UTF8Encoding($false)

function WriteExclusiveJson($name, $value) {
    $path = Join-Path $outputPath $name
    $bytes = $utf8Encoding.GetBytes(($value | ConvertTo-Json -Depth 15) + "`n")
    $stream = [IO.File]::Open($path, [IO.FileMode]::CreateNew, [IO.FileAccess]::Write)
    try { $stream.Write($bytes, 0, $bytes.Length) } finally { $stream.Dispose() }
}

# Metadata only: copy stored labels and exit codes; never recompute mathematical values.
$composite = Get-Content -LiteralPath (Join-Path $basePath 'round20/composite.json') -Raw | ConvertFrom-Json
$configLabels = @()
foreach ($entry in $composite.aggregate_affine_expressions_and_certificates.PSObject.Properties) {
    $configLabels += [ordered]@{
        config = $entry.Name
        Gamma0_theta_stored_label = $entry.Value.Gamma0_theta.whole_box_certificate.sign
        Gamma0_raw_stored_label = $entry.Value.Gamma0_raw.whole_box_certificate.sign
        principal_minus_M0_stored_label = $entry.Value.new_principal_minus_M0.whole_box_certificate.sign
        slack_stored_label = $entry.Value.slack.whole_box_certificate.sign
        Ctail_stored_label = $entry.Value.Ctail.whole_box_certificate.sign
        RAP_stored_label = $entry.Value.RAP.whole_box_certificate.sign
    }
}
$role3 = Get-Content -LiteralPath (Join-Path $basePath 'round20/role3/build_receipt.json') -Raw | ConvertFrom-Json
$role3Attempts = @($role3.attempts | Where-Object { $_.attempt -le 7 } | ForEach-Object {
    [ordered]@{attempt=$_.attempt; module=$_.module; actual_exit_code=$_.actual_exit_code;
        status=$_.status; started_utc=$_.started_utc; finished_utc=$_.finished_utc;
        source_sha256=$_.source_sha256; log_path=$_.log_path; log_sha256=$_.log_sha256}
})
$budget = Get-Content -LiteralPath (Join-Path $basePath 'round20/role4/source_budget_build_receipt.json') -Raw | ConvertFrom-Json
$budgetAttempts = @($budget.attempts | ForEach-Object {
    [ordered]@{attempt=$_.attempt; actual_exit_code=$_.exit_code; credited_pass=$_.credited_pass;
        started_utc=$_.started_utc; finished_utc=$_.finished_utc; source_sha256=$_.source_sha256;
        log_sha256=$_.log_sha256; post_all_unchanged=$_.post_integrity.all_unchanged;
        olean_sha256=$_.olean_sha256}
})
WriteExclusiveJson 'stored_projection.json' ([ordered]@{
    created_utc=[DateTime]::UtcNow.ToString('o'); round=20; scope='READ_ONLY_STORED_METADATA_AND_LABELS';
    mathematical_recomputation=$false; new_numeric_invocations=0; new_Lean_invocations=0;
    role3_cutoff_attempt=7; role3_attempts=$role3Attempts;
    source_budget_attempts=$budgetAttempts; composite_status=$composite.status;
    composite_parameters=$composite.parameters; source_guards=$composite.source_guards;
    composite_config_labels=$configLabels; composite_unpaid=$composite.unpaid;
    victory=$false
})

$relativeInputs = @(
    'round20/agent1_switched_composite.md','round20/agent2_friable.md',
    'round20/role6/final.md','round20/role6_composite/final.md','round20/role6_friable/final.md',
    'round20/composite.json','round20/friable.json',
    'round20/role4/FriableSourceBudget.lean','round20/role4/FriableDemandAggregation.lean',
    'round20/role4/FriablePhysicalPayment.lean','round20/role4/compiler_failures.md',
    'round20/role4/source_budget_build_receipt.json',
    'round20/role4/source_budget_attempt01.log','round20/role4/source_budget_attempt02.log',
    'round20/role4/extension_attempt01.log','round20/role4/extension_attempt02.log',
    'round20/role4/aggregation_attempt01.log','round20/role4/aggregation_attempt02.log',
    'round20/role4_geometry/FriableSourceGeometry.lean',
    'round20/role4_geometry/geometry_actual_failures.md','round20/role4_geometry/geometry_build_receipt.json',
    'round20/role4_geometry/attempt01.log','round20/role4_geometry/attempt02.log',
    'round20/role3/attempt01_analysis.json','round20/role3/attempt03_analysis.json','round20/role3/attempt05_analysis.json',
    'round20/role3/attempt01_OddBonferroniArithmetic.log','round20/role3/attempt02_OddBonferroniArithmetic.log',
    'round20/role3/attempt03_LeastFactorComposite.log','round20/role3/attempt04_LeastFactorComposite.log',
    'round20/role3/attempt05_SwitchedSelbergWeight.log','round20/role3/attempt06_SwitchedSelbergWeight.log',
    'round20/role3/attempt07_PhysicalCompositeSubtraction.log',
    'round20/role3/attempt07_PhysicalCompositeSubtraction_receipt.json'
)
for ($i=1; $i -le 16; $i++) { $relativeInputs += ('round20/role4/attempt{0:D2}.log' -f $i) }
$bindings = [ordered]@{}
foreach ($relativePath in $relativeInputs) {
    $inputPath = Join-Path $basePath $relativePath
    $bindings[$relativePath] = [ordered]@{
        sha256=(Get-FileHash -LiteralPath $inputPath -Algorithm SHA256).Hash.ToLower();
        length=(Get-Item -LiteralPath $inputPath).Length
    }
}
WriteExclusiveJson 'input_manifest.json' ([ordered]@{
    created_utc=[DateTime]::UtcNow.ToString('o'); scope='HASH_OF_READ_SOURCE_ORIGINAL_LOGS_AND_STORED_RESULTS_ONLY';
    compiler_cutoff_role3_attempt=7; no_claim_on_later_attempts=$true;
    originals_not_modified=$true; mathematical_recomputation=$false; bindings=$bindings
})
Write-Output 'Feedback metadata captured exclusively; no math, Lean, Judge, producer or historical replay.'
