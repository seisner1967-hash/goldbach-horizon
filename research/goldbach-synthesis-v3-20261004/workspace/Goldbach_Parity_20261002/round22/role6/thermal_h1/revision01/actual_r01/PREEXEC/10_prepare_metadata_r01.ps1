# New revision metadata only. No Python/Lean/probe/import or numerical run.
$ErrorActionPreference='Stop'
$revisionDirectory=$PSScriptRoot
$originalDirectory=Split-Path $revisionDirectory -Parent
$researchBase=Split-Path (Split-Path (Split-Path $originalDirectory -Parent) -Parent) -Parent
$runtimePath='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$rootGatePath=Join-Path $researchBase '.arbor\sessions\parity\.coordinator\messages\round22_thermal_component_r01_authorization.json'
$manifestPath=Join-Path $revisionDirectory 'prepared_manifest_r01.json'
$preparationPath=Join-Path $revisionDirectory 'preparation_r01.json'
foreach ($path in @($manifestPath,$preparationPath,(Join-Path $revisionDirectory 'actual_r01'),$rootGatePath)) {
    if (Test-Path -LiteralPath $path) { throw 'Revision output/attempt/gate already exists; no overwrite.' }
}
function Binding([string]$path,[string]$kind) {
    $resolved=(Resolve-Path -LiteralPath $path).Path
    return [ordered]@{path=$resolved;sha256=(Get-FileHash -LiteralPath $resolved -Algorithm SHA256).Hash.ToLowerInvariant();bytes=(Get-Item -LiteralPath $resolved).Length;kind=$kind}
}
function CreateJson([string]$path,$data) {
    $bytes=[System.Text.UTF8Encoding]::new($false).GetBytes(($data | ConvertTo-Json -Depth 30)+"`n")
    $stream=[System.IO.File]::Open($path,[System.IO.FileMode]::CreateNew,[System.IO.FileAccess]::Write)
    try { $stream.Write($bytes,0,$bytes.Length) } finally { $stream.Dispose() }
}
$originalPrepPath=Join-Path $originalDirectory 'component_preparation22.json'
if ((Get-FileHash -LiteralPath $originalPrepPath -Algorithm SHA256).Hash.ToLowerInvariant() -ne 'b417be88862b3adb9636d90214243c943c4d8e054856dff3e93baf9be1280a5e') { throw 'Original preparation changed.' }
$originalPrep=Get-Content -LiteralPath $originalPrepPath -Raw | ConvertFrom-Json
foreach ($expected in $originalPrep.bindings) {
    $binding=Binding $expected.path 'READONLY_ORIGINAL_BINDING_SHA_ONLY'
    if (($binding.sha256 -ne $expected.sha256) -or ($binding.bytes -ne $expected.bytes)) { throw 'Original frozen25bindings changed.' }
}
$bindings=@()
foreach ($name in @('dyadic_r01.py','analytic_r01.py','kernel_r01.py','reference_r01.py','producer_r01.py','checker_r01.py',
    'run_once_r01.py','contract_r01.json','paper_r01.md','source_scope_r01.json','prepare_metadata_r01.ps1')) {
    $bindings += Binding (Join-Path $revisionDirectory $name) 'NEW_REVISION01_SOURCE_OR_METADATA'
}
foreach ($name in @('thermal_dyadic22.py','thermal_analytic22.py','thermal_kernel22.py','thermal_reference22.py',
    'component_bank22.py','component_checker22.py','run_component_once22.py')) {
    $bindings += Binding (Join-Path $originalDirectory $name) 'READONLY_SOURCE_ADAPTATION_PROVENANCE_NEVER_IMPORTED'
}
foreach ($entry in @(
    @('component_failure_receipt22.json','3f4ca3b9c9f03ab4a08c6f4922252a78f91ca768ceeb9aa92f42f1b755eda027'),
    @('component_failure22.md','2d5fbd13ef165bc3f21d33f63f1db824a3d59526072ab7fac054bdcfd3aaf0a7'))) {
    $binding=Binding (Join-Path $originalDirectory $entry[0]) 'READONLY_FAILURE_HISTORY_METADATA_NOT_A_NUMERIC_ORACLE'
    if ($binding.sha256 -ne $entry[1]) { throw 'Failure closure changed.' }
    $bindings += $binding
}
$bindings += Binding $originalPrepPath 'READONLY_ORIGINAL_PREPARATION_HISTORY'
foreach ($expected in $originalPrep.bindings) {
    if ($expected.kind -in @('READONLY_FROZEN_PRECRITIQUE','READONLY_FROZEN_PRECRITIQUE_MANIFEST','READONLY_FROZEN_ROLE1_MANIFEST','READONLY_SELECTED_THERMAL_CONTEXT')) {
        $bindings += Binding $expected.path 'READONLY_SELECTED_THERMAL_PAPER_OR_PRECRITIQUE'
    }
}
foreach ($entry in @(
    @('.arbor\sessions\parity\experiments\15.3\executor_prompt.md','0ac337ada01aed929b00f2ff94a7f740409df18350d62433a58edd74fe371958'),
    @('round22\USER_DIRECTIVE.md','c5aa8310ad54c57726339a8e99057f158254eb6d113ac3aeb71ddc9627f23947'),
    @('round22\PROBE_BLOCK.md','a896c9d0fa4114845b20c3023246dcb987463923df798cac2c537c70cfb73fc3'))) {
    $binding=Binding (Join-Path $researchBase $entry[0]) 'READONLY_SELECTION_DIRECTIVE_PROBE'
    if ($binding.sha256 -ne $entry[1]) { throw 'Selection/directive/probe changed.' }
    $bindings += $binding
}
$runtimeBinding=Binding $runtimePath 'READONLY_RUNTIME_BYTES_NO_PROBE'
if ($runtimeBinding.sha256 -ne '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c') { throw 'Runtime bytes changed.' }
$bindings += $runtimeBinding
$timeUtc=[DateTime]::UtcNow.ToString('o')
$manifest=[ordered]@{schema='ROUND22_THERMAL_COMPONENT_REVISION01_PREPARED_MANIFEST';time_utc=$timeUtc;
    status='PREPARED_SOURCE_ONLY_NOT_EXECUTED';actor='ROLE6';bank_id='THERMAL_COMPONENT_R01_AUX22';scope='THERMAL_COMPONENT_R01_AUX_ONLY';
    bindings=$bindings;binding_count=$bindings.Count;original25bindings_verified=$true;original_attempt_closed=$true;
    source_text_adaptation_not_old_result_replay=$true;new_math_invocations=0;new_Lean_invocations=0;runtime_probes=0;H1_claim=$false;WIN=$false}
CreateJson $manifestPath $manifest
$bindings += Binding $manifestPath 'NEW_REVISION01_PREPARED_MANIFEST'
$prep=[ordered]@{schema='ROUND22_THERMAL_COMPONENT_REVISION01_PREPARATION';time_utc=$timeUtc;
    status='PREPARED_SOURCE_ONLY_NOT_EXECUTED';actor='ROLE6';bank_id='THERMAL_COMPONENT_R01_AUX22';scope='THERMAL_COMPONENT_R01_AUX_ONLY';
    bindings=$bindings;binding_count=$bindings.Count;runtime_path=$runtimePath;runtime_flags=@('-B','-X','utf8');
    captures_before_START=($bindings.Count+2);root_gate_path=$rootGatePath;future_actual_directory=(Join-Path $revisionDirectory 'actual_r01');
    expected_case_count=46;expected_Gamma_phase_cases=15;expected_reference_cells_each=2240;expected_reference_cells_total=33600;
    expected_mutation_count=19;expected_sqrt_certificates=15;expected_regression_exponents=@(512,768);
    sole_attempt_consumed=$false;math_invocations=0;Lean_invocations=0;old_producer_invocations=0;old_partial_values_as_oracle=$false;
    cost_measured=$false;runtime_integer_string_limit_modified=$false;H1_claim=$false;WIN=$false;
    command_template=@($runtimePath,'-B','-X','utf8',(Join-Path $revisionDirectory 'run_once_r01.py'),
        '--root-authorization','EXACT_DISTINCT_R01_GATE','--root-authorization-sha256','EXACT_R01_GATE_SHA')}
CreateJson $preparationPath $prep
[ordered]@{metadata_only=$true;time_utc=$timeUtc;binding_count=$bindings.Count;captures_before_START=($bindings.Count+2);
    prepared_manifest_sha256=(Get-FileHash -LiteralPath $manifestPath -Algorithm SHA256).Hash.ToLowerInvariant();
    preparation_sha256=(Get-FileHash -LiteralPath $preparationPath -Algorithm SHA256).Hash.ToLowerInvariant();
    original25bindings_intact=$true;new_math_invocations=0;new_Lean_invocations=0;gate_created=$false;actual_directory_created=$false;
    bindings=$bindings} | ConvertTo-Json -Depth 30
