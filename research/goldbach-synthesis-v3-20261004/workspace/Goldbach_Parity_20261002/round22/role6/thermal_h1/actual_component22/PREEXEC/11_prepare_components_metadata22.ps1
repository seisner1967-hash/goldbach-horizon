# Metadata only: byte reads/SHA256/new manifest and preparation writes.
# Never starts Python, imports an evaluator, probes APIs, compiles or computes
# any mathematical expression from the producers. Execute at most once.
$ErrorActionPreference = 'Stop'
$componentDirectory = $PSScriptRoot
$researchBase = Split-Path (Split-Path (Split-Path $componentDirectory -Parent) -Parent) -Parent
$runtimePath = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$expectedRuntimeSha = '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
$rootGatePath = Join-Path $researchBase '.arbor\sessions\parity\.coordinator\messages\round22_thermal_component_authorization.json'
$manifestPath = Join-Path $componentDirectory 'component_prepared_manifest22.json'
$preparationPath = Join-Path $componentDirectory 'component_preparation22.json'
$actualPath = Join-Path $componentDirectory 'actual_component22'
if ((Test-Path -LiteralPath $manifestPath) -or (Test-Path -LiteralPath $preparationPath) -or (Test-Path -LiteralPath $actualPath)) {
    throw 'Preparation output or actual attempt already exists; metadata builder will not overwrite.'
}
if ((Test-Path -LiteralPath $rootGatePath)) { throw 'An unexpected gate already exists before this new preparation.' }
function Binding([string]$sourcePath, [string]$kind) {
    $resolvedPath = (Resolve-Path -LiteralPath $sourcePath).Path
    $item = Get-Item -LiteralPath $resolvedPath
    return [ordered]@{path=$resolvedPath;sha256=(Get-FileHash -LiteralPath $resolvedPath -Algorithm SHA256).Hash.ToLowerInvariant();bytes=$item.Length;kind=$kind}
}
function CreateJson([string]$path, $data) {
    $content = ($data | ConvertTo-Json -Depth 30) + "`n"
    $encoding = [System.Text.UTF8Encoding]::new($false)
    $stream = [System.IO.File]::Open($path, [System.IO.FileMode]::CreateNew, [System.IO.FileAccess]::Write)
    try { $bytes = $encoding.GetBytes($content); $stream.Write($bytes,0,$bytes.Length) }
    finally { $stream.Dispose() }
}
$sourceNames = @('thermal_dyadic22.py','thermal_analytic22.py','thermal_kernel22.py','thermal_reference22.py',
    'component_bank22.py','component_checker22.py','component_contract22.json','component_paper22.md',
    'run_component_once22.py','thermal_contract22.json','component_source_scope22.json','prepare_components_metadata22.ps1')
$bindings = @()
foreach ($name in $sourceNames) { $bindings += Binding (Join-Path $componentDirectory $name) 'NEW_COMPONENT_SOURCE_OR_PAPER' }
$paperDirectory = Join-Path $researchBase 'round22\role6\contour_precritique22'
$paperManifest = Join-Path $paperDirectory 'paper_manifest22.json'
if ((Get-FileHash -LiteralPath $paperManifest -Algorithm SHA256).Hash.ToLowerInvariant() -ne 'fe767a6228af36575130dfb4f618352aa50732827d87862eca1316cefd709611') { throw 'Frozen precritique manifest changed.' }
$paperData = Get-Content -LiteralPath $paperManifest -Raw | ConvertFrom-Json
foreach ($artifact in $paperData.artifacts) {
    $binding = Binding $artifact.path 'READONLY_FROZEN_PRECRITIQUE'
    if (($binding.sha256 -ne $artifact.sha256) -or ($binding.bytes -ne $artifact.bytes)) { throw 'Frozen precritique bytes changed.' }
    $bindings += $binding
}
$bindings += Binding $paperManifest 'READONLY_FROZEN_PRECRITIQUE_MANIFEST'
$role1Directory = Join-Path $researchBase 'round22\role1_bridge'
$role1Manifest = Join-Path $role1Directory 'paper_manifest22.json'
if ((Get-FileHash -LiteralPath $role1Manifest -Algorithm SHA256).Hash.ToLowerInvariant() -ne '812bad4eb69d612208eae8380d8bdc1dd8ab4fb2605d39eaa790f0479f2b37e3') { throw 'Frozen ROLE1 manifest changed.' }
$role1Data = Get-Content -LiteralPath $role1Manifest -Raw | ConvertFrom-Json
$bindings += Binding $role1Manifest 'READONLY_FROZEN_ROLE1_MANIFEST'
foreach ($name in @('contour_formula22.md','numeric_precontract22.md')) {
    $sourcePath = Join-Path $role1Directory $name
    $expected = @($role1Data.artifacts | Where-Object { $_.path -eq $sourcePath })
    if ($expected.Count -ne 1) { throw 'ROLE1 expected binding missing.' }
    $binding = Binding $sourcePath 'READONLY_SELECTED_THERMAL_CONTEXT'
    if (($binding.sha256 -ne $expected[0].sha256) -or ($binding.bytes -ne $expected[0].bytes)) { throw 'Frozen ROLE1 context bytes changed.' }
    $bindings += $binding
}
foreach ($entry in @(
    @('.arbor\sessions\parity\experiments\15.3\executor_prompt.md','0ac337ada01aed929b00f2ff94a7f740409df18350d62433a58edd74fe371958'),
    @('round22\USER_DIRECTIVE.md','c5aa8310ad54c57726339a8e99057f158254eb6d113ac3aeb71ddc9627f23947'),
    @('round22\PROBE_BLOCK.md','a896c9d0fa4114845b20c3023246dcb987463923df798cac2c537c70cfb73fc3'),
    @('round22\role6\gamma_h2\dyadic_gamma22.py','01c1eb04ad4f0559b181b91c5fb300654d99ee8c16ed0b1d901e05a7604c64b6'))) {
    $binding = Binding (Join-Path $researchBase $entry[0]) 'READONLY_SELECTION_DIRECTIVE_OR_ARITHMETIC_SOURCE_PROVENANCE'
    if ($binding.sha256 -ne $entry[1]) { throw 'Readonly input SHA differs from expected.' }
    $bindings += $binding
}
$runtimeBinding = Binding $runtimePath 'READONLY_RUNTIME_BYTES_NO_RUNTIME_PROBE'
if ($runtimeBinding.sha256 -ne $expectedRuntimeSha) { throw 'Known runtime bytes changed.' }
$bindings += $runtimeBinding
$createdUtc = [DateTime]::UtcNow.ToString('o')
$manifest = [ordered]@{schema='ROUND22_THERMAL_COMPONENT_PREPARED_MANIFEST_V1';time_utc=$createdUtc;
    status='PREPARED_COMPONENT_SOURCES_ONLY_NOT_EXECUTED';actor='ROLE6';bank_id='THERMAL_COMPONENT_AUX22';
    scope='THERMAL_COMPONENT_AUX_ONLY';bindings=$bindings;binding_count=$bindings.Count;
    component_math_invocations=0;component_Lean_invocations=0;old_bank_replays=0;runtime_probes=0;H1_claim=$false;WIN=$false}
CreateJson $manifestPath $manifest
$bindings += Binding $manifestPath 'NEW_PREPARED_COMPONENT_MANIFEST'
$preparation = [ordered]@{schema='ROUND22_THERMAL_COMPONENT_PREPARATION_V1';time_utc=$createdUtc;
    status='PREPARED_SOURCE_ONLY_NOT_EXECUTED';actor='ROLE6';bank_id='THERMAL_COMPONENT_AUX22';scope='THERMAL_COMPONENT_AUX_ONLY';
    runtime_path=$runtimePath;runtime_flags=@('-B','-X','utf8');bindings=$bindings;binding_count=$bindings.Count;
    captures_before_START=($bindings.Count+2);root_gate_path=$rootGatePath;future_actual_directory=$actualPath;
    expected_case_count=44;expected_Gamma_phase_cases=15;expected_reference_cells_each=2240;expected_reference_cells_total=33600;
    expected_mutation_count=19;expected_sqrt_certificates=15;sole_attempt_consumed=$false;
    component_math_executions=0;component_Lean_executions=0;old_producer_reexecutions=0;cost_measured=$false;
    no_credit_for_global_H1_Weil_heat_coefficientN_DN_WIN=$true;
    command_template=@($runtimePath,'-B','-X','utf8',(Join-Path $componentDirectory 'run_component_once22.py'),
        '--root-authorization','EXACT_DISTINCT_ROOT_GATE','--root-authorization-sha256','EXACT_GATE_SHA256')}
CreateJson $preparationPath $preparation
$summary = [ordered]@{metadata_only=$true;time_utc=$createdUtc;binding_count=$bindings.Count;captures_before_START=($bindings.Count+2);
    manifest_sha256=(Get-FileHash -LiteralPath $manifestPath -Algorithm SHA256).Hash.ToLowerInvariant();
    preparation_sha256=(Get-FileHash -LiteralPath $preparationPath -Algorithm SHA256).Hash.ToLowerInvariant();
    component_math_executions=0;Lean_executions=0;gate_created=$false;actual_attempt_created=$false;bindings=$bindings}
$summary | ConvertTo-Json -Depth 30
