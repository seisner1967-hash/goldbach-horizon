$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$taskOwned = Join-Path $taskBase 'round22\role6'
$taskRuntime = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$taskGate = Join-Path $taskBase '.arbor\sessions\parity\.coordinator\messages\round22_epstein_authorization.json'
$taskPrep = Join-Path $taskOwned 'epstein_preparation22.json'
$taskManifest = Join-Path $taskOwned 'prepared_manifest22.json'
$taskActual = Join-Path $taskOwned 'actual_epstein22'

# Metadata only.  No Python, Lean, import, parser probe or math producer is invoked.
function Write-TaskCreateNewJson([string]$targetPath, $payload) {
    $resolved = [IO.Path]::GetFullPath($targetPath)
    $ownedPrefix = [IO.Path]::GetFullPath($taskOwned) + [IO.Path]::DirectorySeparatorChar
    if (-not $resolved.StartsWith($ownedPrefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw ('Write outside ROLE6 ownership: ' + $resolved)
    }
    $bytes = [Text.UTF8Encoding]::new($false).GetBytes(($payload | ConvertTo-Json -Depth 50) + "`n")
    $stream = [IO.File]::Open($resolved, [IO.FileMode]::CreateNew, [IO.FileAccess]::Write, [IO.FileShare]::None)
    try { $stream.Write($bytes, 0, $bytes.Length) } finally { $stream.Dispose() }
}
function Get-TaskBinding([string]$path, [string]$role) {
    $resolved = [IO.Path]::GetFullPath($path)
    $item = Get-Item -LiteralPath $resolved
    if ($item.PSIsContainer) { throw ('Not a file: ' + $resolved) }
    return [ordered]@{ path=$resolved; role=$role; bytes=$item.Length; sha256=(Get-FileHash -LiteralPath $resolved -Algorithm SHA256).Hash.ToLowerInvariant() }
}
if (Test-Path -LiteralPath $taskActual) { throw 'Actual attempt already reserved; no preparation rerun.' }
if (Test-Path -LiteralPath $taskPrep) { throw 'Preparation already exists; no overwrite.' }
if (Test-Path -LiteralPath $taskManifest) { throw 'Prepared manifest already exists; no overwrite.' }

$taskSources = @(
    @{path=(Join-Path $taskOwned 'interval22.py');role='new_exact_outward_library'},
    @{path=(Join-Path $taskOwned 'epstein_bank22.py');role='new_math_producer_SOURCE_ONLY'},
    @{path=(Join-Path $taskOwned 'epstein_contract22.json');role='canonical24case_contract'},
    @{path=(Join-Path $taskOwned 'epstein_paper22.md');role='primitive_telescope_tail_paper'},
    @{path=(Join-Path $taskOwned 'run_epstein_once22.py');role='one_attempt_launcher_SOURCE_ONLY'},
    @{path=(Join-Path $taskOwned 'strict_precontract22.json');role='per_layer_scope_guards'},
    @{path=(Join-Path $taskOwned 'read_scope22.json');role='actual_read_scopes'},
    @{path=(Join-Path $taskOwned 'pivot_ack22.json');role='zero_math21_ack_conservation21_distinct'},
    @{path=(Join-Path $taskOwned 'preparation_notes22.md');role='review_and_future_receipt_protocol'},
    @{path=(Join-Path $taskOwned 'prepare_epstein_metadata22.ps1');role='metadata_builder_SOURCE_NO_PYTHON'},
    @{path=(Join-Path $taskBase 'round22\agent6_precontract.md');role='ROLE6_final_precontract'},
    @{path=(Join-Path $taskBase 'round22\USER_DIRECTIVE.md');role='user_definitive_pivot_FULL'},
    @{path=(Join-Path $taskBase 'round22\PROBE_BLOCK.md');role='continuous_probe_FULL'},
    @{path=(Join-Path $taskBase 'round22\previous_artifacts_sha256.json');role='3089_registry_FILE_SHA_ONLY'},
    @{path=(Join-Path $taskBase 'round22\role1\real_trace_annex.md');role='FINAL1_future_Weil_annex_READ_ONLY'},
    @{path=(Join-Path $taskBase 'round22\role1\numeric_contract.md');role='FINAL1_numerics_READ_ONLY'},
    @{path=(Join-Path $taskBase 'round22\role2\uniform_formula.md');role='FINAL2_geometric_and_analytic_formula_READ_ONLY'},
    @{path=(Join-Path $taskBase 'round22\role2\numeric_contract.md');role='FINAL2_G0_H0_C0_READ_ONLY'},
    @{path=(Join-Path $taskBase 'round22\role2\final_manifest.json');role='FINAL2_archive_binding_READ_ONLY'},
    @{path=$taskRuntime;role='known_runtime_BYTES_ONLY'}
)
$taskBindings = @($taskSources | ForEach-Object { Get-TaskBinding $_.path $_.role })
$taskExpected = @{
    $taskRuntime='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
    (Join-Path $taskBase 'round22\USER_DIRECTIVE.md')='c5aa8310ad54c57726339a8e99057f158254eb6d113ac3aeb71ddc9627f23947'
    (Join-Path $taskBase 'round22\PROBE_BLOCK.md')='a896c9d0fa4114845b20c3023246dcb987463923df798cac2c537c70cfb73fc3'
    (Join-Path $taskBase 'round22\previous_artifacts_sha256.json')='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
    (Join-Path $taskBase 'round22\role1\real_trace_annex.md')='4736c056f047c84f4ebe38ed4f60b1a9c473481006dcee8341c168afdd9ea2b5'
    (Join-Path $taskBase 'round22\role1\numeric_contract.md')='8c593946be90aa424120b7ec74b664cf447e9791af3510143df791efd986280a'
    (Join-Path $taskBase 'round22\role2\uniform_formula.md')='720b8b2363c222321e7f50752591a8a5d0e992c119bfc3b4f445b9c80b7b7825'
    (Join-Path $taskBase 'round22\role2\numeric_contract.md')='943470e906efd8a77b2fbdbe50f001978e9bbaa9c20101f6ad379bcca9e03ebf'
    (Join-Path $taskBase 'round22\role2\final_manifest.json')='0e225a6f5cf711a9588670e868a94ee5103be4b9124275888f2e79f7ffa3f13f'
}
foreach ($binding in $taskBindings) {
    if ($taskExpected.ContainsKey($binding.path) -and $taskExpected[$binding.path] -ne $binding.sha256) {
        throw ('Fixed input/runtime byte mismatch: ' + $binding.path)
    }
}
$taskTime = [DateTime]::UtcNow.ToString('o')
$taskManifestPayload = [ordered]@{
    schema='round22.role6.prepared_manifest.v1'; status='FROZEN_SOURCES_ONLY_NOT_MATH_EXECUTED'; metadata_created_utc=$taskTime
    actual_math22=0; actual_Lean22=0; actual_conservation22=0; old_file_writes=0
    source_count=$taskBindings.Count; bindings=$taskBindings; excludes_self=$true
}
Write-TaskCreateNewJson $taskManifest $taskManifestPayload
$taskAllBindings = @($taskBindings) + @(Get-TaskBinding $taskManifest 'prepared_manifest_metadata_only')
$taskLauncherCommand = @($taskRuntime,'-B','-X','utf8',(Join-Path $taskOwned 'run_epstein_once22.py'),'--root-authorization',$taskGate,'--root-authorization-sha256','ROOT_FUTURE_GATE_SHA256_REQUIRED')
$taskProducerCommand = @($taskRuntime,'-B','-X','utf8',(Join-Path $taskOwned 'epstein_bank22.py'),'--contract',(Join-Path $taskOwned 'epstein_contract22.json'),'--output',(Join-Path $taskActual 'epstein_result22.json'))
$taskPreparationPayload = [ordered]@{
    schema='round22.epstein_unfolding_aux.preparation.v1'; status='PREPARED_STOP_UNTIL_FULL_ROOT_SHA_SELECTION_DISTINCT_GATE'
    metadata_created_utc=$taskTime; preparation_id=[Guid]::NewGuid().ToString(); actual_math22=0; actual_Lean22=0
    bank_id='EPSTEIN_UNFOLDING_AUX22'; scope='EPSTEIN_UNFOLDING_AUX_ONLY'; N=100000000; Y=10000; cases=24
    original_cases=18; scale_cases=6; precision_bits=96; tolerance=@(1,100000); tail_cap=@(1,1000000)
    coefficient_N_computed=$false; heat_signal_computed=$false; Weil_trace_computed=$false; D_N_bound_proved=$false
    source_onset_satisfied=$false; forbidden_methods_used=$false; old_results_replayed=$false
    runtime_path=$taskRuntime; runtime_sha256=$taskExpected[$taskRuntime]; runtime_probe_invocations=0
    root_authorization_path=$taskGate; root_authorization_exists_at_preparation=(Test-Path -LiteralPath $taskGate)
    root_gate_sha_not_yet_known=$true; launcher_command_template=$taskLauncherCommand; producer_command=$taskProducerCommand
    bindings=$taskAllBindings; binding_count=$taskAllBindings.Count
    capture_plan=[ordered]@{phase='PREEXEC_BEFORE_MATH_START'; bound_file_copies=$taskAllBindings.Count; additional_copies=@('epstein_preparation22.json','root_gate.json'); planned_total=($taskAllBindings.Count+2); execute_now=$false}
    reserved_actual_directory=$taskActual; reserved_directory_exists=$false; one_actual_attempt_only=$true
    paper_resource_estimate=[ordered]@{individual_original_shifts=(18*8193); scale_indices_represented_per_case=2097153; scale_individual_shifts_evaluated=0; approx_sqrt_certificates='about300000'; no_timing_or_math_benchmark=$true}
    receipts_plan=@('attempt_reservation.json','PREEXEC_captures.json','actual_START.json','actual.log','epstein_result22.json','epstein_sqrt_certificates22.jsonl','POSTEXEC_integrity.json','actual_receipt.json')
    preparation_is_not_START_or_PASS=$true; old3089_registry_scope='file_sha_only_not_reexecution_or_full_preflight'
    after_preparation='STOP_NO_IMPORT_NO_PRODUCER_NO_LEAN_WAIT_FOR_ROOT'
}
Write-TaskCreateNewJson $taskPrep $taskPreparationPayload
Write-Output (([ordered]@{status=$taskPreparationPayload.status;scope=$taskPreparationPayload.scope;binding_count=$taskPreparationPayload.binding_count;capture_plan=$taskPreparationPayload.capture_plan;actual_math22=0;actual_Lean22=0}) | ConvertTo-Json -Depth 10)
Get-FileHash -LiteralPath $taskPrep,$taskManifest,(Join-Path $taskBase 'round22\agent6_precontract.md'),(Join-Path $taskOwned 'interval22.py'),(Join-Path $taskOwned 'epstein_bank22.py'),(Join-Path $taskOwned 'run_epstein_once22.py'),(Join-Path $taskOwned 'prepare_epstein_metadata22.ps1') -Algorithm SHA256 | Select-Object Path,Hash | ConvertTo-Json
