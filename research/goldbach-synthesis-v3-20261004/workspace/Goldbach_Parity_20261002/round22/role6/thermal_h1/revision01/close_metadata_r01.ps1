# Closure metadata only; no Python, checker, numerical calculation, or Lean.
$ErrorActionPreference='Stop'
$revisionDirectory=$PSScriptRoot
$actualDirectory=Join-Path $revisionDirectory 'actual_r01'
$closurePath=Join-Path $revisionDirectory 'closure_receipt_r01.json'
if (Test-Path -LiteralPath $closurePath) { throw 'No closure overwrite.' }
function Sha([string]$path) { return (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() }
function Binding([string]$path) { return [ordered]@{path=$path;sha256=(Sha $path);bytes=(Get-Item -LiteralPath $path).Length} }
$prep=Get-Content -Raw -LiteralPath (Join-Path $revisionDirectory 'preparation_r01.json') | ConvertFrom-Json
$receipt=Get-Content -Raw -LiteralPath (Join-Path $actualDirectory 'actual_receipt.json') | ConvertFrom-Json
$captures=Get-Content -Raw -LiteralPath (Join-Path $actualDirectory 'PREEXEC_captures.json') | ConvertFrom-Json
$post=Get-Content -Raw -LiteralPath (Join-Path $actualDirectory 'POSTEXEC_integrity.json') | ConvertFrom-Json
$resultPath=Join-Path $actualDirectory 'result_r01.json'
$result=Get-Content -Raw -LiteralPath $resultPath | ConvertFrom-Json
if ($receipt.exit_code -ne 0 -or -not $receipt.post_integrity -or $receipt.launch_error) { throw 'Actual receipt failure.' }
if ($result.status -ne 'THERMAL_COMPONENT_R01_AUX_PASS' -or $result.cases.Count -ne 46 -or $result.mutations.Count -ne 19) { throw 'Result metadata mismatch.' }
if (-not $result.independent_checker.checker_PASS -or $result.failures.Count -ne 0 -or $result.unresolved.Count -ne 0) { throw 'Result verdict flags mismatch.' }
if ($result.H1_numeric_claim -or $result.H1_formal_claim -or $result.coefficient_N_claim -or $result.D_N_claim -or $result.WIN) { throw 'Invalid global claim.' }
if ($prep.bindings.Count -ne 33 -or $captures.captures.Count -ne 35 -or $captures.math_started) { throw 'PREEXEC metadata mismatch.' }
foreach ($binding in $prep.bindings) {
    if ((Sha $binding.path) -ne $binding.sha256 -or (Get-Item -LiteralPath $binding.path).Length -ne $binding.bytes) { throw 'Prepared binding changed.' }
}
foreach ($capture in $captures.captures) {
    if ($capture.phase -ne 'PREEXEC' -or (Sha $capture.copy) -ne $capture.sha256 -or (Sha $capture.source) -ne $capture.sha256) { throw 'PREEXEC byte capture mismatch.' }
}
if (-not $post.all_unchanged -or -not $post.gate_unchanged -or -not $post.preparation_unchanged -or $post.bindings.Count -ne 33) { throw 'POSTEXEC metadata mismatch.' }
foreach ($binding in $post.bindings) {
    if (-not $binding.unchanged -or $binding.actual_sha256 -ne $binding.expected_sha256 -or (Sha $binding.path) -ne $binding.expected_sha256) { throw 'POSTEXEC byte mismatch.' }
}
$oldPrepPath=Join-Path (Split-Path $revisionDirectory -Parent) 'component_preparation22.json'
$oldPrep=Get-Content -Raw -LiteralPath $oldPrepPath | ConvertFrom-Json
if ($oldPrep.bindings.Count -ne 25) { throw 'Original binding catalogue mismatch.' }
foreach ($binding in $oldPrep.bindings) {
    if ((Sha $binding.path) -ne $binding.sha256 -or (Get-Item -LiteralPath $binding.path).Length -ne $binding.bytes) { throw 'Original frozen binding changed.' }
}
if ((Sha $resultPath) -ne $receipt.result_sha256 -or (Sha (Join-Path $actualDirectory 'actual.log')) -ne $receipt.log_sha256 -or
    (Sha (Join-Path $actualDirectory 'sqrt_certificates_r01.jsonl')) -ne $receipt.sqrt_certificate_sha256) { throw 'Actual output digest mismatch.' }
$actualBindings=@()
foreach ($name in @('actual_START.json','attempt_reservation.json','PREEXEC_captures.json','actual_receipt.json',
    'actual.log','result_r01.json','sqrt_certificates_r01.jsonl','POSTEXEC_integrity.json')) {
    $actualBindings+=Binding (Join-Path $actualDirectory $name)
}
$certificateLines=@(Get-Content -LiteralPath (Join-Path $actualDirectory 'sqrt_certificates_r01.jsonl')).Count
if ($certificateLines -ne 15) { throw 'Certificate line count mismatch.' }
$closure=[ordered]@{schema='ROUND22_COMPONENT_R01_METADATA_CLOSURE';time_utc=[DateTime]::UtcNow.ToString('o');
    status='CLOSED_AUX_PASS_NO_REPLAY';actor='ROLE6';scope='THERMAL_COMPONENT_R01_AUX_ONLY';
    attempt_token=$receipt.attempt_token;actual_START_utc='2026-10-03T10:41:16.513468+00:00';
    actual_FINISH_utc='2026-10-03T10:44:48.631579+00:00';exit_code=0;case_count=46;mutation_count=19;
    preparation_sha256=(Sha (Join-Path $revisionDirectory 'preparation_r01.json'));
    prepared_manifest_sha256=(Sha (Join-Path $revisionDirectory 'prepared_manifest_r01.json'));
    gate_sha256=$receipt.root_gate_sha256;new_bindings_verified=33;PREEXEC_copies_verified=35;POSTEXEC_bindings_verified=33;
    original_bindings_verified=25;sqrt_certificate_lines=15;mathematical_invocations=1;posthoc_math_invocations=0;
    Lean_invocations=0;old_bank_replays=0;previous_partial_values_as_oracle=$false;
    independent_checker_ran_in_unique_child=$true;independent_checker_rerun=$false;
    whole_result_JSON_parsed=$true;all46_case_decisions_and19_mutations_read=$true;raw3395_lines_FULL_read_claim=$false;
    reading_receipts=@('6e379e','61bc29','e02c33','744b84');truncated_read_recovered_scope='c22c78 raw rational output truncated;744b84 complete catalogue/decision/mutation projection';
    report=(Binding (Join-Path $revisionDirectory 'closure_report_r01.md'));actual_bindings=$actualBindings;
    global_H1_claim=$false;coefficient_N_claim=$false;D_N_claim=$false;WIN=$false}
$bytes=[System.Text.UTF8Encoding]::new($false).GetBytes(($closure | ConvertTo-Json -Depth 25)+"`n")
$stream=[System.IO.File]::Open($closurePath,[System.IO.FileMode]::CreateNew,[System.IO.FileAccess]::Write)
try { $stream.Write($bytes,0,$bytes.Length) } finally { $stream.Dispose() }
[ordered]@{metadata_only=$true;closure=(Binding $closurePath);report=$closure.report;actual_bindings=$actualBindings;
    verified_new_bindings=33;verified_PREEXEC=35;verified_original_bindings=25;new_math=0;new_Lean=0} | ConvertTo-Json -Depth 10

