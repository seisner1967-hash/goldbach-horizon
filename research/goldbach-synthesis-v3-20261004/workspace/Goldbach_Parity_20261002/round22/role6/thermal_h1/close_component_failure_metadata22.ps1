# New metadata closure only; no evaluator import/run or numerical recheck.
$ErrorActionPreference='Stop'
$closureDirectory=$PSScriptRoot
$actualDirectory=Join-Path $closureDirectory 'actual_component22'
$preparationPath=Join-Path $closureDirectory 'component_preparation22.json'
$closurePath=Join-Path $closureDirectory 'component_failure_receipt22.json'
if (Test-Path -LiteralPath $closurePath) { throw 'Closure already exists; will not overwrite.' }
$preparation=Get-Content -LiteralPath $preparationPath -Raw | ConvertFrom-Json
$actualReceipt=Get-Content -LiteralPath (Join-Path $actualDirectory 'actual_receipt.json') -Raw | ConvertFrom-Json
$captures=Get-Content -LiteralPath (Join-Path $actualDirectory 'PREEXEC_captures.json') -Raw | ConvertFrom-Json
$post=Get-Content -LiteralPath (Join-Path $actualDirectory 'POSTEXEC_integrity.json') -Raw | ConvertFrom-Json
foreach ($binding in $preparation.bindings) {
    if ((Get-FileHash -LiteralPath $binding.path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $binding.sha256) { throw 'Binding changed.' }
    if ((Get-Item -LiteralPath $binding.path).Length -ne $binding.bytes) { throw 'Binding bytes changed.' }
}
foreach ($capture in $captures.captures) {
    if ($capture.phase -ne 'PREEXEC') { throw 'Capture phase differs.' }
    if ((Get-FileHash -LiteralPath $capture.copy -Algorithm SHA256).Hash.ToLowerInvariant() -ne $capture.sha256) { throw 'Capture bytes changed.' }
}
if (($actualReceipt.exit_code -ne 1) -or ($null -ne $actualReceipt.result_sha256) -or (-not $post.all_unchanged)) { throw 'Unexpected raw receipt.' }
if (Test-Path -LiteralPath (Join-Path $actualDirectory 'component_result22.json')) { throw 'Unexpected result file.' }
$artifacts=@()
foreach ($name in @('attempt_reservation.json','actual_START.json','actual.log','PREEXEC_captures.json',
    'POSTEXEC_integrity.json','actual_receipt.json','component_sqrt_certificates22.jsonl')) {
    $path=Join-Path $actualDirectory $name
    $artifacts += [ordered]@{path=$path;sha256=(Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant();bytes=(Get-Item -LiteralPath $path).Length}
}
$certificateLines=@(Get-Content -LiteralPath (Join-Path $actualDirectory 'component_sqrt_certificates22.jsonl'))
$data=[ordered]@{schema='ROUND22_COMPONENT_FAILURE_CLOSURE_V1';time_utc=[DateTime]::UtcNow.ToString('o');
    classification='TECHNICAL_SERIALIZATION_FAILURE_NO_COMPLETED_RESULT';bank_id='THERMAL_COMPONENT_AUX22';
    actual_START=$actualReceipt.actual_START;actual_FINISH=$actualReceipt.actual_FINISH;exit_code=1;
    attempt_token=$actualReceipt.attempt_token;attempt_consumed=$true;automatic_retry=0;
    preparation_sha256=(Get-FileHash -LiteralPath $preparationPath -Algorithm SHA256).Hash.ToLowerInvariant();
    bindings_verified=$preparation.bindings.Count;PREEXEC_copies_verified=$captures.captures.Count;
    POSTEXEC_all_unchanged=$post.all_unchanged;certificate_line_count=$certificateLines.Count;
    certificate_scope='READ_FULL_METADATA_NO_NEW_INTEGER_SQUARE_CHECK';artifacts=$artifacts;
    raw_FULL_reads=@('8ee9d7','2a6c38','44eab4','19233f','67b1e1','b93fc7');
    completed_result=$false;partial_PASS=$false;H1_claim=$false;coefficientN_claim=$false;D_N_claim=$false;WIN=$false;
    current_bank_math_invocations=1;Lean_invocations=0;old_bank_replays=0;new_revision_math_invocations=0}
$encoding=[System.Text.UTF8Encoding]::new($false)
$stream=[System.IO.File]::Open($closurePath,[System.IO.FileMode]::CreateNew,[System.IO.FileAccess]::Write)
try { $content=$encoding.GetBytes(($data | ConvertTo-Json -Depth 20)+"`n");$stream.Write($content,0,$content.Length) }
finally { $stream.Dispose() }
[ordered]@{metadata_only=$true;closure_sha256=(Get-FileHash -LiteralPath $closurePath -Algorithm SHA256).Hash.ToLowerInvariant();
    bindings=$preparation.bindings.Count;captures=$captures.captures.Count;certificates=$certificateLines.Count;
    receipt_sha256=(Get-FileHash -LiteralPath (Join-Path $actualDirectory 'actual_receipt.json') -Algorithm SHA256).Hash.ToLowerInvariant();
    report_sha256=(Get-FileHash -LiteralPath (Join-Path $closureDirectory 'component_failure22.md') -Algorithm SHA256).Hash.ToLowerInvariant()} | ConvertTo-Json
