$ErrorActionPreference='Stop'
$roleDir='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\role3'
$oldDir=Join-Path $roleDir 'stage03'
$revisionDir=Join-Path $oldDir 'revision02'
$utf8=[System.Text.UTF8Encoding]::new($false)
function Save-Json($name,$value) {
  $target=Join-Path $revisionDir $name
  if (Test-Path -LiteralPath $target) {throw ('refusing replacement: '+$target)}
  [IO.File]::WriteAllText($target,($value|ConvertTo-Json -Depth 40)+[Environment]::NewLine,$utf8)
}
$oldManifest=Get-Content -Raw -LiteralPath (Join-Path $oldDir 'source_manifest.json')|ConvertFrom-Json
foreach($entry in $oldManifest.inputs){
  if((Get-FileHash -LiteralPath $entry.path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $entry.sha256){throw ('frozen input changed: '+$entry.path)}
}
$now=[DateTimeOffset]::UtcNow.ToString('o')
$logPath=Join-Path $oldDir 'stage03_attempt01\EpsteinUnfold22.log'
if((Get-FileHash -LiteralPath $logPath -Algorithm SHA256).Hash.ToLowerInvariant() -ne 'f187b9a31dbfe4c85cb51c6bbfef4ea6a069babd296f582737b66ce50ee50b54'){throw 'failure log changed'}
Save-Json 'read_receipts.json' ([ordered]@{schema='round22.role3.unfold_revision02.read_receipts.v1';time=$now;inherited_read_receipts=(Join-Path $oldDir 'read_receipts.json');failure_log=$logPath;failure_log_sha256='f187b9a31dbfe4c85cb51c6bbfef4ea6a069babd296f582737b66ce50ee50b54';failure_log_scope='FULL';failure_log_chunk='91ebcb';additional_API_read=[ordered]@{path='Mathlib/MeasureTheory/Integral/IntervalIntegral.lean';scope='TARGETED';lines='552-572';reason='integral_const_mul is unconditional'};new_compiler_calls=0;Python_math_calls=0;old_PASS_replays=0})
$paths=@((Join-Path $oldDir 'source_manifest.json'),(Join-Path $oldDir 'prepared_receipt.json'),$logPath,(Join-Path $oldDir 'stage03_attempt01\PREEXEC.json'),(Join-Path $oldDir 'stage03_attempt01\POSTEXEC.json'),(Join-Path $oldDir 'stage03_attempt01\receipt.json'),(Join-Path $revisionDir 'EpsteinUnfold22.lean'),(Join-Path $revisionDir 'run_revision02_once.py'),(Join-Path $revisionDir 'preparation.md'),(Join-Path $revisionDir 'read_receipts.json'),(Join-Path $revisionDir 'write_metadata.ps1'))
$inputs=@($oldManifest.inputs|ForEach-Object{[ordered]@{path=$_.path;sha256=$_.sha256}})+@($paths|ForEach-Object{[ordered]@{path=$_;sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}})
$source=Join-Path $revisionDir 'EpsteinUnfold22.lean'
$body=[IO.File]::ReadAllText($source)
if([regex]::IsMatch($body,'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b')){throw 'forbidden source construct'}
$rows=@([ordered]@{module='EpsteinUnfold22';path=$source;sha256=(Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant();theorem_count=([regex]::Matches($body,'(?m)^theorem\s+')).Count;definition_count=([regex]::Matches($body,'(?m)^def\s+')).Count;axiom_print_count=([regex]::Matches($body,'(?m)^#print axioms Epstein22\.')).Count;status='SOURCE_ONLY_UNCOMPILED'})
Save-Json 'source_manifest.json' ([ordered]@{schema='round22.role3.unfold_revision02.source_manifest.v1';time=$now;stage='G0_UNFOLD_REVISION02';node_id='16.1';modules=@('EpsteinUnfold22');module_rows=$rows;inputs=$inputs;dependency_olean_sha256='679f572be0d81f8c86bfa418fb460d5168774fc56b2b2537a9469ff0aca7a544';previous_actual_attempt='stage03_attempt01';previous_actual_exit=1;new_Lean_invocations=0;infinite_G0_complete=$false;new_D_N_bound=$false;victory=$false})
$manifestHash=(Get-FileHash -LiteralPath (Join-Path $revisionDir 'source_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant()
Save-Json 'prepared_receipt.json' ([ordered]@{schema='round22.role3.unfold_revision02.prepared_receipt.v1';time=$now;status='PREPARED_SOURCE_ONLY_REQUEST_ROOT_FULL_SHA_REVIEW';source_manifest_sha256=$manifestHash;launcher_sha256=(Get-FileHash -LiteralPath (Join-Path $revisionDir 'run_revision02_once.py') -Algorithm SHA256).Hash.ToLowerInvariant();input_count=$inputs.Count;module_rows=$rows;Lean_gate='CLOSED';new_compiler_calls=0;Python_math_calls=0;no_win=$true;metadata_exit_credit='actual tool return required separately'})
[ordered]@{status='UNFOLD_REVISION02_PREPARED_SOURCE_ONLY';source_manifest_sha256=$manifestHash;input_count=$inputs.Count;module_rows=$rows}|ConvertTo-Json -Depth 12
