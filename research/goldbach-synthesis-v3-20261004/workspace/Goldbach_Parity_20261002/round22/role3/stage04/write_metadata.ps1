$ErrorActionPreference='Stop'
$taskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$roleDir=Join-Path $taskBase 'round22\role3'
$stageDir=Join-Path $roleDir 'stage04'
$unfoldDir=Join-Path $roleDir 'stage03\revision04'
$unfoldOut=Join-Path $unfoldDir 'stage03_attempt04'
$finiteDir=Join-Path $roleDir 'stage02\revision03'
$finiteOut=Join-Path $finiteDir 'stage02_attempt03'
$kernelDir=Join-Path $roleDir 'revision02'
$kernelOut=Join-Path $kernelDir 'stage01_attempt02'
$utf8=[System.Text.UTF8Encoding]::new($false)
function Save-Json($name,$value){
  $target=Join-Path $stageDir $name
  if(Test-Path -LiteralPath $target){throw ('refusing replacement: '+$target)}
  [IO.File]::WriteAllText($target,($value|ConvertTo-Json -Depth 40)+[Environment]::NewLine,$utf8)
}
$prior=Get-Content -Raw -LiteralPath (Join-Path $unfoldDir 'source_manifest.json')|ConvertFrom-Json
foreach($entry in $prior.inputs){if((Get-FileHash -LiteralPath $entry.path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $entry.sha256){throw ('frozen dependency input changed: '+$entry.path)}}
$unfoldReceipt=Get-Content -Raw -LiteralPath (Join-Path $unfoldOut 'receipt.json')|ConvertFrom-Json
if($unfoldReceipt.status -ne 'AUTHOR_STAGE_AUX_PASS' -or $unfoldReceipt.actual_child_invocations -ne 1 -or -not $unfoldReceipt.all_source_inputs_unchanged){throw 'actual Unfold PASS required'}
$unfoldOlean=Join-Path $unfoldOut 'EpsteinUnfold22.olean'
$unfoldHash=(Get-FileHash -LiteralPath $unfoldOlean -Algorithm SHA256).Hash.ToLowerInvariant()
if($unfoldHash -ne $unfoldReceipt.rows[0].olean_sha256){throw 'Unfold olean differs from actual receipt'}
$launcher=Join-Path $stageDir 'run_stage04_once.py'
if(-not [IO.File]::ReadAllText($launcher).Contains('DEPENDENCY_OLEAN_SHA = "'+$unfoldHash+'"')){throw 'launcher dependency not finalized'}
$now=[DateTimeOffset]::UtcNow.ToString('o')
Save-Json 'read_receipts.json' ([ordered]@{schema='round22.role3.tail_stage04.read_receipts.v1';time=$now;inherited_FINAL2_FULL_receipts=(Join-Path $roleDir 'phase_read_receipts.json');tail_source_FULL='e6e45a';joint_continuity_API_TARGETED='e886d5 GroupWithZero lines179..211';independent_SOURCE_review='ROLE4 FULL a30387 before field_simp/gcongr clarifications and new joint continuity';kernel_PASS_log_FULL='41e1f7';finite_PASS_log_FULL='5e8492';unfold_PASS_log_FULL='4ee808';unfold_PASS_receipt_FULL='289c04';unfold_actual_invocation='4752d4 session40561, final a4760e exit0';new_stage04_compiler_calls=0;Python_math_calls=0;old_PASS_replays=0})
$phase=Get-Content -Raw -LiteralPath (Join-Path $roleDir 'phase_read_receipts.json')|ConvertFrom-Json
$paths=@($phase.entries|ForEach-Object{$_.path})+@(
  (Join-Path $taskBase 'round22\USER_DIRECTIVE.md'),(Join-Path $taskBase 'round22\PROBE_BLOCK.md'),(Join-Path $roleDir 'phase_read_receipts.json'),
  (Join-Path $kernelDir 'EpsteinKernel22.lean'),(Join-Path $kernelOut 'EpsteinKernel22.olean'),(Join-Path $kernelOut 'EpsteinKernel22.log'),(Join-Path $kernelOut 'receipt.json'),
  (Join-Path $finiteDir 'EpsteinFinite22.lean'),(Join-Path $finiteOut 'EpsteinFinite22.olean'),(Join-Path $finiteOut 'EpsteinFinite22.log'),(Join-Path $finiteOut 'receipt.json'),
  (Join-Path $unfoldDir 'EpsteinUnfold22.lean'),(Join-Path $unfoldDir 'source_manifest.json'),(Join-Path $unfoldDir 'prepared_receipt.json'),$unfoldOlean,(Join-Path $unfoldOut 'EpsteinUnfold22.log'),(Join-Path $unfoldOut 'receipt.json'),(Join-Path $unfoldOut 'PREEXEC.json'),(Join-Path $unfoldOut 'POSTEXEC.json'),
  'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\Topology\Algebra\GroupWithZero.lean',
  (Join-Path $stageDir 'EpsteinTail22.lean'),$launcher,(Join-Path $stageDir 'preparation.md'),(Join-Path $stageDir 'read_receipts.json'),(Join-Path $stageDir 'write_metadata.ps1')
)
$inputs=@($paths|ForEach-Object{[ordered]@{path=$_;sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}})
$source=Join-Path $stageDir 'EpsteinTail22.lean'
$body=[IO.File]::ReadAllText($source)
if([regex]::IsMatch($body,'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b')){throw 'forbidden source construct'}
$rows=@([ordered]@{module='EpsteinTail22';path=$source;sha256=(Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant();theorem_count=([regex]::Matches($body,'(?m)^theorem\s+')).Count;definition_count=([regex]::Matches($body,'(?m)^def\s+')).Count;axiom_print_count=([regex]::Matches($body,'(?m)^#print axioms Epstein22\.')).Count;status='SOURCE_ONLY_UNCOMPILED'})
Save-Json 'source_manifest.json' ([ordered]@{schema='round22.role3.tail_stage04.source_manifest.v1';time=$now;stage='G0_TAIL_STAGE04';node_id='16.1';modules=@('EpsteinTail22');module_rows=$rows;inputs=$inputs;dependency_olean_sha256=$unfoldHash;dependency_recompile=$false;new_Lean_invocations=0;tail_complete=$false;new_D_N_bound=$false;victory=$false})
$manifestHash=(Get-FileHash -LiteralPath (Join-Path $stageDir 'source_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant()
Save-Json 'prepared_receipt.json' ([ordered]@{schema='round22.role3.tail_stage04.prepared_receipt.v1';time=$now;status='PREPARED_SOURCE_ONLY_REQUEST_ROOT_FULL_SHA_REVIEW';source_manifest_sha256=$manifestHash;launcher_sha256=(Get-FileHash -LiteralPath $launcher -Algorithm SHA256).Hash.ToLowerInvariant();input_count=$inputs.Count;module_rows=$rows;Lean_gate='CLOSED';new_compiler_calls=0;Python_math_calls=0;no_win=$true;metadata_exit_credit='actual tool return required separately'})
[ordered]@{status='TAIL_STAGE04_PREPARED_SOURCE_ONLY';source_manifest_sha256=$manifestHash;input_count=$inputs.Count;module_rows=$rows}|ConvertTo-Json -Depth 12
