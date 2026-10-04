$ErrorActionPreference='Stop'
$taskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$roleDir=Join-Path $taskBase 'round22\role3'
$stageDir=Join-Path $roleDir 'stage03'
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
$priorManifest=Get-Content -Raw -LiteralPath (Join-Path $finiteDir 'source_manifest.json')|ConvertFrom-Json
foreach($entry in $priorManifest.inputs){if((Get-FileHash -LiteralPath $entry.path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $entry.sha256){throw ('frozen dependency input changed: '+$entry.path)}}
$finiteReceipt=Get-Content -Raw -LiteralPath (Join-Path $finiteOut 'receipt.json')|ConvertFrom-Json
if($finiteReceipt.status -ne 'AUTHOR_STAGE_AUX_PASS' -or $finiteReceipt.actual_child_invocations -ne 1 -or -not $finiteReceipt.all_source_inputs_unchanged){throw 'actual Finite PASS required'}
$finiteOlean=Join-Path $finiteOut 'EpsteinFinite22.olean'
$finiteHash=(Get-FileHash -LiteralPath $finiteOlean -Algorithm SHA256).Hash.ToLowerInvariant()
if($finiteHash -ne $finiteReceipt.rows[0].olean_sha256){throw 'Finite olean differs from actual receipt'}
$launcher=Join-Path $stageDir 'run_stage03_once.py'
if(-not [IO.File]::ReadAllText($launcher).Contains('DEPENDENCY_OLEAN_SHA = "'+$finiteHash+'"')){throw 'launcher dependency not finalized'}
$now=[DateTimeOffset]::UtcNow.ToString('o')
Save-Json 'read_receipts.json' ([ordered]@{schema='round22.role3.unfold_stage03.read_receipts.v1';time=$now;inherited_FINAL2_FULL_receipts=(Join-Path $roleDir 'phase_read_receipts.json');independent_SOURCE_review='ROLE4 FULL fdffac before constructive natAbs-only clarification; no mathematical missing charge reported';root_stage03_SOURCE_read='FULL 0eca6f';kernel_PASS_log_FULL='41e1f7';API_reads=@([ordered]@{path='Mathlib/MeasureTheory/Integral/DominatedConvergence.lean';scope='TARGETED';lines='152-155';source_read='actual static source'},[ordered]@{path='Mathlib/Analysis/NormedSpace/FunctionSeries.lean';scope='TARGETED';lines='101-115';chunk='fa5e96'},[ordered]@{path='Mathlib/Analysis/PSeries.lean';scope='TARGETED';lines='321-330';chunk='fa5e96'},[ordered]@{path='Mathlib/Analysis/Normed/Group/InfiniteSum.lean';scope='TARGETED';lines='100-107';chunk='6fd814'},[ordered]@{path='Mathlib/Topology/Algebra/InfiniteSum/Defs.lean';scope='TARGETED';lines='148-157';chunk='6fd814'});new_compiler_calls=0;Python_math_calls=0;old_PASS_replays=0})
$phaseReads=Get-Content -Raw -LiteralPath (Join-Path $roleDir 'phase_read_receipts.json')|ConvertFrom-Json
$paths=@($phaseReads.entries|ForEach-Object{$_.path})+@(
  (Join-Path $taskBase 'round22\USER_DIRECTIVE.md'),(Join-Path $taskBase 'round22\PROBE_BLOCK.md'),(Join-Path $roleDir 'phase_read_receipts.json'),
  (Join-Path $kernelDir 'EpsteinKernel22.lean'),(Join-Path $kernelOut 'EpsteinKernel22.olean'),(Join-Path $kernelOut 'EpsteinKernel22.log'),(Join-Path $kernelOut 'receipt.json'),
  (Join-Path $finiteDir 'EpsteinFinite22.lean'),(Join-Path $finiteDir 'source_manifest.json'),(Join-Path $finiteDir 'prepared_receipt.json'),$finiteOlean,(Join-Path $finiteOut 'EpsteinFinite22.log'),(Join-Path $finiteOut 'receipt.json'),(Join-Path $finiteOut 'PREEXEC.json'),(Join-Path $finiteOut 'POSTEXEC.json'),
  (Join-Path $stageDir 'EpsteinUnfold22.lean'),$launcher,(Join-Path $stageDir 'preparation.md'),(Join-Path $stageDir 'read_receipts.json'),(Join-Path $stageDir 'write_metadata.ps1')
)
$inputs=@($paths|ForEach-Object{[ordered]@{path=$_;sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}})
$source=Join-Path $stageDir 'EpsteinUnfold22.lean'
$body=[IO.File]::ReadAllText($source)
if([regex]::IsMatch($body,'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b')){throw 'forbidden source construct'}
$rows=@([ordered]@{module='EpsteinUnfold22';path=$source;sha256=(Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant();theorem_count=([regex]::Matches($body,'(?m)^theorem\s+')).Count;definition_count=([regex]::Matches($body,'(?m)^def\s+')).Count;axiom_print_count=([regex]::Matches($body,'(?m)^#print axioms Epstein22\.')).Count;status='SOURCE_ONLY_UNCOMPILED'})
Save-Json 'source_manifest.json' ([ordered]@{schema='round22.role3.unfold_stage03.source_manifest.v1';time=$now;stage='G0_UNFOLD_STAGE03';node_id='16.1';modules=@('EpsteinUnfold22');module_rows=$rows;inputs=$inputs;dependency_olean_sha256=$finiteHash;Kernel_recompile=$false;Finite_recompile=$false;new_Lean_invocations=0;infinite_G0_complete=$false;new_D_N_bound=$false;victory=$false})
$manifestHash=(Get-FileHash -LiteralPath (Join-Path $stageDir 'source_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant()
Save-Json 'prepared_receipt.json' ([ordered]@{schema='round22.role3.unfold_stage03.prepared_receipt.v1';time=$now;status='PREPARED_SOURCE_ONLY_REQUEST_ROOT_FULL_SHA_REVIEW';source_manifest_sha256=$manifestHash;launcher_sha256=(Get-FileHash -LiteralPath $launcher -Algorithm SHA256).Hash.ToLowerInvariant();input_count=$inputs.Count;module_rows=$rows;Lean_gate='CLOSED';new_compiler_calls=0;Python_math_calls=0;no_win=$true;metadata_exit_credit='actual tool return required separately'})
[ordered]@{status='UNFOLD_STAGE03_PREPARED_SOURCE_ONLY';source_manifest_sha256=$manifestHash;input_count=$inputs.Count;module_rows=$rows}|ConvertTo-Json -Depth 12
