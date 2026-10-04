$ErrorActionPreference='Stop'
$taskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$roleDir=Join-Path $taskBase 'round22\role3'
$stageDir=Join-Path $roleDir 'stage02'
$kernelDir=Join-Path $roleDir 'revision02'
$kernelOut=Join-Path $kernelDir 'stage01_attempt02'
$utf8=[System.Text.UTF8Encoding]::new($false)
function Save-Json($name,$value) {
  $target=Join-Path $stageDir $name
  if (Test-Path -LiteralPath $target) { throw ('refusing replacement: '+$target) }
  [IO.File]::WriteAllText($target,($value|ConvertTo-Json -Depth 40)+[Environment]::NewLine,$utf8)
}
$kernelManifest=Get-Content -Raw -LiteralPath (Join-Path $kernelDir 'source_manifest.json')|ConvertFrom-Json
foreach ($entry in $kernelManifest.inputs) {
  if ((Get-FileHash -LiteralPath $entry.path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $entry.sha256) { throw ('frozen input changed: '+$entry.path) }
}
$kernelReceipt=Get-Content -Raw -LiteralPath (Join-Path $kernelOut 'receipt.json')|ConvertFrom-Json
if ($kernelReceipt.status -ne 'AUTHOR_STAGE_AUX_PASS' -or $kernelReceipt.actual_child_invocations -ne 1 -or -not $kernelReceipt.all_source_inputs_unchanged) { throw 'actual Kernel receipt mismatch' }
$kernelOlean=Join-Path $kernelOut 'EpsteinKernel22.olean'
$kernelOleanHash=(Get-FileHash -LiteralPath $kernelOlean -Algorithm SHA256).Hash.ToLowerInvariant()
if ($kernelOleanHash -ne '9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d') { throw 'actual dependency olean mismatch' }
$now=[DateTimeOffset]::UtcNow.ToString('o')
Save-Json 'read_receipts.json' ([ordered]@{
  schema='round22.role3.finite_stage02.read_receipts.v1';time=$now;
  inherited_FINAL2_FULL_receipts=(Join-Path $roleDir 'phase_read_receipts.json');
  actual_Kernel_PASS_log_FULL_chunk='41e1f7';
  actual_Kernel_PASS_log_sha256='70182795d884a636bf5c89904a21ee83f4ce9c83fea2c718093a60cb2a275886';
  API_sources=@(
    [ordered]@{path='Mathlib/Data/Int/Interval.lean';scope='TARGETED';lines='71-89';chunk='435706'},
    [ordered]@{path='Mathlib/Algebra/BigOperators/Group/Finset.lean';scope='TARGETED_SEARCH';lines='588-592';source_search='actual read preceding stage02 preparation'},
    [ordered]@{path='Mathlib/MeasureTheory/Integral/IntervalIntegral.lean';scope='TARGETED';lines='675-688';chunk='331457'}
  );new_compiler_calls=0;Python_math_calls=0;old_PASS_replays=0
})
$phaseReads=Get-Content -Raw -LiteralPath (Join-Path $roleDir 'phase_read_receipts.json')|ConvertFrom-Json
$paths=@($phaseReads.entries|ForEach-Object {$_.path})+@(
  (Join-Path $taskBase 'round22\USER_DIRECTIVE.md'),
  (Join-Path $taskBase 'round22\PROBE_BLOCK.md'),
  (Join-Path $roleDir 'phase_read_receipts.json'),
  (Join-Path $kernelDir 'EpsteinKernel22.lean'),
  (Join-Path $kernelDir 'source_manifest.json'),
  (Join-Path $kernelDir 'prepared_receipt.json'),
  $kernelOlean,
  (Join-Path $kernelOut 'EpsteinKernel22.log'),
  (Join-Path $kernelOut 'PREEXEC.json'),
  (Join-Path $kernelOut 'POSTEXEC.json'),
  (Join-Path $kernelOut 'receipt.json'),
  (Join-Path $stageDir 'EpsteinFinite22.lean'),
  (Join-Path $stageDir 'run_stage02_once.py'),
  (Join-Path $stageDir 'preparation.md'),
  (Join-Path $stageDir 'read_receipts.json'),
  (Join-Path $stageDir 'write_metadata.ps1')
)
$inputs=@($paths|ForEach-Object {[ordered]@{path=$_;sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}})
$source=Join-Path $stageDir 'EpsteinFinite22.lean'
$body=[IO.File]::ReadAllText($source)
if ([regex]::IsMatch($body,'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b')) { throw 'forbidden source construct' }
$moduleRows=@([ordered]@{module='EpsteinFinite22';path=$source;sha256=(Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant();theorem_count=([regex]::Matches($body,'(?m)^theorem\s+')).Count;definition_count=([regex]::Matches($body,'(?m)^def\s+')).Count;axiom_print_count=([regex]::Matches($body,'(?m)^#print axioms Epstein22\.')).Count;status='SOURCE_ONLY_UNCOMPILED'})
Save-Json 'source_manifest.json' ([ordered]@{schema='round22.role3.finite_stage02.source_manifest.v1';time=$now;stage='G0_FINITE_STAGE02';node_id='16.1';modules=@('EpsteinFinite22');module_rows=$moduleRows;inputs=$inputs;dependency_olean_sha256=$kernelOleanHash;Kernel_recompile=$false;new_Lean_invocations=0;infinite_G0_complete=$false;new_D_N_bound=$false;victory=$false})
$manifestHash=(Get-FileHash -LiteralPath (Join-Path $stageDir 'source_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant()
Save-Json 'prepared_receipt.json' ([ordered]@{schema='round22.role3.finite_stage02.prepared_receipt.v1';time=$now;status='PREPARED_SOURCE_ONLY_REQUEST_ROOT_FULL_SHA_REVIEW';source_manifest_sha256=$manifestHash;launcher_sha256=(Get-FileHash -LiteralPath (Join-Path $stageDir 'run_stage02_once.py') -Algorithm SHA256).Hash.ToLowerInvariant();input_count=$inputs.Count;module_rows=$moduleRows;Lean_gate='CLOSED';new_compiler_calls=0;Python_math_calls=0;no_win=$true;metadata_exit_credit='actual tool return required separately'})
[ordered]@{status='FINITE_STAGE02_PREPARED_SOURCE_ONLY';source_manifest_sha256=$manifestHash;input_count=$inputs.Count;module_rows=$moduleRows}|ConvertTo-Json -Depth 12
