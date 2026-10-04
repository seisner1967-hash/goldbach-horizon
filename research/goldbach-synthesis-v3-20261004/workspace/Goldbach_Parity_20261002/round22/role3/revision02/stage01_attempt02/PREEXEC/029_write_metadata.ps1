$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$oldDir = Join-Path $taskBase 'round22\role3'
$revisionDir = Join-Path $oldDir 'revision02'
$utf8 = [System.Text.UTF8Encoding]::new($false)
function Save-Json($name, $value) {
  $target = Join-Path $revisionDir $name
  if (Test-Path -LiteralPath $target) { throw ('refusing metadata replacement: '+$target) }
  [IO.File]::WriteAllText($target, ($value | ConvertTo-Json -Depth 40) + [Environment]::NewLine, $utf8)
}
$now = [DateTimeOffset]::UtcNow.ToString('o')
$oldManifest = Get-Content -Raw -LiteralPath (Join-Path $oldDir 'stage01_source_manifest.json') | ConvertFrom-Json
foreach ($entry in $oldManifest.inputs) {
  if ((Get-FileHash -LiteralPath $entry.path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $entry.sha256) {
    throw ('frozen first-attempt input changed: '+$entry.path)
  }
}
$logPath = Join-Path $oldDir 'stage01_attempt01\EpsteinKernel22.log'
if ((Get-FileHash -LiteralPath $logPath -Algorithm SHA256).Hash.ToLowerInvariant() -ne '8affa881e01451cff53f978bd16fddddcc1dc4eb83b7fd3cd42c7b6f30f5552a') { throw 'actual failure log changed' }
Save-Json 'read_receipts.json' ([ordered]@{
  schema='round22.role3.kernel_revision02.read_receipts.v1';time=$now;
  inherited_final_read_receipts=(Join-Path $oldDir 'phase_read_receipts.json');
  inherited_final_read_receipts_sha256=(Get-FileHash -LiteralPath (Join-Path $oldDir 'phase_read_receipts.json') -Algorithm SHA256).Hash.ToLowerInvariant();
  actual_failure_log=$logPath;failure_log_sha256='8affa881e01451cff53f978bd16fddddcc1dc4eb83b7fd3cd42c7b6f30f5552a';
  failure_log_read_scope='FULL';failure_log_read_chunk='fd6861';
  correction_scope='SOURCE_ONLY_FROM_ACTUAL_COMPILER_DIAGNOSTICS';
  new_compiler_invocations=0;Python_math_invocations=0;old_PASS_replays=0
})
$newPaths = @(
  (Join-Path $oldDir 'stage01_source_manifest.json'),
  (Join-Path $oldDir 'stage01_prepared_receipt.json'),
  $logPath,
  (Join-Path $oldDir 'stage01_attempt01\PREEXEC.json'),
  (Join-Path $oldDir 'stage01_attempt01\POSTEXEC.json'),
  (Join-Path $oldDir 'stage01_attempt01\receipt.json'),
  (Join-Path $revisionDir 'EpsteinKernel22.lean'),
  (Join-Path $revisionDir 'run_revision02_once.py'),
  (Join-Path $revisionDir 'preparation.md'),
  (Join-Path $revisionDir 'read_receipts.json'),
  (Join-Path $revisionDir 'write_metadata.ps1')
)
$inputs = @($oldManifest.inputs | ForEach-Object {[ordered]@{path=$_.path;sha256=$_.sha256}}) + @($newPaths | ForEach-Object {[ordered]@{path=$_;sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}})
$source = Join-Path $revisionDir 'EpsteinKernel22.lean'
$body = [IO.File]::ReadAllText($source)
if ([regex]::IsMatch($body,'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b')) { throw 'forbidden source construct' }
$moduleRows = @([ordered]@{
  module='EpsteinKernel22';path=$source;sha256=(Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant();
  theorem_count=([regex]::Matches($body,'(?m)^theorem\s+')).Count;
  definition_count=([regex]::Matches($body,'(?m)^def\s+')).Count;
  axiom_print_count=([regex]::Matches($body,'(?m)^#print axioms Epstein22\.')).Count;
  status='SOURCE_ONLY_UNCOMPILED_REVISION02'
})
Save-Json 'source_manifest.json' ([ordered]@{
  schema='round22.role3.kernel_revision02.source_manifest.v1';time=$now;
  stage='G0_KERNEL_REVISION02';node_id='16.1';modules=@('EpsteinKernel22');module_rows=$moduleRows;
  inputs=$inputs;previous_actual_attempt='stage01_attempt01';previous_actual_exit=1;
  previous_actual_log_sha256='8affa881e01451cff53f978bd16fddddcc1dc4eb83b7fd3cd42c7b6f30f5552a';
  new_Lean_invocations=0;infinite_G0_complete=$false;new_D_N_bound=$false;victory=$false
})
$manifestHash = (Get-FileHash -LiteralPath (Join-Path $revisionDir 'source_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant()
Save-Json 'prepared_receipt.json' ([ordered]@{
  schema='round22.role3.kernel_revision02.prepared_receipt.v1';time=$now;
  status='PREPARED_SOURCE_ONLY_REQUEST_ROOT_FULL_SHA_REVIEW';source_manifest_sha256=$manifestHash;
  launcher_sha256=(Get-FileHash -LiteralPath (Join-Path $revisionDir 'run_revision02_once.py') -Algorithm SHA256).Hash.ToLowerInvariant();
  input_count=$inputs.Count;module_rows=$moduleRows;Lean_gate='CLOSED';new_compiler_calls=0;Python_math_calls=0;no_win=$true;
  metadata_command='native PowerShell execution of owned write_metadata.ps1 text';metadata_exit_credit='actual tool return required separately'
})
[ordered]@{status='REVISION02_PREPARED_SOURCE_ONLY';source_manifest_sha256=$manifestHash;input_count=$inputs.Count;module_rows=$moduleRows} | ConvertTo-Json -Depth 12
