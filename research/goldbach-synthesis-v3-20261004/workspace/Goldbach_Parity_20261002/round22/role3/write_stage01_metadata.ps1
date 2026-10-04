$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$roleDir = Join-Path $taskBase 'round22\role3'
$utf8 = [System.Text.UTF8Encoding]::new($false)
function Save-Json($name, $value) {
  [IO.File]::WriteAllText((Join-Path $roleDir $name), ($value | ConvertTo-Json -Depth 30) + [Environment]::NewLine, $utf8)
}
$finalInputs = @(
  [ordered]@{path=(Join-Path $taskBase '.arbor\sessions\parity\experiments\16.1\executor_prompt.md');expected='ef1a3b96ec5c14d305b24f5405146c7997513b6f2fff27e89d9967e062c0faf2';read='FULL';chunk='94a2d4'},
  [ordered]@{path=(Join-Path $taskBase 'round22\agent2_operator.md');expected='be2a121cd14fe3513c9ee8ae28458a8a03f38957599d4a9bbba4e2174dbdcafe';read='FULL';chunk='ed84da'},
  [ordered]@{path=(Join-Path $taskBase 'round22\role2\uniform_formula.md');expected='720b8b2363c222321e7f50752591a8a5d0e992c119bfc3b4f445b9c80b7b7825';read='FULL';chunk='ec5e8a'},
  [ordered]@{path=(Join-Path $taskBase 'round22\role2\lean_contract.md');expected='9648829a0eb94f57f2a2e0e056836fac03e611d5a1d2fb21e4f453a04e953dbc';read='FULL';chunk='850f26'},
  [ordered]@{path=(Join-Path $taskBase 'round22\role2\numeric_contract.md');expected='943470e906efd8a77b2fbdbe50f001978e9bbaa9c20101f6ad379bcca9e03ebf';read='FULL';chunk='1f7117'}
)
foreach ($entry in $finalInputs) {
  $entry.sha256 = (Get-FileHash -LiteralPath $entry.path -Algorithm SHA256).Hash.ToLowerInvariant()
  if ($entry.sha256 -ne $entry.expected) { throw ('FINAL source hash mismatch: '+$entry.path) }
}
$now = [DateTimeOffset]::UtcNow.ToString('o')
Save-Json 'phase_read_receipts.json' ([ordered]@{schema='round22.role3.selected_read_receipts.v1';time=$now;selection='16.1_ACTUAL_ROOT_f89dcf_EXIT0';entries=$finalInputs;actual_FULL=5;preparation_reads_manifest_sha256='1ccf7fb13d2f33080f4b23201d9c2480f0e7349d0cd7f66ea307ac9e3c2efd05';additional_targeted_sources=@([ordered]@{path='Mathlib/Data/Int/Interval.lean';range='71-89';chunk='435706'},[ordered]@{path='Mathlib/Topology/Algebra/InfiniteSum/Basic.lean';range='108-137';chunk='53c4b2'},[ordered]@{path='Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean';range='159-189';chunk='022b89'});compiler_calls=0;Python_math_calls=0;old_PASS_replays=0})
$inputPaths = @($finalInputs | ForEach-Object {$_.path}) + @(
  (Join-Path $taskBase 'round22\USER_DIRECTIVE.md'),
  (Join-Path $taskBase 'round22\PROBE_BLOCK.md'),
  (Join-Path $roleDir 'EpsteinKernel22.lean'),
  (Join-Path $roleDir 'run_stage_once.py'),
  (Join-Path $roleDir 'phase_read_receipts.json'),
  (Join-Path $roleDir 'stage01_preparation.md'),
  (Join-Path $roleDir 'api_plan.md'),
  (Join-Path $roleDir 'preparation_readonly.md'),
  (Join-Path $roleDir 'input_manifest.json'),
  (Join-Path $roleDir 'read_receipts.json'),
  (Join-Path $roleDir 'preparation_manifest.json'),
  (Join-Path $roleDir 'preparation_receipt.json'),
  (Join-Path $roleDir 'write_preparation_metadata.ps1'),
  (Join-Path $roleDir 'write_stage01_metadata.ps1')
)
$inputs = @($inputPaths | ForEach-Object {[ordered]@{path=$_;sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}})
$moduleRows = @('EpsteinKernel22') | ForEach-Object {
  $src = Join-Path $roleDir ($_+'.lean')
  $body = [IO.File]::ReadAllText($src)
  [ordered]@{module=$_;path=$src;sha256=(Get-FileHash -LiteralPath $src -Algorithm SHA256).Hash.ToLowerInvariant();theorem_count=([regex]::Matches($body,'(?m)^theorem\s+')).Count;definition_count=([regex]::Matches($body,'(?m)^def\s+')).Count;axiom_print_count=([regex]::Matches($body,'(?m)^#print axioms Epstein22\.')).Count;status='SOURCE_ONLY_UNCOMPILED'}
}
Save-Json 'stage01_source_manifest.json' ([ordered]@{schema='round22.role3.author_stage01.source_manifest.v1';time=$now;stage='G0_KERNEL_STAGE01';node_id='16.1';modules=@('EpsteinKernel22');module_rows=@($moduleRows);inputs=$inputs;scope='SUBSTANTIVE_G0_KERNEL_ONLY_FINITE_WINDOW_STILL_PREPARING';actual_Lean_invocations=0;infinite_G0_complete=$false;new_D_N_bound=$false;victory=$false})
$manifestHash = (Get-FileHash -LiteralPath (Join-Path $roleDir 'stage01_source_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant()
Save-Json 'stage01_prepared_receipt.json' ([ordered]@{schema='round22.role3.author_stage01.prepared_receipt.v1';time=$now;status='PREPARED_SOURCE_ONLY_REQUEST_ROOT_FULL_SHA_REVIEW';source_manifest_sha256=$manifestHash;launcher_sha256=(Get-FileHash -LiteralPath (Join-Path $roleDir 'run_stage_once.py') -Algorithm SHA256).Hash.ToLowerInvariant();input_count=$inputs.Count;module_rows=@($moduleRows);Lean_gate='CLOSED';compiler_calls=0;Python_math_calls=0;no_win=$true;metadata_command='native PowerShell command executing owned write_stage01_metadata.ps1 text';metadata_exit_credit='actual tool return required separately'})
[ordered]@{status='PREPARED_SOURCE_ONLY';source_manifest_sha256=$manifestHash;input_count=$inputs.Count;module_rows=@($moduleRows)} | ConvertTo-Json -Depth 12
