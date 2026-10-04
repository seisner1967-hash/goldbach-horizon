$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$roleDir = Join-Path $taskBase 'round22\role3'
$libBase = 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib'
$utf8 = [System.Text.UTF8Encoding]::new($false)
function Save-Json($name, $value) {
  [System.IO.File]::WriteAllText((Join-Path $roleDir $name), ($value | ConvertTo-Json -Depth 30) + [Environment]::NewLine, $utf8)
}
function Make-Input($path, $scope, $chunks, $ranges, $status) {
  [ordered]@{path=$path; sha256=(Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant(); scope=$scope; source_read_chunks=$chunks; ranges=$ranges; status=$status; hash_capture_kind='READ_ONLY_METADATA_SNAPSHOT_AT_REPORT_NOT_PREEXEC'}
}
$entries = @(
  (Make-Input (Join-Path $taskBase 'round22\USER_DIRECTIVE.md') 'FULL' @('273454') @() 'FIXED_DIRECTIVE'),
  (Make-Input (Join-Path $taskBase 'round22\PROBE_BLOCK.md') 'FULL' @('6fa232') @() 'FIXED_PROBE'),
  (Make-Input 'C:\Users\Utilisateur\.codex\skills\arbor-agent-executor\SKILL.md' 'FULL' @('926fa9') @() 'READ_WORKFLOW_ONLY_MISSION_OVERRIDES_EXECUTION'),
  (Make-Input (Join-Path $taskBase 'round22\role2\uniform_formula.md') 'FULL' @('8608ab') @() 'DRAFT_NOT_SELECTED_NOT_FINAL'),
  (Make-Input (Join-Path $libBase 'Analysis\SpecialFunctions\Sqrt.lean') 'FULL' @('2745d1') @() 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'MeasureTheory\Integral\Periodic.lean') 'FULL' @('9a76db') @() 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'Analysis\NormedSpace\FunctionSeries.lean') 'FULL' @('00f3c7') @() 'SOURCE_ONLY'),
  (Make-Input (Join-Path $taskBase 'round22\role6\epstein_contract22.json') 'FULL' @('1080b6') @() 'PREPARED_DRAFT_NOT_EXECUTED'),
  (Make-Input (Join-Path $taskBase 'round22\role6\epstein_bank22.py') 'FULL' @('991d66') @() 'PREPARED_DRAFT_NOT_EXECUTED'),
  (Make-Input (Join-Path $libBase 'Data\Real\Sqrt.lean') 'TARGETED_SEARCH' @('e2bc03') @('sqrt algebra theorem-name matches') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'MeasureTheory\Integral\FundThmCalculus.lean') 'TARGETED' @('134254') @('1100-1184') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'MeasureTheory\Integral\IntervalIntegral.lean') 'TARGETED' @('9efebd','71fe12','73d6af','f841e1') @('621-715','790-859','1041-1113','526-551') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'MeasureTheory\Integral\DominatedConvergence.lean') 'TARGETED' @('8b8ac1') @('99-168') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'MeasureTheory\Integral\IntegralEqImproper.lean') 'TARGETED' @('c4a462','d0df15') @('781-862','912-1013') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'MeasureTheory\Integral\SetIntegral.lean') 'TARGETED' @('37a158') @('278-319') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'Topology\Algebra\InfiniteSum\NatInt.lean') 'TARGETED' @('326557') @('437-520') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'Algebra\BigOperators\Group\Finset.lean') 'TARGETED' @('6667b4') @('1464-1501') 'SOURCE_ONLY_TO_ADDITIVE_NAMES_UNPROBED'),
  (Make-Input (Join-Path $libBase 'Analysis\PSeries.lean') 'TARGETED' @('d688fa') @('285-330') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'Analysis\SpecialFunctions\ImproperIntegrals.lean') 'TARGETED' @('3f1182') @('31-116') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'Analysis\Normed\Group\Tannery.lean') 'TARGETED' @('fd19cb') @('1-195 requested; actual short file returned') 'SOURCE_ONLY_NOT_CREDITED_FULL'),
  (Make-Input (Join-Path $libBase 'Analysis\SpecialFunctions\JapaneseBracket.lean') 'TARGETED' @('c7ee6f') @('129-173') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'MeasureTheory\Measure\Lebesgue\Integral.lean') 'TARGETED' @('edf734') @('1-138') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'Analysis\SpecialFunctions\Pow\Real.lean') 'TARGETED' @('202cd8','1320c1') @('182-245','948-972') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'Topology\Algebra\InfiniteSum\Basic.lean') 'TARGETED' @('9c0faa','1e6600') @('1-90','446-474') 'SOURCE_ONLY_TO_ADDITIVE_NAMES_UNPROBED'),
  (Make-Input (Join-Path $libBase 'Analysis\SumIntegralComparisons.lean') 'TARGETED' @('8bfe7f') @('1-148') 'SOURCE_ONLY'),
  (Make-Input (Join-Path $libBase 'NumberTheory\LSeries\RiemannZeta.lean') 'TARGETED' @('90317f') @('175-205') 'SOURCE_ONLY')
)
$captureTime = [DateTimeOffset]::UtcNow.ToString('o')
Save-Json 'input_manifest.json' ([ordered]@{schema='round22.role3.readonly_inputs.v1';captured_at=$captureTime;input_count=$entries.Count;entries=$entries;purpose='API preparation only; any FINAL source change requires fresh read/binding before execution'})
Save-Json 'read_receipts.json' ([ordered]@{schema='round22.role3.read_receipts.v1';captured_at=$captureTime;actual_FULL=(@($entries | Where-Object {$_.scope -eq 'FULL'})).Count;actual_TARGETED_or_SEARCH=(@($entries | Where-Object {$_.scope -ne 'FULL'})).Count;credited_reads=$entries;truncated_searches_not_FULL=@('d45bbe','1cd67b','b3ab0e');missing_path_discovery_not_API_failure=@('570d0f','9cab0c','eaad2b');source_read_only=$true;compiler_calls=0;api_probe_calls=0;math_python_calls=0;new_proof_sources=0;old_result_replays=0})
$ownNames = @('api_plan.md','preparation_readonly.md','input_manifest.json','read_receipts.json','write_preparation_metadata.ps1')
$own = @($ownNames | ForEach-Object {[ordered]@{path=(Join-Path $roleDir $_);sha256=(Get-FileHash -LiteralPath (Join-Path $roleDir $_) -Algorithm SHA256).Hash.ToLowerInvariant()}})
Save-Json 'preparation_manifest.json' ([ordered]@{schema='round22.role3.preparation_artifacts.v1';captured_at=$captureTime;status='READ_ONLY_PREPARATION_READY';bindings=$own;scope='AUX_API_PLAN_ONLY_NOT_SELECTED_NOT_EXECUTED';self_and_receipt_excluded=$true})
Save-Json 'preparation_receipt.json' ([ordered]@{schema='round22.role3.preparation_receipt.v1';captured_at=$captureTime;status='READ_ONLY_PREPARATION_READY';writer_command='native PowerShell command: & ([scriptblock]::Create([IO.File]::ReadAllText(abs role3 writer path)))';writer_exit_claim='actual tool result required separately';previous_script_launcher_failure=[ordered]@{chunk='499d11';exit_code=1;cause='local PowerShell script execution policy; no writer action executed';not_math_failure=$true};input_manifest_sha256=(Get-FileHash -LiteralPath (Join-Path $roleDir 'input_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant();preparation_manifest_sha256=(Get-FileHash -LiteralPath (Join-Path $roleDir 'preparation_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant();compiler_calls=0;math_python_calls=0;proof_sources_written=0;selected_FINAL2=$false;victory=$false})
[ordered]@{status='READ_ONLY_PREPARATION_READY';inputs=$entries.Count;FULL=(@($entries|Where-Object {$_.scope -eq 'FULL'})).Count;TARGETED_or_SEARCH=(@($entries|Where-Object {$_.scope -ne 'FULL'})).Count;own_bindings=$own.Count;compiled_modules=0;compiled_theorems=0;manifest_sha256=(Get-FileHash -LiteralPath (Join-Path $roleDir 'preparation_manifest.json') -Algorithm SHA256).Hash.ToLowerInvariant()} | ConvertTo-Json
