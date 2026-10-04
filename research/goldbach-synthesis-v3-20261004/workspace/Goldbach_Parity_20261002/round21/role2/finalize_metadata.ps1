$ErrorActionPreference = 'Stop'
$baseDir = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$ownedDir = Join-Path $baseDir 'round21\role2'
$cacheDir = 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib'
function Get-Sha([string]$filePath) { (Get-FileHash -LiteralPath $filePath -Algorithm SHA256).Hash.ToLowerInvariant() }
function Save-Json([string]$filePath, $data) {
  [System.IO.File]::WriteAllText($filePath, ($data | ConvertTo-Json -Depth 30) + [Environment]::NewLine,
    [System.Text.UTF8Encoding]::new($false))
}
$specifications = @(
  @('C:\Users\Utilisateur\.codex\skills\arbor-agent-ideate\SKILL.md','FULL','entire file','9699e2'),
  @((Join-Path $baseDir 'round21\PROBE_BLOCK.md'),'FULL','entire file','6d10b8'),
  @((Join-Path $baseDir '.arbor\sessions\parity\.coordinator\messages\round20_feedback.md'),'FULL','entire file','a8ab96'),
  @((Join-Path $baseDir 'round20\agent5_judge.md'),'FULL','entire file','3e388a'),
  @((Join-Path $baseDir 'round20\ideation_failure_feedback20_final.md'),'FULL','entire file','5f9301'),
  @((Join-Path $baseDir 'round20\agent2_friable.md'),'FULL','lines1..125 and126..end','a604e9,978ba6'),
  @((Join-Path $baseDir 'round20\role4\FriablePhysicalDemand.lean'),'FULL','entire file','c65085'),
  @((Join-Path $baseDir 'round20\role4\FriableDemandAggregation.lean'),'FULL','entire file','c65085'),
  @((Join-Path $baseDir 'round20\role4\FriablePhysicalPrefix.lean'),'FULL','entire file','236eb2'),
  @((Join-Path $baseDir 'round20\role4\FriablePhysicalPayment.lean'),'FULL','entire file','bddc79'),
  @((Join-Path $baseDir 'round20\role4\FriableSourceBudget.lean'),'FULL','entire file','941617'),
  @((Join-Path $baseDir 'round19\role4\NonSSBracketSwitch.lean'),'FULL','entire file','5789b1'),
  @((Join-Path $baseDir 'round20\role4_geometry\FriableSourceGeometry.lean'),'TARGETED','lines350..401 and rg declarations/geometry field references','ac08aa,089c82'),
  @((Join-Path $baseDir 'round19\role4\BalancedResourceSwitch.lean'),'TARGETED','lines1..110','43d222'),
  @((Join-Path $cacheDir 'NumberTheory\ArithmeticFunction.lean'),'TARGETED','rg zeta/sigma/multiplicative declarations and lines1311..1345','170104,4bfdf2'),
  @((Join-Path $cacheDir 'Algebra\Order\BigOperators\Ring\Finset.lean'),'TARGETED','rg moment declarations and lines154..195','033ed0,9c5efd'),
  @((Join-Path $cacheDir 'NumberTheory\Harmonic\Bounds.lean'),'TARGETED','rg harmonic_le_one_add_log and lines19..48','08efc6,704b76')
)
$entryList = foreach ($spec in $specifications) {
  [ordered]@{ path=$spec[0]; sha256=(Get-Sha $spec[0]); read_mode=$spec[1]; ranges=$spec[2]; observations=$spec[3]; bytes=(Get-Item -LiteralPath $spec[0]).Length }
}
$helperPath = 'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
$readReceipt = [ordered]@{
  kind='ROLE2_ROUND21_HONEST_READ_RECEIPT'; created_utc=[DateTime]::UtcNow.ToString('o');
  entries=$entryList; full_count=@($entryList | Where-Object read_mode -eq 'FULL').Count;
  targeted_count=@($entryList | Where-Object read_mode -eq 'TARGETED').Count;
  fresh_constraints=[ordered]@{ helper_path=$helperPath; helper_sha256=(Get-Sha $helperPath); command='python -B -X utf8 arbor_state.py view --cwd B --run-name parity --format constraints'; actual_exit_code=0; observation='e6bb4f'; output_read='FULL'; findings=37; pruned=5; max_depth=2; tree_not_mutated_by_ROLE2=$true };
  web=[ordered]@{ observation='functions.exec web search 109'; read_mode='TARGETED_SEARCH_RESULTS'; sources=@('https://terrytao.wordpress.com/wp-content/uploads/2009/01/whatsnew.pdf','https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Zeta.html'); full_pdf_read_claimed=$false; dependency_of_paper_proof=$false };
  execution_scope=[ordered]@{ arithmetic_Python_invocations=0; Lean_invocations=0; Judge_invocations=0; previous_PASS_replays=0; previous_file_mutations=0; readonly_helper_invocations=1; metadata_only_closure=$true };
  no_claim_of_FULL_for_unlisted_files=$true
}
Save-Json (Join-Path $ownedDir 'read_receipt.json') $readReceipt
$inputManifest = [ordered]@{ kind='ROLE2_ROUND21_READ_INPUT_MANIFEST'; entries=$entryList; helper_metadata_sha256=(Get-Sha $helperPath); raw_output_observation='e6bb4f'; no_math_execution=$true }
Save-Json (Join-Path $ownedDir 'input_manifest.json') $inputManifest
$ownedPaths = @(
  (Join-Path $baseDir 'round21\agent2_nonfriable.md'),
  (Join-Path $ownedDir 'lean_contract.md'),
  (Join-Path $ownedDir 'numeric_contract.md'),
  (Join-Path $ownedDir 'finalize_metadata.ps1'),
  (Join-Path $ownedDir 'read_receipt.json'),
  (Join-Path $ownedDir 'input_manifest.json')
)
$bindings = [ordered]@{}
foreach ($ownedPath in $ownedPaths) {
  $relative = $ownedPath.Substring($baseDir.Length + 1).Replace('\','/')
  $bindings[$relative] = Get-Sha $ownedPath
}
$frozenInputs = [ordered]@{}
foreach ($entry in $entryList) { $frozenInputs[$entry.path] = $entry.sha256 }
foreach ($entry in $entryList) {
  if ((Get-Sha $entry.path) -ne $entry.sha256) { throw 'Read input changed during metadata closure' }
}
$manifest = [ordered]@{ kind='ROLE2_ROUND21_FINAL_MANIFEST'; base=$baseDir; bindings=$bindings; read_inputs=$frozenInputs; readonly_helper_sha256=(Get-Sha $helperPath); no_math_execution=$true }
Save-Json (Join-Path $ownedDir 'final_manifest.json') $manifest
$finalReceipt = [ordered]@{
  status='FINAL2_IDEATION21_SOURCE_PARTIAL_PAYMENT_PROPOSED_NO_WIN'; created_utc=[DateTime]::UtcNow.ToString('o');
  ownership='round21/role2/** and round21/agent2_nonfriable.md'; actual_math_invocations=0; actual_Lean_invocations=0; actual_Judge_invocations=0;
  readonly_helper_exit_code=0; fresh_constraints_observation='e6bb4f'; source_onset='log N >= 10^24';
  proposed_new_cost='uniqueF0notF1Cost <= 35*N*u^(-14)'; proposed_extended_budget='sourceExtendedFriableCost <= N/(8192*u*ell)';
  proof_compiled=$false; numerical_test_executed=$false; score=0; victory=$false;
  report_sha256=(Get-Sha (Join-Path $baseDir 'round21\agent2_nonfriable.md'));
  lean_contract_sha256=(Get-Sha (Join-Path $ownedDir 'lean_contract.md'));
  numeric_contract_sha256=(Get-Sha (Join-Path $ownedDir 'numeric_contract.md'));
  read_receipt_sha256=(Get-Sha (Join-Path $ownedDir 'read_receipt.json'));
  input_manifest_sha256=(Get-Sha (Join-Path $ownedDir 'input_manifest.json'));
  final_manifest_sha256=(Get-Sha (Join-Path $ownedDir 'final_manifest.json'));
  all_read_inputs_unchanged_during_closure=$true; output_files_frozen=$true;
  unresolved=@('both-nonfriable complement','H19 whole-source bridge','full parents/capacity/Gamma/T_A union','six-post D_N ledger');
  no_old_artifact_written=$true
}
Save-Json (Join-Path $ownedDir 'final_receipt.json') $finalReceipt
$finalReceipt | ConvertTo-Json -Depth 20
[ordered]@{ final_receipt_sha256=(Get-Sha (Join-Path $ownedDir 'final_receipt.json')); metadata_only=$true } | ConvertTo-Json
