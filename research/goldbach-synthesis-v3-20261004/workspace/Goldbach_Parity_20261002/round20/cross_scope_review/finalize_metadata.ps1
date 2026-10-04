$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$taskOwned = Join-Path $taskBase 'round20\cross_scope_review'
$taskFull = @(
  'round20\agent1_switched_composite.md',
  'round20\agent2_friable.md',
  'round20\agent3_formalisation.md',
  'round20\agent4_formalisation.md',
  'round20\ideation_failure_feedback20_final.md',
  'round20\role3\OddBonferroniArithmetic.lean',
  'round20\role3\LeastFactorComposite.lean',
  'round20\role3\SwitchedSelbergWeight.lean',
  'round20\role3\PhysicalCompositeSubtraction.lean',
  'round20\role3\CompositeAPConductor.lean',
  'round20\role3\SwitchedIncidenceEstimator.lean',
  'round20\role4\FriableSourceBudget.lean'
)
$taskTargeted = @(
  @{path='round20\role4\FriableDemandAggregation.lean'; ranges=@('1-44'); scope='Targeted definition read plus declaration search; not FULL'},
  @{path='round20\role4\FriablePhysicalPayment.lean'; ranges=@('167-182','336-338'); scope='Targeted definition read plus declaration search; not FULL'},
  @{path='round20\role4_geometry\FriableSourceGeometry.lean'; ranges=@('1-35'); scope='Targeted source-parameter read plus partial declaration search; not FULL'}
)
$taskReadEntries = @()
foreach ($taskRel in $taskFull) {
  $taskAbs = Join-Path $taskBase $taskRel
  $taskReadEntries += [ordered]@{
    path=$taskRel; sha256=(Get-FileHash -LiteralPath $taskAbs -Algorithm SHA256).Hash.ToLowerInvariant()
    read_mode='FULL'; ranges=@('entire file'); bytes=(Get-Item -LiteralPath $taskAbs).Length
  }
}
foreach ($taskEntry in $taskTargeted) {
  $taskAbs = Join-Path $taskBase $taskEntry.path
  $taskReadEntries += [ordered]@{
    path=$taskEntry.path; sha256=(Get-FileHash -LiteralPath $taskAbs -Algorithm SHA256).Hash.ToLowerInvariant()
    read_mode='TARGETED'; ranges=$taskEntry.ranges; scope=$taskEntry.scope
    bytes=(Get-Item -LiteralPath $taskAbs).Length
  }
}
$taskManifest = [ordered]@{
  kind='ROUND20_CROSS_SCOPE_REVIEW_READ_INPUTS'; created_utc=[DateTime]::UtcNow.ToString('o')
  base=$taskBase; actual_body_inputs_only=$true; full_count=$taskFull.Count
  targeted_count=$taskTargeted.Count; entries=$taskReadEntries
  no_claimed_full_for_targeted_inputs=$true
}
$taskManifestPath = Join-Path $taskOwned 'input_manifest.json'
$taskManifest | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $taskManifestPath -Encoding UTF8
$taskUnchanged = $true
foreach ($taskEntry in $taskReadEntries) {
  $taskHashAfter=(Get-FileHash -LiteralPath (Join-Path $taskBase $taskEntry.path) -Algorithm SHA256).Hash.ToLowerInvariant()
  if ($taskHashAfter -ne $taskEntry.sha256) { $taskUnchanged=$false }
}
if (-not $taskUnchanged) { throw 'A read input changed during metadata closure.' }
$taskOutputs = @('inventory.md','input_manifest.json','finalize_metadata.ps1')
$taskOutputHashes = [ordered]@{}
foreach ($taskOutput in $taskOutputs) {
  $taskOutputHashes[$taskOutput]=(Get-FileHash -LiteralPath (Join-Path $taskOwned $taskOutput) -Algorithm SHA256).Hash.ToLowerInvariant()
}
$taskReceipt = [ordered]@{
  kind='ROUND20_CROSS_SCOPE_REVIEW_FINAL'; created_utc=[DateTime]::UtcNow.ToString('o')
  owner='/root/round20_cross_scope_review'; status='FINAL_READONLY_SCOPE_INVENTORY'
  input_files=15; full_files=12; targeted_files=3; post_metadata_inputs_unchanged=$taskUnchanged
  new_math_executions=0; lean_invocations=0; numeric_replay=0; judge_invocations=0
  source_changes=0; frozen_artifact_changes=0; ideate_drafts=0; tree_mutations=0
  independent_compiler_verdict=$false; victory=$false
  mathematical_statement_contradiction_identified=$false
  quantitative_B6_proved_in_read_role3_sources=$false
  source_M0_bridge_proved_in_read_role3_sources=$false
  cross_track_bridge_present_in_read_final_sources=$false
  result='B1/B2/B3/B5 auxiliary identities; source friable partial budget; open frame/reference/AP/distribution/ledger bridges'
  output_sha256=$taskOutputHashes
}
$taskReceiptPath=Join-Path $taskOwned 'final_receipt.json'
$taskReceipt | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $taskReceiptPath -Encoding UTF8
$taskDisplay=[ordered]@{
  status=$taskReceipt.status; input_files=15; full_files=12; targeted_files=3
  post_metadata_inputs_unchanged=$taskUnchanged; output_sha256=$taskOutputHashes
  receipt_sha256=(Get-FileHash -LiteralPath $taskReceiptPath -Algorithm SHA256).Hash.ToLowerInvariant()
}
$taskDisplay | ConvertTo-Json -Depth 5
