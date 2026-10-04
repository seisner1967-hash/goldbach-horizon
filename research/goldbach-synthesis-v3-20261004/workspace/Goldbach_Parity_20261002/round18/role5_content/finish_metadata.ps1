$ErrorActionPreference = 'Stop'
$reviewRoot = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$reviewPath = Join-Path $reviewRoot 'round18\agent5_content.md'
$reviewText = [IO.File]::ReadAllText($reviewPath).Replace('(/D:/', '(D:/')
[IO.File]::WriteAllText($reviewPath, $reviewText, [Text.UTF8Encoding]::new($false))
$reviewInputs = @(
  'round18\agent1_calibrated_typeii.md',
  'round18\agent2_capacity_incidence.md',
  'round18\agent3_formalisation.md',
  'round18\agent4_formalisation.md',
  'round18\agent6.md',
  'round18\role3\final_receipt.json',
  'round18\role3\manifest.json',
  'round18\role4\final_receipt.json',
  'round18\role6_final_receipt.json',
  'round18\numeric_manifest.json',
  'round18\role6\numeric_summary.json',
  'round18\PROBE_BLOCK.md',
  'round18\previous_artifacts_sha256.json',
  'round18\role3\SeparatedTypeII.lean',
  'round18\role3\SeparatedTypeIIPrice.lean',
  'round18\role3\SeparatedTypeIICount.lean',
  'round18\role3\SeparatedTypeIILower.lean',
  'round18\role4\DoubleExtractionArithmetic.lean',
  'round18\role4\DividedFourForms.lean',
  'round18\role4\DividedRootCounts.lean',
  'round18\role4\DividedSelbergBridge.lean',
  'round18\role3\attempt01.log',
  'round18\role3\attempt02.log',
  'round18\role3\attempt04.log',
  'round18\role3\crt_attempt01.log',
  'round18\role3\crt_attempt02.log',
  'round18\role3\crt_attempt03.log',
  'round18\role3\crt_attempt04.log',
  'round18\role3\lower_attempt01.log',
  'round18\role3\lower_attempt02.log',
  'round18\role4\attempt01.log',
  'round18\role4\attempt03.log',
  'round18\role4\attempt05.log',
  'round18\role4\attempt06.log',
  'round18\role4\attempt07.log',
  'round18\role4\attempt09.log',
  'round18\role5_content\finish_metadata.ps1'
)
$reviewBindings = [ordered]@{}
foreach ($reviewInput in $reviewInputs) {
  $reviewFullPath = Join-Path $reviewRoot $reviewInput
  $reviewBindings[$reviewInput.Replace('\', '/')] = [ordered]@{
    sha256 = (Get-FileHash -LiteralPath $reviewFullPath -Algorithm SHA256).Hash.ToLowerInvariant()
    bytes = (Get-Item -LiteralPath $reviewFullPath).Length
  }
}
$reviewExpected = [ordered]@{
  'round18/agent1_calibrated_typeii.md' = '228766a630e37e4cee7f92bc46cb862582da59379b15653f4c00abcbc37313f0'
  'round18/agent2_capacity_incidence.md' = '48dbcc5875c140d6d4991fa7d6cd58749048e3cf151e35f476893c27f81ae595'
  'round18/agent3_formalisation.md' = 'b0d82b52621c6f57a1a34f24d3a422437847a685678e1b905aea2058062bcb62'
  'round18/agent4_formalisation.md' = '9f30e03fbfab99eeb88ef421e6f1dc35f1897383cc910b41ea9cdc661592b81d'
  'round18/agent6.md' = '95f54c20ebde7682b3ac1e4a78695ccf5ab79148322479379de8b27b44d80075'
  'round18/role3/SeparatedTypeII.lean' = '4513f3323bbf475b329daf423de805eb207d3fe88793f91016369bcb0d5228d7'
  'round18/role3/SeparatedTypeIIPrice.lean' = 'dd971712c281236332d272e645498b6ace83b6b6a80915b5f6bca4fa8cc2551c'
  'round18/role3/SeparatedTypeIICount.lean' = '55ac598030d5bd67202553a5a8ffffc6fcc2ba3aa796428808aecb9586d5d5d1'
  'round18/role3/SeparatedTypeIILower.lean' = '5676b1d3be3ae3595b59f5235b53b2813b72def907a855ef057bf940b519a68e'
  'round18/role4/DoubleExtractionArithmetic.lean' = 'be85b2d59e5af092e943e6714981997f372b1ad8a2e9ae14ab7153814a5e1f76'
  'round18/role4/DividedFourForms.lean' = '613dba073eb175ab7f96c588f0da1b7cf34844f197383e7cf3391078965bf68a'
  'round18/role4/DividedRootCounts.lean' = 'f7c4a4e4f2cad55275a37473a8d7e909497cf4dfd0d7e77f950ed55515655302'
  'round18/role4/DividedSelbergBridge.lean' = '2b5f1edaaab665560e5e1b6668f29794e3e10e2305b28428082f590458150db3'
}
foreach ($reviewKey in $reviewExpected.Keys) {
  if ($reviewBindings[$reviewKey].sha256 -ne $reviewExpected[$reviewKey]) {
    throw ('Frozen input SHA mismatch: ' + $reviewKey)
  }
}
function WriteReviewJsonExclusive($reviewTarget, $reviewObject) {
  $reviewStream = [IO.File]::Open($reviewTarget, [IO.FileMode]::CreateNew, [IO.FileAccess]::Write)
  $reviewWriter = [IO.StreamWriter]::new($reviewStream, [Text.UTF8Encoding]::new($false))
  try { $reviewWriter.Write(($reviewObject | ConvertTo-Json -Depth 8)) }
  finally { $reviewWriter.Dispose() }
}
$reviewManifest = [ordered]@{
  status = 'FROZEN_CONTENT_REVIEW_INPUTS'
  round = 18
  role = '5_content'
  timestamp_utc = [DateTime]::UtcNow.ToString('o')
  bound_input_count = $reviewBindings.Count
  source_SHA_matches_eight_frozen_inputs = $true
  FINAL_SHA_matches_five_frozen_inputs = $true
  scope = 'Source content review and stored diagnostics only; no compilation or mathematical recomputation'
  bindings = $reviewBindings
}
$reviewManifestPath = Join-Path $reviewRoot 'round18\role5_content\manifest.json'
WriteReviewJsonExclusive $reviewManifestPath $reviewManifest
$reviewReportHash = (Get-FileHash -LiteralPath $reviewPath -Algorithm SHA256).Hash.ToLowerInvariant()
$reviewManifestHash = (Get-FileHash -LiteralPath $reviewManifestPath -Algorithm SHA256).Hash.ToLowerInvariant()
$reviewReceipt = [ordered]@{
  status = 'FINAL_CONTENT_REVIEW_AUXILIARY_CONDITIONAL_NO_WIN'
  round = 18
  role = '5_content'
  finished_at_utc = [DateTime]::UtcNow.ToString('o')
  report = 'round18/agent5_content.md'
  report_sha256 = $reviewReportHash
  manifest = 'round18/role5_content/manifest.json'
  manifest_sha256 = $reviewManifestHash
  bound_inputs = $reviewBindings.Count
  eight_sources_fully_read = $true
  all_FINALs_1_2_3_4_6_read = $true
  line_numbers_verified = $true
  victory = $false
  global_D_N_controlled = $false
  official_counts_changed = $false
  independent_compilation_certified_by_this_role = $false
  new_hypothesis19_written = $false
  Lean_executions = 0
  numeric_producer_executions = 0
  kernel_executions = 0
  log_sign_executions = 0
  preflight_executions = 0
  PDF_executions = 0
  mathematical_audit_program_executions = 0
  old_997_files_written = 0
  metadata_shell_parse_failure_before_execution = 1
  mathematical_findings = @(
    'Actual adversarial product sum is reindexed to actual incidences; normalization assumes structural A>0 only'
    'R5 has independent arithmetic guards and is not a bound for prime Gamma or D_N'
    'H*ell calibration preserves the entire old adversarial sum in the price; R5 coprimality guard fails for calibrated H'
    'theta, raw Lambda and bilinear multiplicities remain separate'
    'New roots and Selberg weights are constructed on divided forms; rho4 only outside actualDelta'
    'Prime-log, source R4/R6, SS-to-rough interval bridge, uniform CRT+1 and parameter aggregation remain unproved here'
    'Written SS budget onset is 1e36; original source onset 1e24 and intermediate segment remain unpaid'
    'S minus SS, T_A unique assignment, aggregate Gamma and full ledger remain open'
  )
  compilation_failures_as_reported = 15
  failure_count_is_invocations_not_error_count = $true
  finite_numeric_observations = 'Read from frozen FINAL6 and numeric_summary only; not independently audited by this role'
}
$reviewReceiptPath = Join-Path $reviewRoot 'round18\role5_content\final_receipt.json'
WriteReviewJsonExclusive $reviewReceiptPath $reviewReceipt
[ordered]@{
  report_sha256 = $reviewReportHash
  manifest_sha256 = $reviewManifestHash
  receipt_sha256 = (Get-FileHash -LiteralPath $reviewReceiptPath -Algorithm SHA256).Hash.ToLowerInvariant()
  bound_inputs = $reviewBindings.Count
  victory = $false
} | ConvertTo-Json
