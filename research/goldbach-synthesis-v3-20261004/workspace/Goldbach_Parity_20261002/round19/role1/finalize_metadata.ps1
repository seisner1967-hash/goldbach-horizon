# Metadata only. No numerical producer, compiler, kernel, AP, log or sign evaluation.
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$researchRoot = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$roundRoot = Join-Path $researchRoot 'round19'
$ownedRoot = Join-Path $roundRoot 'role1'
$reportPath = Join-Path $roundRoot 'agent1_weighted_aggregate.md'
$manifestPath = Join-Path $ownedRoot 'manifest.json'
$receiptPath = Join-Path $ownedRoot 'final_receipt.json'
if ((Test-Path -LiteralPath $manifestPath) -or (Test-Path -LiteralPath $receiptPath)) {
  throw 'Refusing to overwrite frozen final metadata.'
}
$utf8 = [System.Text.UTF8Encoding]::new($false)
$reportText = [System.IO.File]::ReadAllText($reportPath)
$labels = [regex]::Matches($reportText, '(?m)^(Mechanism|Hypothesis|Observable|Conflicts):')
if ($labels.Count -ne 4) { throw 'Expected exactly four hypothesis lines.' }
$inputs = @(
 'round19/PROBE_BLOCK.md',
 '.arbor/sessions/parity/.coordinator/messages/round18_feedback.md',
 'round18/agent1_calibrated_typeii.md',
 'round18/agent3_formalisation.md',
 'round18/agent5.md',
 'round18/agent5_content.md',
 'round15/agent1_weighted_incidence.md',
 'round12/agent1_compensation.md',
 'round12/agent2_bilateral.md',
 'round18/role3/SeparatedTypeII.lean'
)
$bindings = [ordered]@{}
foreach ($relativePath in $inputs) {
  $inputPath = Join-Path $researchRoot $relativePath
  $bindings[$relativePath] = [ordered]@{
    sha256 = (Get-FileHash -LiteralPath $inputPath -Algorithm SHA256).Hash.ToLowerInvariant()
    bytes = (Get-Item -LiteralPath $inputPath).Length
    disposition = 'read_only_reference'
  }
}
foreach ($relativePath in @('round19/agent1_weighted_aggregate.md','round19/role1/finalize_metadata.ps1')) {
  $inputPath = Join-Path $researchRoot $relativePath
  $bindings[$relativePath] = [ordered]@{
    sha256 = (Get-FileHash -LiteralPath $inputPath -Algorithm SHA256).Hash.ToLowerInvariant()
    bytes = (Get-Item -LiteralPath $inputPath).Length
    disposition = 'owned_final'
  }
}
$manifest = [ordered]@{
  role = 'round19_role1_ideation'
  status = 'FINAL_CONCEPTUAL_NO_WIN'
  bindings = $bindings
  metadata_only = $true
  mathematical_execution_count = 0
  numerical_producer_count = 0
  lean_invocation_count = 0
  node_selection_count = 0
}
[System.IO.File]::WriteAllText($manifestPath, ($manifest | ConvertTo-Json -Depth 8) + [Environment]::NewLine, $utf8)
$receipt = [ordered]@{
  status = 'FINAL_CONCEPTUAL_NO_WIN'
  frozen_at_utc = [DateTimeOffset]::UtcNow.ToString('o')
  report_sha256 = $bindings['round19/agent1_weighted_aggregate.md'].sha256
  manifest_sha256 = (Get-FileHash -LiteralPath $manifestPath -Algorithm SHA256).Hash.ToLowerInvariant()
  finalizer_sha256 = $bindings['round19/role1/finalize_metadata.ps1'].sha256
  bound_files = $bindings.Count
  mechanism = 'rank_three_face_calibration_and_factor_split_AP_price'
  victory = $false
  source_bound_written_only = $true
  gamma_rank_unestimated = $true
  BV_onset_uncomputed = $true
  protected_archives_written = $false
  outputs_immutable_after_final = $true
  constraints_read = [ordered]@{
    findings = 33
    pruned = 5
    max_depth = 2
    stdout_encoding_failure_chunk = '8e99df'
    successful_utf8_full_read_chunk = '02761a'
    failure_kind = 'reader_encoding_only_not_mathematical'
  }
  primary_source = 'https://arxiv.org/pdf/math/0506067'
}
[System.IO.File]::WriteAllText($receiptPath, ($receipt | ConvertTo-Json -Depth 8) + [Environment]::NewLine, $utf8)
[ordered]@{
  status = 'FINAL_METADATA_WRITTEN'
  report_sha256 = $receipt.report_sha256
  manifest_sha256 = $receipt.manifest_sha256
  receipt_sha256 = (Get-FileHash -LiteralPath $receiptPath -Algorithm SHA256).Hash.ToLowerInvariant()
  bound_files = $bindings.Count
} | ConvertTo-Json -Depth 4
