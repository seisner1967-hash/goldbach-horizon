param([string] $Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
$ErrorActionPreference = 'Stop'
$RoundRoot = $PSScriptRoot
$JudgeRoot = Join-Path $RoundRoot 'judge'
$Utf8 = [System.Text.UTF8Encoding]::new($false)
$Before = & (Join-Path $RoundRoot 'verify-frozen.ps1')
if (@(Get-ChildItem -LiteralPath $RoundRoot -Filter '*.lean' -Recurse -File).Count -ne 0) {
    throw 'Round 8 admits no new Lean source; an auxiliary substitution is not accepted'
}
$InputsPath = Join-Path $JudgeRoot 'input_sha256.json'
$Inputs = Get-Content -LiteralPath $InputsPath -Raw | ConvertFrom-Json -AsHashtable
if ($Inputs.role_reports -ne 5 -or $Inputs.numerical_sources -ne 3) { throw 'Final five-role freeze is required' }
foreach ($Entry in $Inputs.sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath (Join-Path $RoundRoot $Entry.Key) -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Final production input changed: $($Entry.Key)" }
}
foreach ($Entry in $Inputs.external_sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath $Entry.Key -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Original external PDF changed: $($Entry.Key)" }
}
$StatusByStem = [ordered]@{
    compensation = 'PASS_EXACT_IDENTITIES_ONLY'
    native_gram = 'PASS_ALGEBRA_ONLY'
    head_regrouping = 'PASS_HEAD_IDENTITY_ONLY'
}
$Gates = [System.Collections.Generic.List[object]]::new()
foreach ($Stem in $StatusByStem.Keys) {
    $Path = Join-Path $RoundRoot "$Stem.json"
    $Gate = Get-Content -LiteralPath $Path -Raw | ConvertFrom-Json -AsHashtable
    if ($Gate.status -ne $StatusByStem[$Stem] -or $Gate.N -ne 100000000) { throw "Unexpected numeric gate: $Path" }
    if ($Gate.script_sha256 -ne $Inputs.sha256["$($Stem)_checks.py"]) { throw "Stale gate source hash: $Path" }
    $Gates.Add([ordered]@{ path = $Path; status = $Gate.status; N = $Gate.N
        sha256 = $Inputs.sha256["$Stem.json"]; script_sha256 = $Gate.script_sha256 })
}
$ReplayPath = Join-Path $JudgeRoot 'numerical\replay.py'
$RawOutput = & $Python $ReplayPath 2>&1
$ReplayExit = $LASTEXITCODE
$ReplayLog = Join-Path $JudgeRoot 'numerical_replay.log'
[System.IO.File]::WriteAllText($ReplayLog, (($RawOutput | ForEach-Object { [string]$_ }) -join "`n") + "`n", $Utf8)
if ($ReplayExit -ne 0) { throw "Independent replay failed (exit $ReplayExit); read $ReplayLog" }
$ReplayReceiptPath = Join-Path $JudgeRoot 'numerical\replay_receipt.json'
$ReplayReceipt = Get-Content -LiteralPath $ReplayReceiptPath -Raw | ConvertFrom-Json -AsHashtable
if ($ReplayReceipt.status -ne 'PASS_EXACT_REPLAY' -or $ReplayReceipt.lean_invoked -ne $false) {
    throw 'Unexpected replay status or Lean invocation'
}
$After = & (Join-Path $RoundRoot 'verify-frozen.ps1')
foreach ($Entry in $Inputs.sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath (Join-Path $RoundRoot $Entry.Key) -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Production input changed during audit: $($Entry.Key)" }
}
foreach ($Entry in $Inputs.external_sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath $Entry.Key -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Original PDF changed during audit: $($Entry.Key)" }
}
$Receipt = [ordered]@{
    round = 8; status = 'PARTIAL_HEAD_GAIN_WITH_OPEN_SIGNED_REMAINDER'; victory = $false; score = 0
    native_gram_candidate = 'REJECTED_BEFORE_COMPILATION_MISSING_WEIGHTED_ARITHMETIC_ESTIMATE'
    lean_invoked = $false; compiler_exit_code = $null; new_lean_modules = 0; new_lean_conclusions = 0
    previous_auxiliary_modules = 9; previous_auxiliary_conclusions = 116
    recorded_at_utc = [DateTime]::UtcNow.ToString('o')
    input_manifest = $InputsPath
    input_manifest_sha256 = (Get-FileHash -LiteralPath $InputsPath -Algorithm SHA256).Hash.ToLowerInvariant()
    source_sha256 = $Inputs.sha256; external_source_sha256 = $Inputs.external_sha256
    numerical_gates = @($Gates.ToArray())
    judge_scripts_sha256 = [ordered]@{
        'audit-judge.ps1' = (Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash.ToLowerInvariant()
        'verify-frozen.ps1' = (Get-FileHash -LiteralPath (Join-Path $RoundRoot 'verify-frozen.ps1') -Algorithm SHA256).Hash.ToLowerInvariant()
        'replay.py' = (Get-FileHash -LiteralPath $ReplayPath -Algorithm SHA256).Hash.ToLowerInvariant()
    }
    numerical_replay = [ordered]@{ status = $ReplayReceipt.status; exit_code = $ReplayExit
        receipt = $ReplayReceiptPath
        receipt_sha256 = (Get-FileHash -LiteralPath $ReplayReceiptPath -Algorithm SHA256).Hash.ToLowerInvariant()
        log = $ReplayLog; log_sha256 = (Get-FileHash -LiteralPath $ReplayLog -Algorithm SHA256).Hash.ToLowerInvariant() }
    source_onset = $ReplayReceipt.source_onset
    preserved_previous_artifacts_before = $Before; preserved_previous_artifacts_after = $After
    analytical_head = 'Written qualitative independent bound; new BV calibration and common threshold not evaluated; no Lean certificate'
    analytical_source_domain = 'Acquired adaptive inputs u >= 10^24 with original premises; N=1e8 finite diagnostics only'
    unresolved_obligation = 'R16: long physical minus complete matching model, plus 2 max(e,0); effective head fees calibration still required'
    scope = 'Exact identities retained; specific separability/tail/support shortcuts falsified; no general impossibility inferred'
}
[System.IO.File]::WriteAllText((Join-Path $RoundRoot 'judge_receipt.json'), ($Receipt | ConvertTo-Json -Depth 12) + "`n", $Utf8)
Write-Output 'Round 8: three isolated exact replays and source-page reproduction passed; 227 previous artifacts preserved; no Lean invoked; victory=false.'
Write-Output 'Score: 0'
