param([string] $Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
$ErrorActionPreference = 'Stop'
$JudgeRoot = $PSScriptRoot
$RoundRoot = Split-Path -Parent $JudgeRoot
$Utf8 = [System.Text.UTF8Encoding]::new($false)
$Before = & (Join-Path $JudgeRoot 'verify-frozen.ps1') -Python $Python
if (@(Get-ChildItem -LiteralPath $RoundRoot -Filter '*.lean' -Recurse -File).Count -ne 0) {
    throw 'Round 9 admits no new Lean source or auxiliary substitution'
}
$InputsPath = Join-Path $JudgeRoot 'input_sha256.json'
$Inputs = Get-Content -LiteralPath $InputsPath -Raw | ConvertFrom-Json -AsHashtable
if ($Inputs.role_reports -ne 5 -or $Inputs.numerical_sources -ne 1 -or
    $Inputs.role3_completion_sha256 -ne $Inputs.sha256['agent3_contract_audit.md']) {
    throw 'Final five-role freeze and role-3 completion hash are required'
}
foreach ($Entry in $Inputs.sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath (Join-Path $RoundRoot $Entry.Key) -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Final production input changed: $($Entry.Key)" }
}
foreach ($Entry in $Inputs.external_sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath $Entry.Key -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Original external PDF changed: $($Entry.Key)" }
}
$GatePath = Join-Path $RoundRoot 'new_contracts.json'
$Gate = Get-Content -LiteralPath $GatePath -Raw | ConvertFrom-Json -AsHashtable
if ($Gate.status -ne 'FINITE_NEW_CONTRACT_CHECKS_ONLY' -or $Gate.N -ne 100000000 -or
    $Gate.script_sha256 -ne $Inputs.sha256['new_contract_checks.py']) { throw 'Unexpected new contract gate or stale source hash' }
$ReplayPath = Join-Path $JudgeRoot 'numerical\replay.py'
$RawOutput = & $Python $ReplayPath 2>&1
$ReplayExit = $LASTEXITCODE
$ReplayLog = Join-Path $JudgeRoot 'numerical_replay.log'
[System.IO.File]::WriteAllText($ReplayLog, (($RawOutput | ForEach-Object { [string]$_ }) -join "`n") + "`n", $Utf8)
if ($ReplayExit -ne 0) { throw "Independent replay failed (exit $ReplayExit); read $ReplayLog" }
$ReplayReceiptPath = Join-Path $JudgeRoot 'numerical\replay_receipt.json'
$ReplayReceipt = Get-Content -LiteralPath $ReplayReceiptPath -Raw | ConvertFrom-Json -AsHashtable
if ($ReplayReceipt.status -ne 'PASS_EXACT_REPLAY' -or $ReplayReceipt.lean_invoked -ne $false) { throw 'Unexpected replay result or Lean invocation' }
$After = & (Join-Path $JudgeRoot 'verify-frozen.ps1') -Python $Python
foreach ($Entry in $Inputs.sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath (Join-Path $RoundRoot $Entry.Key) -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Production input changed during audit: $($Entry.Key)" }
}
foreach ($Entry in $Inputs.external_sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath $Entry.Key -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Original PDF changed during audit: $($Entry.Key)" }
}
$Receipt = [ordered]@{
    round = 9; status = 'PARTIAL_PAYMENTS_WITH_OPEN_PRIME_SIGNED_MOMENT'; victory = $false; score = 0
    lean_invoked = $false; compiler_exit_code = $null; new_lean_modules = 0; new_lean_conclusions = 0
    previous_auxiliary_modules = 9; previous_auxiliary_conclusions = 116
    recorded_at_utc = [DateTime]::UtcNow.ToString('o')
    input_manifest = $InputsPath
    input_manifest_sha256 = (Get-FileHash -LiteralPath $InputsPath -Algorithm SHA256).Hash.ToLowerInvariant()
    role3_completion_sha256 = $Inputs.role3_completion_sha256
    source_sha256 = $Inputs.sha256; external_source_sha256 = $Inputs.external_sha256
    numerical_gate = [ordered]@{
        path = $GatePath; status = $Gate.status; sha256 = $Inputs.sha256['new_contracts.json']
        source_sha256 = $Gate.script_sha256; contract_statuses = $ReplayReceipt.contract_statuses
        properpower_analytic_payment_tested = $false
    }
    numerical_replay = [ordered]@{
        status = $ReplayReceipt.status; exit_code = $ReplayExit; all_fields_equal = $true; all_bytes_equal = $true
        receipt = $ReplayReceiptPath
        receipt_sha256 = (Get-FileHash -LiteralPath $ReplayReceiptPath -Algorithm SHA256).Hash.ToLowerInvariant()
        log = $ReplayLog; log_sha256 = (Get-FileHash -LiteralPath $ReplayLog -Algorithm SHA256).Hash.ToLowerInvariant()
    }
    judge_scripts_sha256 = [ordered]@{
        'audit-judge.ps1' = (Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash.ToLowerInvariant()
        'verify-frozen.ps1' = (Get-FileHash -LiteralPath (Join-Path $JudgeRoot 'verify-frozen.ps1') -Algorithm SHA256).Hash.ToLowerInvariant()
        'replay.py' = (Get-FileHash -LiteralPath $ReplayPath -Algorithm SHA256).Hash.ToLowerInvariant()
    }
    source54 = $ReplayReceipt.source54
    preserved_previous_artifacts_before = $Before; preserved_previous_artifacts_after = $After
    written_partial_payments = [ordered]@{
        J3 = 'Effective harmonic-face allowance at source u >= 10^24; weaker exponent explicitly distinguished'
        J4 = 'Qualitative physical-band allowance; extra BV threshold unevaluated'
        W12 = 'First-axis proper-power positive bound effective for u >= 65536; no Lean certificate'
    }
    ledger_routes = [ordered]@{
        original_H = 'B_H = P_tail^H - M_alpha; W12 initial application, with its own head'
        raised_a9 = 'B_a9 = P^a9 - M_a9; separate raised-face route J5'
        fee_rule = 'No summation of the two ledgers or equality of their signed proper-power pieces; one direct uniform-positive W11/W12 fee in the chosen ledger'
    }
    unresolved = 'Prime-axis signed moment J6/W13 and covered bridge 2 max(e,0); effective BV calibration also remains'
    scope = 'Only one new finite bank; corrected identities and specific falsifiers retained; no global impossibility asserted'
}
[System.IO.File]::WriteAllText((Join-Path $JudgeRoot 'judge_receipt.json'), ($Receipt | ConvertTo-Json -Depth 12) + "`n", $Utf8)
Write-Output 'Round 9: one isolated exact bank and source-page reproduction passed; 307 prior artifacts preserved; no Lean invoked; victory=false.'
Write-Output 'Score: 0'
