param(
    [string] $Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
)
$ErrorActionPreference = 'Stop'
$RoundRoot = $PSScriptRoot
$JudgeRoot = Join-Path $RoundRoot 'judge'
$Utf8 = [System.Text.UTF8Encoding]::new($false)
$Before = & (Join-Path $RoundRoot 'verify-frozen.ps1')
if (@(Get-ChildItem -LiteralPath $RoundRoot -Filter '*.lean' -Recurse -File).Count -ne 0) {
    throw 'Round 7 admits no new Lean source; this is an audit before compilation'
}
$InputsPath = Join-Path $JudgeRoot 'input_sha256.json'
$Inputs = Get-Content -LiteralPath $InputsPath -Raw | ConvertFrom-Json -AsHashtable
foreach ($Entry in $Inputs.sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath (Join-Path $RoundRoot $Entry.Key) -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Final production input changed: $($Entry.Key)" }
}
$StatusByStem = [ordered]@{
    logarithmic = 'PASS_IDENTITY_ONLY'
    jacobi = 'PASS_IDENTITIES_ONLY'
    trace = 'PASS_EXACT_CONNECTION_ONLY'
}
$Gates = [System.Collections.Generic.List[object]]::new()
foreach ($Stem in $StatusByStem.Keys) {
    $Path = Join-Path $RoundRoot "$Stem.json"
    $Gate = Get-Content -LiteralPath $Path -Raw | ConvertFrom-Json -AsHashtable
    if ($Gate.status -ne $StatusByStem[$Stem] -or $Gate.N -ne 100000000) {
        throw "Unexpected final numeric gate: $Path"
    }
    if ($Gate.script_sha256 -ne $Inputs.sha256["$($Stem)_checks.py"]) {
        throw "Numeric gate source hash is stale: $Path"
    }
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
    throw 'Unexpected isolated replay status or Lean invocation'
}
$After = & (Join-Path $RoundRoot 'verify-frozen.ps1')
foreach ($Entry in $Inputs.sha256.GetEnumerator()) {
    $Observed = (Get-FileHash -LiteralPath (Join-Path $RoundRoot $Entry.Key) -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Entry.Value) { throw "Production input changed during audit: $($Entry.Key)" }
}
$Receipt = [ordered]@{
    round = 7; status = 'REJECTED_BEFORE_COMPILATION'; victory = $false; score = 0
    identities = 'EXACT_IDENTITIES_RETAINED; finite replay does not provide new Lean certification'
    quantitative_gain = 'SIGNED_GAIN_NOT_OBTAINED'; lean_invoked = $false; compiler_exit_code = $null
    new_lean_modules = 0; new_lean_conclusions = 0
    previous_auxiliary_modules = 9; previous_auxiliary_conclusions = 116
    recorded_at_utc = [DateTime]::UtcNow.ToString('o')
    input_manifest = $InputsPath
    input_manifest_sha256 = (Get-FileHash -LiteralPath $InputsPath -Algorithm SHA256).Hash.ToLowerInvariant()
    source_sha256 = $Inputs.sha256; numerical_gates = @($Gates.ToArray())
    judge_scripts_sha256 = [ordered]@{
        'audit-judge.ps1' = (Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash.ToLowerInvariant()
        'verify-frozen.ps1' = (Get-FileHash -LiteralPath (Join-Path $RoundRoot 'verify-frozen.ps1') -Algorithm SHA256).Hash.ToLowerInvariant()
        'replay.py' = (Get-FileHash -LiteralPath $ReplayPath -Algorithm SHA256).Hash.ToLowerInvariant()
    }
    numerical_replay = [ordered]@{ status = $ReplayReceipt.status; exit_code = $ReplayExit
        receipt = $ReplayReceiptPath
        receipt_sha256 = (Get-FileHash -LiteralPath $ReplayReceiptPath -Algorithm SHA256).Hash.ToLowerInvariant()
        log = $ReplayLog; log_sha256 = (Get-FileHash -LiteralPath $ReplayLog -Algorithm SHA256).Hash.ToLowerInvariant() }
    preserved_previous_artifacts_before = $Before; preserved_previous_artifacts_after = $After
    full_Jacobi_cycles_with_A_273 = [ordered]@{
        p_3_7_13 = 'NORMALIZATION_DIAGNOSTICS_ONLY; p divides A, physical p-unit fibre empty'
        CRT_p_11_M_819 = 'ADMISSIBLE_SIGNED_EXPANSION_CELL_DIAGNOSTIC; not squarefree HH tuples'
    }
    analytical_partial_results = [ordered]@{
        Mellin_tail = 'WRITTEN_ANALYTIC_BOUND; no Lean certificate; near-zero signed integral remains'
        C1_lower_bound = 'QUALITATIVE_EVENTUAL N*log(N)/384 for even N, 3 not dividing N; global threshold not evaluated; no Lean certificate'
    }
    native_connection_counterexample = 'Original tuple k=7: new two-axis twists vanish, native centered row=5/6'
    scope = 'Specific false shortcuts rejected; corrected identities and general open mechanisms retained'
}
[System.IO.File]::WriteAllText((Join-Path $RoundRoot 'judge_receipt.json'), ($Receipt | ConvertTo-Json -Depth 12) + "`n", $Utf8)
Write-Output 'Round 7: three isolated exact replays passed with distinct gate statuses; 190 previous artifacts preserved; no Lean invoked; victory=false.'
Write-Output 'Score: 0'
