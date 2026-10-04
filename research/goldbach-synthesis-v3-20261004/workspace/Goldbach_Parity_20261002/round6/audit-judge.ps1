param(
    [string] $Python = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
)
$ErrorActionPreference = 'Stop'
$RoundRoot = $PSScriptRoot
$JudgeRoot = Join-Path $RoundRoot 'judge'
$Utf8 = [System.Text.UTF8Encoding]::new($false)
[void](New-Item -ItemType Directory -Path $JudgeRoot -Force)
$Before = & (Join-Path $RoundRoot 'verify-frozen.ps1')
if (@(Get-ChildItem -LiteralPath $RoundRoot -Filter '*.lean' -Recurse -File).Count -ne 0) {
    throw 'Round 6 is an audit before compilation, with no new Lean source accepted'
}
$SourceNames = @('agent1_finite_dilation.md', 'agent2_coupled_squarefree.md',
    'agent3_contract_audit.md', 'agent4_contract_audit.md', 'agent6.md',
    'exact_tools.py', 'conservation.py', 'katai_checks.py', 'squarefree_checks.py')
$Sources = [ordered]@{}
foreach ($Name in $SourceNames) {
    $Path = Join-Path $RoundRoot $Name
    $Sources[$Name] = (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()
}
$Gates = [System.Collections.Generic.List[object]]::new()
foreach ($Stem in @('katai', 'squarefree')) {
    $Path = Join-Path $RoundRoot "$Stem.json"
    $Gate = Get-Content -LiteralPath $Path -Raw | ConvertFrom-Json -AsHashtable
    $ExpectedStatus = if ($Stem -eq 'squarefree') { 'PASS_CORRECTED_CONTRACT' } else { 'PASS' }
    if ($Gate.status -ne $ExpectedStatus -or $Gate.N -ne 100000000) { throw "Final numeric gate not passed: $Path" }
    if ($Gate.script_sha256 -ne $Sources["$($Stem)_checks.py"]) { throw "Numeric gate source hash is stale: $Path" }
    $Gates.Add([ordered]@{ path = $Path; status = $Gate.status; N = $Gate.N
        sha256 = (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()
        script_sha256 = $Gate.script_sha256 })
}
$ReplayPath = Join-Path $JudgeRoot 'numerical\replay.py'
$RawOutput = & $Python $ReplayPath 2>&1
$ReplayExit = $LASTEXITCODE
$ReplayLog = Join-Path $JudgeRoot 'numerical_replay.log'
[System.IO.File]::WriteAllText($ReplayLog, (($RawOutput | ForEach-Object { [string]$_ }) -join "`n") + "`n", $Utf8)
if ($ReplayExit -ne 0) { throw "Independent numeric replay failed; read $ReplayLog" }
$ReplayReceiptPath = Join-Path $JudgeRoot 'numerical\replay_receipt.json'
$ReplayReceipt = Get-Content -LiteralPath $ReplayReceiptPath -Raw | ConvertFrom-Json -AsHashtable
if ($ReplayReceipt.status -ne 'PASS' -or $ReplayReceipt.lean_invoked -ne $false) {
    throw 'Unexpected replay status or Lean invocation'
}
$After = & (Join-Path $RoundRoot 'verify-frozen.ps1')
foreach ($Name in $SourceNames) {
    $Observed = (Get-FileHash -LiteralPath (Join-Path $RoundRoot $Name) -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Observed -ne $Sources[$Name]) { throw "Round-6 source changed during audit: $Name" }
}
$Receipt = [ordered]@{
    round = 6; status = 'REJECTED_BEFORE_COMPILATION'; victory = $false; score = 0
    identities = 'CORRECTED_FINITE_IDENTITIES_VALID; no new Lean certification'
    quantitative_gain = 'NOT_OBTAINED'; lean_invoked = $false; compiler_exit_code = $null
    new_lean_modules = 0; new_lean_conclusions = 0
    previous_auxiliary_modules = 9; previous_auxiliary_conclusions = 116
    recorded_at_utc = [DateTime]::UtcNow.ToString('o')
    source_sha256 = $Sources; numerical_gates = @($Gates.ToArray())
    numerical_replay = [ordered]@{ status = $ReplayReceipt.status; exit_code = $ReplayExit
        receipt = $ReplayReceiptPath
        receipt_sha256 = (Get-FileHash -LiteralPath $ReplayReceiptPath -Algorithm SHA256).Hash.ToLowerInvariant()
        log = $ReplayLog; log_sha256 = (Get-FileHash -LiteralPath $ReplayLog -Algorithm SHA256).Hash.ToLowerInvariant() }
    preserved_previous_artifacts_before = $Before; preserved_previous_artifacts_after = $After
    historical_agent3_numeric_hashes_used_as_current_gate = $false
    scope = 'False shortcuts rejected; exact corrected identities retained; no signed complete-residue estimate'
}
[System.IO.File]::WriteAllText((Join-Path $RoundRoot 'judge_receipt.json'), ($Receipt | ConvertTo-Json -Depth 12) + "`n", $Utf8)
Write-Output 'Round 6: isolated numeric replay PASS; 160 previous artifacts preserved; no Lean invoked; victory=false.'
Write-Output 'Score: 0'
