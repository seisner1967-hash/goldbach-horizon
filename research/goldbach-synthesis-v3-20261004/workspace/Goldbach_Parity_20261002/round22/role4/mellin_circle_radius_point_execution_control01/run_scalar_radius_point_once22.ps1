# Metadata launcher only. One gate-authorized scalar Python child; no scientific code.
$ErrorActionPreference = 'Stop'
$taskGatePath = 'D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/.arbor/sessions/parity/.coordinator/messages/round22_scalar_radius_point01_authorization.json'
$taskGateExpected = 'e9149ac83f476cfdf1b14098dbd03e167c80e79716e02b1c7bf00c0405ee7e48'
$taskPlanPath = 'D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/mellin_circle_radius_point_source_review01/independent_invocation_plan22.json'
$taskPlanExpected = '5fffe743379d5a4da83127cc8f67b5b78f6b4ff12518c6497b8f55de1dfabd14'
$taskActual = 'D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role6/mellin_circle_radius_point_source01/actual_radius_point01_attempt01'
$taskParentPath = $PSCommandPath
function taskSHA([string]$taskPath) { return (Get-FileHash -LiteralPath $taskPath -Algorithm SHA256).Hash.ToLowerInvariant() }
function taskRow([string]$taskPath) {
  $taskFile = Get-Item -LiteralPath $taskPath
  return [ordered]@{path=$taskFile.FullName.Replace('\','/');bytes=$taskFile.Length;sha256=(taskSHA $taskPath)}
}
function taskJSON([string]$taskPath, $taskData) {
  $taskText = ($taskData | ConvertTo-Json -Depth 20)
  $taskBytes = [Text.UTF8Encoding]::new($false).GetBytes($taskText + [Environment]::NewLine)
  $taskStream = [IO.File]::Open($taskPath,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::Read)
  try { $taskStream.Write($taskBytes,0,$taskBytes.Length) } finally { $taskStream.Dispose() }
}
function taskCheck($taskExpected) {
  $taskObserved = taskRow $taskExpected.path
  if ($taskObserved.bytes -ne $taskExpected.bytes -or $taskObserved.sha256 -cne $taskExpected.sha256) { throw "Input byte mismatch: $($taskExpected.path)" }
  return $taskObserved
}
if ((taskSHA $taskGatePath) -cne $taskGateExpected) { throw 'ROOT gate SHA mismatch' }
if ((taskSHA $taskPlanPath) -cne $taskPlanExpected) { throw 'Frozen invocation plan SHA mismatch' }
$taskGate = Get-Content -LiteralPath $taskGatePath -Raw | ConvertFrom-Json
$taskPlan = Get-Content -LiteralPath $taskPlanPath -Raw | ConvertFrom-Json
if (-not $taskGate.authorized -or $taskGate.status -cne 'AUTHORIZED_ONE_INDEPENDENT_SCALAR_INVOCATION') { throw 'Gate not authorized' }
if ($taskGate.scope -cne 'NUMERIC_RADIUS_BOUND_ONLY_NOT_IDENTITY_OR_LEAN_PROOF') { throw 'Unexpected gate scope' }
if ($taskGate.actual_directory -cne $taskActual -or $taskPlan.future_actual_directory -cne $taskActual -or $taskPlan.cwd -cne $taskActual) { throw 'ACTUAL/CWD mismatch' }
if ($taskGate.bindings.Count -ne 14 -or $taskGate.inputs.Count -ne 9) { throw 'Exact gate binding/input counts required' }
$taskFixedArgs = @('-I','-S','-B','-X','utf8','D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role6/mellin_circle_radius_point_source01/radius_point22.py')
if (($taskGate.argv | ConvertTo-Json -Compress) -cne ($taskFixedArgs | ConvertTo-Json -Compress) -or ($taskPlan.argv | ConvertTo-Json -Compress) -cne ($taskFixedArgs | ConvertTo-Json -Compress)) { throw 'Fixed argv mismatch' }
if ($taskGate.program.sha256 -cne 'a612d5863785a1aa2c29da8333a448087a38afccc5567ef95a7584807dfa7078') { throw 'Source SHA mismatch' }
if ($taskGate.runtime.path -cne 'C:/Users/Utilisateur/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe' -or $taskGate.runtime.sha256 -cne '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c') { throw 'Runtime mismatch' }
if ($taskGate.limits.total_parent_wall_seconds -ne 30 -or $taskGate.limits.child_deadline_seconds_from_parent_T0 -ne 20 -or $taskGate.limits.closing_reserve_seconds -ne 10 -or $taskGate.limits.combined_stdout_stderr_bytes -ne 1048576 -or $taskGate.maximum_mathematical_children -ne 1 -or $taskGate.retries -ne 0) { throw 'Fixed limits mismatch' }
if ((Test-Path -LiteralPath $taskActual)) { throw 'Refusing any invocation: ACTUAL already exists' }
$taskDistinct = @($taskGate.bindings | ForEach-Object { (Get-Item -LiteralPath $_.path).FullName } | Sort-Object -Unique)
if ($taskDistinct.Count -ne 14) { throw 'Gate paths are not 14 distinct resolved files' }
$taskExpectedInputPaths = @($taskGate.inputs | ForEach-Object { (Get-Item -LiteralPath $_.path).FullName } | Sort-Object -Unique)
$taskPlanInputPaths = @($taskPlan.inputs | ForEach-Object { (Get-Item -LiteralPath $_.path).FullName } | Sort-Object -Unique)
if ($taskExpectedInputPaths.Count -ne 9 -or (Compare-Object $taskExpectedInputPaths $taskPlanInputPaths)) { throw 'Exact nine planned inputs required' }
$taskParentOriginal = taskRow $taskParentPath
New-Item -ItemType Directory -Path $taskActual -ErrorAction Stop | Out-Null
$taskT0 = [DateTime]::UtcNow.ToString('o')
$taskWatch = [Diagnostics.Stopwatch]::StartNew()
$taskProcess = $null
$taskInvocationCount = 0
$taskExit = $null
$taskError = $null
$taskStopReason = $null
$taskSTARTUTC = $null
$taskFINUTC = $null
$taskCaptures = @()
$taskPRE = @()
$taskPOST = @()
$taskMismatches = @()
$taskOutput = $null
$taskVerdict = 'SCALAR_RADIUS_BOUND_ONLY_FAILED'
$taskGateCapture = $null
$taskParentCapture = $null
$taskStdout = "$taskActual/stdout.log"
$taskStderr = "$taskActual/stderr.log"
try {
  New-Item -ItemType Directory -Path "$taskActual/PREEXEC" -ErrorAction Stop | Out-Null
  $taskIndex = 0
  foreach ($taskBinding in $taskGate.bindings) {
    $taskIndex++
    $taskObserved = taskCheck $taskBinding
    $taskPRE += $taskObserved
    $taskName = '{0:D2}_{1}' -f $taskIndex,[IO.Path]::GetFileName($taskBinding.path)
    $taskCopy = "$taskActual/PREEXEC/$taskName"
    [IO.File]::Copy((Get-Item -LiteralPath $taskBinding.path).FullName,$taskCopy,$false)
    if ((taskSHA $taskCopy) -cne $taskBinding.sha256) { throw 'Capture SHA mismatch' }
    $taskCaptures += [ordered]@{original=$taskObserved;copy=(taskRow $taskCopy)}
  }
  $taskRuntimePRE = taskCheck $taskGate.runtime
  $taskGateCapture = "$taskActual/PREEXEC/15_ROOT_gate.json"
  [IO.File]::Copy($taskGatePath,$taskGateCapture,$false)
  if ((taskSHA $taskGateCapture) -cne $taskGateExpected) { throw 'Gate capture mismatch' }
  $taskParentCapture = "$taskActual/PREEXEC/16_metadata_parent.ps1"
  [IO.File]::Copy($taskParentPath,$taskParentCapture,$false)
  if ((taskSHA $taskParentCapture) -cne $taskParentOriginal.sha256) { throw 'Parent capture mismatch' }
  taskJSON "$taskActual/PRE.json" ([ordered]@{UTC=[DateTime]::UtcNow.ToString('o');parent_T0_UTC=$taskT0;gate_sha256=$taskGateExpected;plan_sha256=$taskPlanExpected;gate_bindings=$taskPRE;captures=$taskCaptures;runtime=$taskRuntimePRE;metadata_parent=$taskParentOriginal;original_input_count=9;gate_binding_count=14;capture_gate_parent_extra=2;scientific_invocations_so_far=0})
  foreach ($taskLog in @($taskStdout,$taskStderr)) { $taskEmpty=[IO.File]::Open($taskLog,[IO.FileMode]::CreateNew);$taskEmpty.Dispose() }
  $taskSTARTUTC = [DateTime]::UtcNow.ToString('o')
  taskJSON "$taskActual/START.json" ([ordered]@{UTC=$taskSTARTUTC;parent_T0_UTC=$taskT0;runtime=$taskGate.runtime;argv=$taskFixedArgs;cwd=$taskActual;gate_sha256=$taskGateExpected;plan_sha256=$taskPlanExpected;parent_sha256=$taskParentOriginal.sha256;source_sha256=$taskGate.program.sha256;max_children=1;retry=0;total_parent_wall_seconds=30;child_deadline_seconds_from_T0=20;closing_reserve_seconds=10;maximum_outputs_bytes=1048576;atomic_OS_start_deadline_guarantee=$false})
  if ($taskWatch.Elapsed.TotalSeconds -ge 20) { $taskStopReason='EXPIRED_AT_LAST_PARENT_CHECK_NO_CHILD';throw 'Child deadline expired before invocation' }
  $taskInvocationCount = 1
  $taskProcess = Start-Process -FilePath $taskGate.runtime.path -ArgumentList $taskFixedArgs -WorkingDirectory $taskActual -RedirectStandardOutput $taskStdout -RedirectStandardError $taskStderr -WindowStyle Hidden -PassThru
  while (-not $taskProcess.HasExited) {
    $taskLength = (Get-Item -LiteralPath $taskStdout).Length + (Get-Item -LiteralPath $taskStderr).Length
    if ($taskLength -gt 1048576) { $taskStopReason='OUTPUT_LIMIT_EXCEEDED';$taskProcess.Kill();break }
    if ($taskWatch.Elapsed.TotalSeconds -ge 20) { $taskStopReason='CHILD_DEADLINE';$taskProcess.Kill();break }
    $taskProcess.WaitForExit(25) | Out-Null
    $taskProcess.Refresh()
  }
  $taskProcess.WaitForExit()
  $taskProcess.Refresh()
  $taskExit = $taskProcess.ExitCode
  $taskFINUTC = [DateTime]::UtcNow.ToString('o')
  $taskLength = (Get-Item -LiteralPath $taskStdout).Length + (Get-Item -LiteralPath $taskStderr).Length
  if ($taskLength -gt 1048576) { $taskStopReason='OUTPUT_LIMIT_EXCEEDED' }
  if ($taskStopReason) { throw $taskStopReason }
  if ($taskExit -ne 0) { throw "Scalar child returned $taskExit" }
  $taskOutput = Get-Content -LiteralPath $taskStdout -Raw | ConvertFrom-Json
  if ($taskOutput.schema -cne 'ROUND22_EXACT_SCALAR_RADIUS_BOUND_OUTPUT' -or $taskOutput.scope -cne $taskGate.scope -or $taskOutput.comparison_status -cne 'RATIONAL_UPPER_BOUND_LT_TAU') { throw 'Output scope/status mismatch' }
  if ($taskOutput.upstream_source_sha256 -cne 'bf9b8257760a20d33dd21714221401cd8fd327596f72e56c4d024200b2cb6c4c') { throw 'Output upstream mismatch' }
  if ($taskOutput.parameters.N -ne 100000000 -or $taskOutput.parameters.H -ne 100000000000 -or $taskOutput.parameters.taylor_degree -ne 150 -or $taskOutput.parameters.a.numerator -cne '1' -or $taskOutput.parameters.a.denominator -cne '100000000' -or $taskOutput.parameters.tau.numerator -cne '1' -or $taskOutput.parameters.tau.denominator -cne '1000000' -or $taskOutput.parameters.H_over_8N.numerator -cne '125' -or $taskOutput.parameters.H_over_8N.denominator -cne '1') { throw 'Fixed parameter output mismatch' }
  if ($taskOutput.strict_comparison_integer_witness.left_lt_right -ne $true -or $taskOutput.fixed_degree_witness.S6_at_5_gt_100 -ne $true -or $taskOutput.fixed_degree_witness.S150_at_125_ge_block_product -ne $true -or $taskOutput.fixed_degree_witness.S150_at_125_gt_10_power_50 -ne $true) { throw 'Missing true exact comparison witnesses' }
  foreach ($taskFlag in $taskOutput.limits.PSObject.Properties) { if ($taskFlag.Value -ne $false) { throw "Unexpected proof-boundary flag: $($taskFlag.Name)" } }
  if ((Get-Item -LiteralPath $taskStderr).Length -ne 0) { throw 'Unexpected stderr for successful fixed scalar comparison' }
  $taskVerdict = 'NUMERIC_RADIUS_BOUND_ONLY_PASS_NOT_IDENTITY_OR_LEAN_PROOF'
} catch {
  $taskError = $_.Exception.Message
} finally {
  if ($taskProcess -and -not $taskProcess.HasExited) { $taskProcess.Kill();$taskProcess.WaitForExit();$taskProcess.Refresh();$taskExit=$taskProcess.ExitCode }
  if (-not $taskFINUTC) { $taskFINUTC=[DateTime]::UtcNow.ToString('o') }
  taskJSON "$taskActual/FIN.json" ([ordered]@{UTC=$taskFINUTC;start_UTC=$taskSTARTUTC;parent_T0_UTC=$taskT0;exit_code=$taskExit;PID=$(if($taskProcess){$taskProcess.Id}else{0});child_invocations=$taskInvocationCount;child_closed=$(if($taskProcess){$taskProcess.HasExited}else{$true});stop_reason=$taskStopReason;error=$taskError;parent_elapsed_seconds_at_FIN=$taskWatch.Elapsed.TotalSeconds;stdout=(taskRow $taskStdout);stderr=(taskRow $taskStderr);scope=$taskGate.scope})
  foreach ($taskBinding in $taskGate.bindings) {
    try { $taskObserved=taskCheck $taskBinding;$taskPOST+=$taskObserved } catch { $taskMismatches+=($_.Exception.Message) }
  }
  foreach ($taskCapture in $taskCaptures) {
    try { $taskObserved=taskCheck $taskCapture.copy } catch { $taskMismatches+=($_.Exception.Message) }
  }
  foreach ($taskPair in @(@($taskGatePath,$taskGateExpected),@($taskGateCapture,$taskGateExpected),@($taskParentPath,$taskParentOriginal.sha256),@($taskParentCapture,$taskParentOriginal.sha256))) {
    try { if (-not $taskPair[0] -or (taskSHA $taskPair[0]) -cne $taskPair[1]) { throw "Control conservation mismatch: $($taskPair[0])" } } catch { $taskMismatches+=($_.Exception.Message) }
  }
  if ($taskMismatches.Count -ne 0 -or $taskWatch.Elapsed.TotalSeconds -ge 30) { $taskVerdict='SCALAR_RADIUS_BOUND_ONLY_FAILED' }
  taskJSON "$taskActual/POST.json" ([ordered]@{UTC=[DateTime]::UtcNow.ToString('o');gate_bindings_verified=$taskPOST.Count;capture_count=$taskCaptures.Count;gate_and_parent_original_copies_checked=$true;mismatches=$taskMismatches;all_preserved=($taskMismatches.Count -eq 0);parent_elapsed_seconds=$taskWatch.Elapsed.TotalSeconds;parent_deadline_exceeded=($taskWatch.Elapsed.TotalSeconds -ge 30);no_retry=$true;new_scientific_child_count=$taskInvocationCount})
  $taskOutputs=@('PRE.json','START.json','FIN.json','POST.json','stdout.log','stderr.log') | ForEach-Object { taskRow "$taskActual/$_" }
  $taskReceipt=[ordered]@{schema='ROUND22_INDEPENDENT_SCALAR_RADIUS_POINT01_RECEIPT';status=$taskVerdict;scope=$taskGate.scope;UTC=[DateTime]::UtcNow.ToString('o');parent_T0_UTC=$taskT0;START_UTC=$taskSTARTUTC;FIN_UTC=$taskFINUTC;exit_code=$taskExit;child_invocations=$taskInvocationCount;retry=0;gate_sha256=$taskGateExpected;plan_sha256=$taskPlanExpected;parent_sha256=$taskParentOriginal.sha256;source_sha256=$taskGate.program.sha256;runtime_sha256=$taskGate.runtime.sha256;original_inputs_captured=9;gate_binding_count=14;captures=$taskCaptures;gate_capture=(taskRow $taskGateCapture);metadata_parent_capture=(taskRow $taskParentCapture);POST_binding_count=$taskPOST.Count;POST_mismatch_count=$taskMismatches.Count;all_preserved=($taskMismatches.Count -eq 0);parent_elapsed_seconds=$taskWatch.Elapsed.TotalSeconds;total_parent_wall_limit_seconds=30;child_deadline_from_T0_seconds=20;closing_reserve_seconds=10;maximum_outputs_bytes=1048576;measured_scalar_comparison_available=($taskVerdict -ceq 'NUMERIC_RADIUS_BOUND_ONLY_PASS_NOT_IDENTITY_OR_LEAN_PROOF');comparison_status=$(if($taskOutput){$taskOutput.comparison_status}else{$null});error=$taskError;stop_reason=$taskStopReason;outputs=$taskOutputs;official_credit=0;real_inputs_machine_verified_in_Lean=$false;upstream_SOURCE34_Lean_validated=$false;C_N_evaluated=$false;D_N_evaluated=$false;identity_evaluated=$false;WIN=$false;archive_scope='No writes to archives; no fresh full3089 sweep claimed'}
  taskJSON "$taskActual/receipt.json" $taskReceipt
  [ordered]@{actual=$taskActual;status=$taskVerdict;START_UTC=$taskSTARTUTC;FIN_UTC=$taskFINUTC;exit_code=$taskExit;child_invocations=$taskInvocationCount;elapsed_parent_seconds=$taskWatch.Elapsed.TotalSeconds;POST_mismatches=$taskMismatches.Count;receipt=(taskRow "$taskActual/receipt.json")} | ConvertTo-Json -Depth 4
}
if ($taskVerdict -ceq 'NUMERIC_RADIUS_BOUND_ONLY_PASS_NOT_IDENTITY_OR_LEAN_PROOF') { exit 0 } else { exit 1 }
