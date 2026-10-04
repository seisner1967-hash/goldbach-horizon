$ErrorActionPreference = 'Stop'
$GammaTaskDirectory = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\role6\gamma_h2'
$GammaTaskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$GammaTaskRuntime = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$GammaPrepPath = Join-Path $GammaTaskDirectory 'gamma_preparation22.json'
$GammaManifestPath = Join-Path $GammaTaskDirectory 'gamma_prepared_manifest22.json'
$GammaReceiptPath = Join-Path $GammaTaskDirectory 'gamma_prepared_receipt22.json'
foreach ($GammaNewPath in @($GammaPrepPath, $GammaManifestPath, $GammaReceiptPath)) {
    if (Test-Path -LiteralPath $GammaNewPath) { throw 'Preparation output already exists; no overwrite or replay' }
}
if (Test-Path -LiteralPath (Join-Path $GammaTaskDirectory 'actual_gamma22')) { throw 'Actual directory must not exist during preparation' }

function Get-GammaBinding([string]$GammaSourcePath, [string]$GammaKind, [string]$GammaExpectedHash = '') {
    $GammaResolvedSource = (Resolve-Path -LiteralPath $GammaSourcePath).Path
    $GammaFile = Get-Item -LiteralPath $GammaResolvedSource
    $GammaHash = (Get-FileHash -LiteralPath $GammaResolvedSource -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($GammaExpectedHash -and $GammaHash -ne $GammaExpectedHash) { throw ('Known read-only binding mismatch: ' + $GammaResolvedSource) }
    return [ordered]@{path=$GammaResolvedSource; sha256=$GammaHash; bytes=$GammaFile.Length; kind=$GammaKind}
}

function Write-GammaNewJson([string]$GammaOutputPath, $GammaData) {
    $GammaText = ($GammaData | ConvertTo-Json -Depth 25) + "`n"
    $GammaUtf8 = [System.Text.UTF8Encoding]::new($false)
    $GammaBytes = $GammaUtf8.GetBytes($GammaText)
    $GammaStream = [System.IO.File]::Open($GammaOutputPath, [System.IO.FileMode]::CreateNew, [System.IO.FileAccess]::Write)
    try { $GammaStream.Write($GammaBytes, 0, $GammaBytes.Length) } finally { $GammaStream.Dispose() }
}

$GammaBindings = @()
foreach ($GammaOwnName in @('dyadic_gamma22.py','gamma_bank22.py','gamma_contract22.json','gamma_paper22.md','run_gamma_numeric_once22.py','gamma_read_scope22.json','gamma_preparation_notes22.md','prepare_gamma_metadata22.ps1')) {
    $GammaBindings += Get-GammaBinding (Join-Path $GammaTaskDirectory $GammaOwnName) 'NEW_GAMMA_SOURCE_OR_METADATA'
}
$GammaBindings += Get-GammaBinding (Join-Path $GammaTaskBase 'round22\role6\interval22.py') 'READONLY_ARITHMETIC_SOURCE_PROVENANCE' '6e29ec2c7fb5d8e1eba796f3d863fb4c95db5b2bb5cf9671a9fb80d6469df588'
$GammaBindings += Get-GammaBinding (Join-Path $GammaTaskBase 'round22\role4\GammaPrerequisites22.lean') 'READONLY_GENUINE_GAMMA_ANALYTIC_SOURCE' '8bcfef577be2dbf3412646bd7938fe3d929dc0efdd4d1d7c29149ff6102ed7a0'
$GammaBindings += Get-GammaBinding (Join-Path $GammaTaskBase 'round22\role1\real_trace_annex.md') 'READONLY_FUTURE_TRACE_CONTEXT' '4736c056f047c84f4ebe38ed4f60b1a9c473481006dcee8341c168afdd9ea2b5'
$GammaBindings += Get-GammaBinding (Join-Path $GammaTaskBase 'round22\USER_DIRECTIVE.md') 'READONLY_USER_DIRECTIVE' 'c5aa8310ad54c57726339a8e99057f158254eb6d113ac3aeb71ddc9627f23947'
$GammaBindings += Get-GammaBinding (Join-Path $GammaTaskBase 'round22\PROBE_BLOCK.md') 'READONLY_PROBE' 'a896c9d0fa4114845b20c3023246dcb987463923df798cac2c537c70cfb73fc3'
$GammaBindings += Get-GammaBinding $GammaTaskRuntime 'READONLY_RUNTIME_BYTES' '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'

$GammaTime = [DateTime]::UtcNow.ToString('o')
$GammaManifest = [ordered]@{schema='round22.gamma_h2_aux.prepared_manifest.v1'; status='PREPARED_SOURCE_ONLY_NOT_EXECUTED'; time_utc=$GammaTime; bank_id='GAMMA_ROTATED_LAPLACE_AUX22'; scope='GAMMA_H2_AUX_ONLY'; bindings=$GammaBindings; binding_count=$GammaBindings.Count; no_math_import_or_execution=$true; no_Lean_invocation=$true; no_G0_replay=$true}
Write-GammaNewJson $GammaManifestPath $GammaManifest
$GammaBindings += Get-GammaBinding $GammaManifestPath 'NEW_GAMMA_PREPARED_MANIFEST'
$GammaPrep = [ordered]@{schema='round22.gamma_h2_aux.preparation.v1'; status='PREPARED_SOURCE_ONLY_NOT_EXECUTED'; time_utc=$GammaTime; actor='ROLE6'; bank_id='GAMMA_ROTATED_LAPLACE_AUX22'; scope='GAMMA_H2_AUX_ONLY'; runtime_path=$GammaTaskRuntime; runtime_flags=@('-B','-X','utf8'); bindings=$GammaBindings; binding_count=$GammaBindings.Count; captures_before_START=$GammaBindings.Count+2; root_gate_path=(Join-Path $GammaTaskBase '.arbor\sessions\parity\.coordinator\messages\round22_gamma_numeric_authorization.json'); future_actual_directory=(Join-Path $GammaTaskDirectory 'actual_gamma22'); expected_case_count=21; expected_cells_each_case=9728; expected_mutants_applicable=12; expected_sqrt_certificates=43; Gamma_math_executions=0; Gamma_Lean_executions=0; sole_attempt_consumed=$false; old_producer_reexecution=0; no_credit_for_Weil_heat_coefficientN_DN_WIN=$true; command_template=@($GammaTaskRuntime,'-B','-X','utf8',(Join-Path $GammaTaskDirectory 'run_gamma_numeric_once22.py'),'--root-authorization','EXACT_DISTINCT_ROOT_GATE','--root-authorization-sha256','EXACT_GATE_SHA256')}
Write-GammaNewJson $GammaPrepPath $GammaPrep
$GammaPrepBinding = Get-GammaBinding $GammaPrepPath 'PREPARATION'
$GammaManifestBinding = Get-GammaBinding $GammaManifestPath 'MANIFEST'
$GammaReceipt = [ordered]@{schema='round22.gamma_h2_aux.prepared_receipt.v1'; status='PREPARED_SOURCE_ONLY_NOT_EXECUTED'; time_utc=[DateTime]::UtcNow.ToString('o'); preparation=$GammaPrepBinding; manifest=$GammaManifestBinding; bindings_verified_count=$GammaBindings.Count; runtime_actual_byte_sha256='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'; preparation_is_only_metadata=$true; Gamma_math_executions=0; Gamma_Lean_executions=0; actual_directory_exists=$false; gate_is_not_created_by_ROLE6=$true; G0_is_historical_and_not_replayed=$true}
Write-GammaNewJson $GammaReceiptPath $GammaReceipt
[ordered]@{preparation_sha256=$GammaPrepBinding.sha256; manifest_sha256=$GammaManifestBinding.sha256; receipt_sha256=(Get-FileHash -LiteralPath $GammaReceiptPath -Algorithm SHA256).Hash.ToLowerInvariant(); binding_count=$GammaBindings.Count; planned_PREEXEC_captures=$GammaBindings.Count+2; no_math_started=$true} | ConvertTo-Json
