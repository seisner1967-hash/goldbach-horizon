param(
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{64}$')][string]$IndependentReviewSha256,
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{64}$')][string]$TrustReviewSha256
)
# SOURCE ONLY. ROOT must read and separately authorize exactly one metadata
# invocation. This never imports/parses a candidate, runs a native image,
# prepares an ACTUAL candidate directory or creates an authorization gate.
$ErrorActionPreference='Stop'
$TaskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$TaskHere=Split-Path -Parent $MyInvocation.MyCommand.Path
$Metadata=Join-Path $TaskHere 'metadata_source05'
$MetadataActual=Join-Path $Metadata 'actual_metadata_prepare05_attempt01'
$ManifestOut=Join-Path $Metadata 'numeric_checker_only_manifest22.json'
$PreparationOut=Join-Path $Metadata 'numeric_checker_only_preparation22.json'
$ReceiptOut=Join-Path $Metadata 'metadata_execution_receipt22.json'
$ConservationOut=Join-Path $Metadata 'metadata_conservation22.json'
$ReadsOut=Join-Path $Metadata 'metadata_read_receipts22.json'
$LocalManifest=Join-Path $TaskHere 'numeric_checker_only_manifest22.json'
$LocalPreparation=Join-Path $TaskHere 'numeric_checker_only_preparation22.json'
$Parent=Join-Path $TaskHere 'run_native05_checker_only_once22.py'
$PlanPath=Join-Path $TaskHere 'numeric_checker_only_execution_plan22.json'
$PolicyPath=Join-Path $TaskHere 'numeric_checker_only_trust_policy22.json'
$HandoffPath=Join-Path $TaskHere 'source_handoff22.json'
$ReviewPath=Join-Path $TaskBase 'round22\role4\native_numeric05_checker_only_consumer_review_source01\source_review22.json'
$TrustPath=Join-Path $TaskBase 'round22\role4\native_numeric05_checker_only_consumer_review_source01\trust_review22.json'
$Old=Join-Path $TaskBase 'round22\role3\native_numeric_consumer_source01'
$OldActual=Join-Path $Old 'actual_numeric04_attempt01'
$OldClosure=Join-Path $TaskBase 'round22\role3\native_numeric_closure_source01\numeric_execution_closure22.json'
$OldManifest=Join-Path $Old 'numeric_manifest22.json'
$OldPre=Join-Path $OldActual 'PRE.json'
$OldGate=Join-Path $TaskBase '.arbor\sessions\parity\.coordinator\messages\round22_native_numeric04_authorization.json'
$Registry=Join-Path $TaskBase 'round22\previous_artifacts_sha256.json'
$RegistrySha='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
$Python='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$PythonSha='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
$RuntimePrefix=(Split-Path -Parent $Python)+'\'
$Checker=Join-Path $TaskBase 'round22\role4\circle_native_revision02\build-final04\checker_dif22.exe'
$CheckerSha='2e7e095c2972fea09ee26500df9dae207ff52497d0f61f2052d76d464ebe6990'
$BuildReceiptSha='04ce22f9ee05215ee9c7c335b41755b1da4e001a82fa20085cfe7dccca1a7fc8'
$BackendSha='88d857ce33eece8f90906bc5088d5cac905b868e60ede1b6439b1a3af3126cc3'
$Links=[ordered]@{}
$Links[$OldManifest]='43d746dee55a02c6fc49032be240badf315e9525d67e12fe05a0d6c52cb5bcad'
$Links[$OldGate]='b5dc57f1afa98304645f9e62505026c805c7a536946a15eedec399922aeba932'
$Links[$OldPre]='2263e2fa6b54445a31ac910e213a417b07cee7468c103726f12f8736e46d1d6d'
$Links[$OldClosure]='a99a5e58768d09a16c7a1ae248448be41016cac228fc57c69372d6abb2774df3'
$Links[(Join-Path $TaskBase 'round22\role3\native_numeric_closure_source01\closure_evidence_bindings22.json')]='ad229461cba2a9b411801c024e443148b9ba2673508107e868a173b42c0ea184'
$Links[(Join-Path $TaskBase 'round22\role3\native_numeric_closure_source01\quiescence_evidence22.json')]='2763645031ab61fdbeae88a8cd5d699d4a11b60381f132dd8e5c5da2ba94402a'
$Links[(Join-Path $TaskBase '.arbor\sessions\parity\.coordinator\messages\round22_native_numeric04_closed_observation.json')]='9097721eee09dea1c30c73a2285713b5a72f98c754781b40d8ab8c977d2f75a3'
$Links[(Join-Path $OldActual 'producer_FIN.json')]='fdbb8187fb1ab37ac19d301d0b475da3ee9e48df004732bd60d930905280a520'
$Links[(Join-Path $OldActual 'producer_payload_hashes.json')]='470441f9e6af30a1be7c4c27999c6498ef6b66509521abdb4ac5cb1a2229d50e'
$Links[(Join-Path $OldActual 'WATCHDOG_TERMINATION_REQUEST.json')]='cd559e4e5a3355639dfe3d46d358537ee3ee9984d29206efa1781fc7f7e1f706'
$Links[(Join-Path $TaskBase 'round22\role4\native_numeric05_checker_only_contract_source01\checker_only_contract22.md')]='8fd1e59d4c751d38a1320aadeed9686dd788eed8c1fb473151924afc7827ad30'
function Need([bool]$Ok,[string]$Message){if(-not$Ok){throw $Message}}
function Digest([string]$Path){return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()}
function Check([string]$Path,[string]$Sha){Need ((Digest $Path) -eq $Sha) ('BYTE_CHANGED '+$Path)}
function Read-Control([string]$Path){Need ((Get-Item -LiteralPath $Path).Length -le 16777216) 'CONTROL_SIZE';return (Get-Content -LiteralPath $Path -Raw|ConvertFrom-Json)}
function Key([string]$Path){return [IO.Path]::GetFullPath($Path).ToLowerInvariant()}
function Write-New([string]$Path,$Value){$Bytes=[Text.UTF8Encoding]::new($false).GetBytes(($Value|ConvertTo-Json -Depth 18)+[Environment]::NewLine);$Stream=[IO.File]::Open($Path,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::None);try{$Stream.Write($Bytes,0,$Bytes.Length)}finally{$Stream.Dispose()}}
function Row([string]$Path,[bool]$Capture=$false){$Item=Get-Item -LiteralPath $Path;Need (-not$Item.PSIsContainer -and ($Item.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0) 'DIRECTORY_OR_REPARSE';return [ordered]@{path=$Item.FullName;bytes=[long]$Item.Length;sha256=(Digest $Path);capture=$Capture}}
function Check-Row($Binding){$Item=Get-Item -LiteralPath $Binding.path;Need (-not$Item.PSIsContainer -and ($Item.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0 -and $Item.Length -eq $Binding.bytes) ('SIZE_OR_REPARSE '+$Binding.path);Check $Binding.path $Binding.sha256}
$RowsByPath=@{}
function Add-Binding([string]$Path,[string]$Sha,$Bytes=$null,[bool]$Capture=$false){$Item=Get-Item -LiteralPath $Path;$Size=if($null -eq $Bytes){[long]$Item.Length}else{[long]$Bytes};$K=Key $Item.FullName;if($RowsByPath.ContainsKey($K)){$OldRow=$RowsByPath[$K];Need ($OldRow.sha256 -eq $Sha -and $OldRow.bytes -eq $Size) 'BINDING_CONFLICT';$Capture=$Capture -or $OldRow.capture};$RowsByPath[$K]=[ordered]@{path=$Item.FullName;bytes=$Size;sha256=$Sha;capture=$Capture}}
function Archives(){Check $Registry $RegistrySha;$R=Read-Control $Registry;$Count=0;foreach($P in $R.sha256.PSObject.Properties){$Path=[IO.Path]::GetFullPath((Join-Path $TaskBase $P.Name));Need ($Path.StartsWith($TaskBase+'\',[StringComparison]::OrdinalIgnoreCase)) 'ARCHIVE_OUTSIDE_BASE';Check $Path $P.Value;$Count++};Need ($Count -eq 3089) 'ARCHIVE_COUNT';return $Count}
# Preconditions before any output: reviewed SOURCE, exclusive future metadata
# paths, all historical producer04 and STOP04 controls byte-bound.
foreach($P in @($MetadataActual,$ManifestOut,$PreparationOut,$ReceiptOut,$ConservationOut,$ReadsOut,$LocalManifest,$LocalPreparation)){Need (-not(Test-Path -LiteralPath $P)) ('EXCLUSIVE_METADATA_OUTPUT_EXISTS '+$P)}
Need (-not(Test-Path -LiteralPath (Join-Path $TaskHere 'actual_numeric05_checker_only_attempt01'))) 'ACTUAL05_ALREADY_EXISTS'
Check $ReviewPath $IndependentReviewSha256
Check $TrustPath $TrustReviewSha256
$Review=Read-Control $ReviewPath;$Trust=Read-Control $TrustPath;$Handoff=Read-Control $HandoffPath;$Plan=Read-Control $PlanPath
$HandoffSha=Digest $HandoffPath;$PolicySha=Digest $PolicyPath;$ParentSha=Digest $Parent
Need ($Review.status -eq 'NUMERIC05_CHECKER_ONLY_SOURCE_REVIEW_CLOSED_WITH_NATIVE_REFINEMENT_OPEN' -and $Review.scope -eq 'NATIVE_NUMERIC05_CHECKER_ONLY_N1E8' -and $Review.reviewer -eq 'ROLE4' -and @($Review.unresolved_execution_blockers).Count -eq 0 -and $Review.source_handoff_sha256 -eq $HandoffSha -and $Review.parent_sha256 -eq $ParentSha -and $Review.old04_producer_payloads_mathematically_validated -eq $false) 'INDEPENDENT_SOURCE_REVIEW_REQUIRED'
Need ($Trust.status -eq 'NUMERIC05_CHECKER_ONLY_FIXED_IMAGE_REVIEWED_WITH_EXPLICIT_WINDOWS_NATIVE_TRUST' -and $Trust.scope -eq 'NATIVE_NUMERIC05_CHECKER_ONLY_N1E8' -and $Trust.reviewer -eq 'ROLE4' -and $Trust.checker_binary_sha256 -eq $CheckerSha -and $Trust.backend_sha256 -eq $BackendSha -and $Trust.policy_sha256 -eq $PolicySha -and $Trust.installed_Windows_and_frozen_native_runtime_trusted -eq $true -and $Trust.effective_loads_observed -eq $false -and $Trust.universal_loader_closure_verified -eq $false -and $Trust.all_non_OS_imports_bound -eq $false -and $Trust.numeric_authorization -eq $false -and $Trust.produced_binary_invocations -eq 0 -and @($Trust.unresolved_execution_blockers).Count -eq 0) 'SCOPED_TRUST_REVIEW_REQUIRED'
Need ($Review.backend_sha256 -eq $BackendSha -and $Trust.checker_source_sha256 -eq '4275ef5afc07f23c2d4b860de8f452ff1e2c07e8ab0d01686c16bdb0d09fe0eb') 'REVIEW_NATIVE_SOURCE_BACKEND_LINK'
foreach($Name in @('job_limit_flags_requested','working_set_limit_flag_requested','rss_os_enforced','rss_control','wall_seconds','checker_deadline_parent_offset_seconds','FIN_POST_reserve_seconds')){Need ($Review.$Name -eq $Plan.$Name -and $Trust.$Name -eq $Plan.$Name) ('REVIEW_RESOURCE_MISMATCH '+$Name)}
foreach($P in $Links.Keys){Check $P $Links[$P];Add-Binding $P $Links[$P] $null $true}
$OldRows=Read-Control $OldManifest;Need ($OldRows.binding_count -eq 6456 -and @($OldRows.bindings).Count -eq 6456) 'OLD04_MANIFEST_COUNT'
foreach($R in $OldRows.bindings){Add-Binding $R.path $R.sha256 $R.bytes $R.capture}
$Closed=Read-Control $OldClosure;Need ($Closed.status -eq 'CLOSED_STOP_NO_MATHEMATICAL_VERDICT' -and $Closed.parent_invocations -eq 1 -and $Closed.parent_exit_code -eq 1 -and $Closed.actual_parent_receipt_present -eq $false -and $Closed.parent_POST_present -eq $false -and $Closed.coefficient_report_present -eq $false -and $Closed.all_current_bytes_preserved -eq $true -and @($Closed.output_bindings).Count -eq 83) 'OLD04_STOP_CLOSURE_REQUIRED'
foreach($R in $Closed.output_bindings){Add-Binding $R.path $R.sha256 $R.bytes $false}
$Pre=Read-Control $OldPre;Need (@($Pre.captures).Count -eq 66) 'OLD04_CAPTURE_COUNT'
foreach($R in $Pre.captures){Add-Binding $R.original $R.sha256 $null $true;Add-Binding $R.copy $R.sha256 $null $false}
$OldG=Read-Control $OldGate;Need (@($OldG.metadata_control_bindings).Count -eq 5) 'OLD04_CONTROL_COUNT'
foreach($R in $OldG.metadata_control_bindings){Add-Binding $R.path $R.sha256 $null $true}
foreach($R in $Handoff.bindings){Add-Binding $R.path $R.sha256 $R.bytes $R.capture}
foreach($Pair in @(@($HandoffPath,$HandoffSha),@($ReviewPath,$IndependentReviewSha256),@($TrustPath,$TrustReviewSha256))){Add-Binding $Pair[0] $Pair[1] $null $true}
$Bindings=@($RowsByPath.Values|Sort-Object { $_.path.ToLowerInvariant() })
Need ($Bindings.Count -eq $RowsByPath.Count) 'EXACT_UNION_CARDINALITY'
$RuntimeCount=@($Bindings|Where-Object {$_.path.StartsWith($RuntimePrefix,[StringComparison]::OrdinalIgnoreCase)}).Count
Need ($RuntimeCount -eq 972) 'INHERITED_RUNTIME_PATH_COUNT_CHANGED'
Check $Python $PythonSha;Check $Checker $CheckerSha
foreach($R in $Bindings){Check-Row $R}
$ArchiveCount=Archives
foreach($N in @('receipt.json','POST.json','checker_FIN.json','coefficient_result.json')){Need (-not(Test-Path -LiteralPath (Join-Path $OldActual $N))) 'OLD04_RESULT_RETROSPECTIVELY_ADDED'}
$OldOutputPaths=@($Closed.output_bindings|ForEach-Object {Key $_.path}|Sort-Object)
$ActualOldPaths=@(Get-ChildItem -LiteralPath $OldActual -Recurse -File -Force|ForEach-Object {Key $_.FullName}|Sort-Object)
Need (@(Compare-Object $OldOutputPaths $ActualOldPaths).Count -eq 0) 'OLD04_OUTPUT_SET_CHANGED'
if(-not(Test-Path -LiteralPath $Metadata)){New-Item -ItemType Directory -Path $Metadata|Out-Null}
New-Item -ItemType Directory -Path $MetadataActual|Out-Null
$Started=[DateTime]::UtcNow.ToString('o')
Write-New (Join-Path $MetadataActual 'START.json') ([ordered]@{utc=$Started;scope='METADATA_ONLY_NOT_NUMERIC';helper_invocations=1;source_handoff_sha256=$HandoffSha})
$Completed=$false;$Failure=$null
try{
 $Manifest=[ordered]@{schema='ROUND22_NATIVE_NUMERIC05_CHECKER_ONLY_MANIFEST';status='METADATA_ONLY';source_handoff_sha256=$HandoffSha;binding_count=$Bindings.Count;bindings=$Bindings}
 Write-New $ManifestOut $Manifest
 $ManifestSha=Digest $ManifestOut
 $Prep=[ordered]@{schema='ROUND22_NATIVE_NUMERIC05_CHECKER_ONLY_PREPARATION';status='NATIVE_NUMERIC05_CHECKER_ONLY_METADATA_PREPARED';scope='NATIVE_NUMERIC05_CHECKER_ONLY_N1E8';fixed_N=100000000;fixed_M=100000000;fixed_K=134217728;fixed_S='288230376151711744';max_children=1;max_retries=0;wall_seconds=3600;checker_deadline_parent_offset_seconds=3300;FIN_POST_reserve_seconds=300;output_bytes=2147483648;commit_job_bytes=2147483648;rss_per_process_monitor_bytes=2147483648;sampled_job_rss_cap_bytes=4294967296;max_active_job_processes=16;max_total_job_processes=32;job_limit_flags_requested=8968;working_set_limit_flag_requested=$false;rss_os_enforced=$false;rss_control='SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM';log_bytes=1048576;metadata_bytes=16777216;capture_bytes=33554432;compiler_invocations=0;producer_invocations=0;manifest_path=$LocalManifest;manifest_sha256=$ManifestSha;binding_count=$Bindings.Count;source_handoff_sha256=$HandoffSha;parent_sha256=$ParentSha;numeric_execution_plan_sha256=(Digest $PlanPath);numeric_trust_policy_sha256=$PolicySha;build_receipt_sha256=$BuildReceiptSha;checker_binary_sha256=$CheckerSha;old04_external_closure_sha256=$Links[$OldClosure];independent_numeric_source_review_path=$ReviewPath;independent_numeric_source_review_sha256=$IndependentReviewSha256;numeric_trust_review_path=$TrustPath;numeric_trust_review_sha256=$TrustReviewSha256;canonical_python_path=$Python;canonical_python_sha256=$PythonSha;inherited_runtime_bindings=$RuntimeCount;protected_archives=$ArchiveCount;old04_inputs=6456;old04_capture_pairs=66;old04_output_bindings=83;old04_metadata_controls=5;payload_bytes_mathematically_validated=$false;candidate_actual_created=$false;numeric_authorization=$false;native_Lean_refinement=$false;D_N=$false;WIN=$false}
 Write-New $PreparationOut $Prep
 $PrepSha=Digest $PreparationOut
 foreach($Pair in @(@($ManifestOut,$LocalManifest),@($PreparationOut,$LocalPreparation))){$Data=[IO.File]::ReadAllBytes($Pair[0]);$Stream=[IO.File]::Open($Pair[1],[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::None);try{$Stream.Write($Data,0,$Data.Length)}finally{$Stream.Dispose()};Need ((Digest $Pair[0]) -eq (Digest $Pair[1])) 'EXCLUSIVE_LOCAL_COPY_CHANGED'}
 # All original source/old outputs/archive bytes checked again. No big input
 # is copied into an ACTUAL05 here; that belongs to the future gated parent.
 foreach($R in $Bindings){Check-Row $R}
 Need ((Archives) -eq $ArchiveCount) 'POST_ARCHIVE_COUNT'
 Check $ReviewPath $IndependentReviewSha256;Check $TrustPath $TrustReviewSha256;Check $HandoffPath $HandoffSha
 Write-New $ConservationOut ([ordered]@{schema='ROUND22_NATIVE_NUMERIC05_METADATA_PHYSICAL_CONSERVATION';all_inputs_intact=$true;binding_count=$Bindings.Count;runtime_bindings=$RuntimeCount;old04_input_count=6456;old04_capture_pairs=66;old04_output_bindings=83;old04_metadata_controls=5;archives=$ArchiveCount;payload_scope='INPUT_BYTES_SHA_ONLY_NOT_MATH_VALIDATION';old04_parent_receipt_CREATED=$false;old04_POST_CREATED=$false;candidate_actual_created=$false;native_invocations=0})
 Write-New $ReadsOut ([ordered]@{schema='ROUND22_NATIVE_NUMERIC05_METADATA_READ_RECEIPT';scope='PARSED_CONTROL_METADATA_AND_PHYSICAL_BYTE_SHA;NOT_RAW_FULL_LARGE_INVENTORIES';binding_count=$Bindings.Count;runtime_bindings=$RuntimeCount;archives=$ArchiveCount;source_handoff_sha256=$HandoffSha;review_sha256=$IndependentReviewSha256;trust_sha256=$TrustReviewSha256;helper_source_sha256=(Digest $MyInvocation.MyCommand.Path);payload_scope='BYTES_SHA_ONLY_NO_PARSE';numeric_candidate_imports=0;native_calls=0;compiler_calls=0;gate_created=$false})
 Write-New $ReceiptOut ([ordered]@{schema='ROUND22_NATIVE_NUMERIC05_METADATA_EXECUTION_RECEIPT';status='NATIVE_NUMERIC05_CHECKER_ONLY_METADATA_PREPARED';utc_START=$Started;utc_FIN=[DateTime]::UtcNow.ToString('o');helper_invocations=1;retry_count=0;binding_count=$Bindings.Count;runtime_bindings=$RuntimeCount;protected_archives=$ArchiveCount;preparation_sha256=$PrepSha;manifest_sha256=$ManifestSha;source_handoff_sha256=$HandoffSha;review_sha256=$IndependentReviewSha256;trust_sha256=$TrustReviewSha256;conservation_sha256=(Digest $ConservationOut);reads_sha256=(Digest $ReadsOut);candidate_actual_created=$false;numeric_calls=0;compiler_calls=0;gate_created=$false;D_N=$false;WIN=$false})
 $Completed=$true
}catch{$Failure=$_.Exception.GetType().FullName+': '+$_.Exception.Message}
finally{Write-New (Join-Path $MetadataActual 'FIN.json') ([ordered]@{utc_START=$Started;utc_FIN=[DateTime]::UtcNow.ToString('o');status=if($Completed){'METADATA_PREPARED'}else{'METADATA_FAILURE_NO_RETRY'};error=$Failure;helper_invocations=1;retry_count=0;numeric_calls=0;compiler_calls=0})}
if(-not$Completed){throw $Failure}
[ordered]@{status=$Prep.status;preparation_path=$PreparationOut;preparation_sha256=(Digest $PreparationOut);manifest_path=$ManifestOut;manifest_sha256=(Digest $ManifestOut);receipt_path=$ReceiptOut;receipt_sha256=(Digest $ReceiptOut);binding_count=$Bindings.Count;runtime_bindings=$RuntimeCount;archives=$ArchiveCount;actual_candidate_created=$false;numeric_calls=0}|ConvertTo-Json
