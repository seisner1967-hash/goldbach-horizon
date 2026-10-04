param(
 [Parameter(Mandatory=$true)][string]$QuiescenceEvidencePath,
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{64}$')][string]$QuiescenceEvidenceSha256,
 [Parameter(Mandatory=$true)][int]$ParentExitCode,
 [Parameter(Mandatory=$true)][string]$SessionClosedToolChunk
)
# SOURCE ONLY. ONE metadata invocation AFTER ROOT FULL reading/authorization
# and external observation of session completion and known PID absence.
# Never invokes a candidate, APIs, native primitives or a coefficient oracle.
$ErrorActionPreference='Stop'
$TaskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$TaskHere=Split-Path -Parent $MyInvocation.MyCommand.Path
$Consumer=Join-Path $TaskBase 'round22\role3\native_numeric_consumer_source01'
$Actual=Join-Path $Consumer 'actual_numeric04_attempt01'
$GatePath=Join-Path $TaskBase '.arbor\sessions\parity\.coordinator\messages\round22_native_numeric04_authorization.json'
$GateSha='b5dc57f1afa98304645f9e62505026c805c7a536946a15eedec399922aeba932'
$ManifestPath=Join-Path $Consumer 'numeric_manifest22.json'
$ManifestSha='43d746dee55a02c6fc49032be240badf315e9525d67e12fe05a0d6c52cb5bcad'
$PreparationPath=Join-Path $Consumer 'numeric_preparation22.json'
$PreparationSha='97a05adf8c9acd4165b9210ae9a9dce6bf55a6ef4a2f038e6dd1d1aa0ae8f5c6'
$PrePath=Join-Path $Actual 'PRE.json'
$PreSha='2263e2fa6b54445a31ac910e213a417b07cee7468c103726f12f8736e46d1d6d'
$RegistryPath=Join-Path $TaskBase 'round22\previous_artifacts_sha256.json'
$RegistrySha='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
$ClosurePath=Join-Path $TaskHere 'numeric_execution_closure22.json'
$EvidenceBindingsPath=Join-Path $TaskHere 'closure_evidence_bindings22.json'
$ActualMetadata=Join-Path $TaskHere 'actual_closure01_attempt01'
function Need([bool]$Condition,[string]$Message){if(-not$Condition){throw $Message}}
function Digest([string]$TaskPath){return (Get-FileHash -LiteralPath $TaskPath -Algorithm SHA256).Hash.ToLowerInvariant()}
function Check([string]$TaskPath,[string]$Expected){Need ((Digest $TaskPath) -eq $Expected) ('BYTE_CHANGED '+$TaskPath)}
function Read-Control([string]$TaskPath){
 $Item=Get-Item -LiteralPath $TaskPath
 Need (-not$Item.PSIsContainer -and $Item.Length -le 16777216) ('CONTROL_SIZE '+$TaskPath)
 return (Get-Content -LiteralPath $TaskPath -Raw | ConvertFrom-Json)
}
function Row([string]$TaskPath){
 $Item=Get-Item -LiteralPath $TaskPath
 Need (-not$Item.PSIsContainer -and ($Item.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0) ('REPARSE_OR_DIRECTORY '+$TaskPath)
 return [ordered]@{path=$Item.FullName;bytes=[long]$Item.Length;sha256=(Digest $Item.FullName)}
}
function Check-Row($Binding){
 Need ((Get-Item -LiteralPath $Binding.path).Length -eq $Binding.bytes) ('SIZE_CHANGED '+$Binding.path)
 Check $Binding.path $Binding.sha256
}
function Write-New([string]$TaskPath,$Value){
 $Bytes=[Text.UTF8Encoding]::new($false).GetBytes(($Value | ConvertTo-Json -Depth 14)+[Environment]::NewLine)
 $Stream=[IO.File]::Open($TaskPath,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::None)
 try{$Stream.Write($Bytes,0,$Bytes.Length)}finally{$Stream.Dispose()}
}
foreach($TaskPath in @($ClosurePath,$EvidenceBindingsPath,$ActualMetadata)){
 Need (-not(Test-Path -LiteralPath $TaskPath)) ('EXCLUSIVE_CLOSURE_PATH_EXISTS '+$TaskPath)
}
# External quiescence evidence is mandatory. This helper neither kills nor
# polls processes and does not manufacture a parent receipt after watchdog.
Check $QuiescenceEvidencePath $QuiescenceEvidenceSha256
$Quiescence=Read-Control $QuiescenceEvidencePath
Need ($Quiescence.schema -eq 'ROUND22_NATIVE_NUMERIC04_QUIESCENCE_METADATA' -and
      $Quiescence.gate_sha256 -eq $GateSha -and $Quiescence.session_id -eq 17351 -and
      $Quiescence.parent_session_complete -is [bool] -and $Quiescence.parent_session_complete -eq $true -and
      $Quiescence.known_created_child_pids_absent -is [bool] -and $Quiescence.known_created_child_pids_absent -eq $true -and
      $Quiescence.parent_exit_code -eq $ParentExitCode -and $Quiescence.session_closed_tool_chunk -eq $SessionClosedToolChunk) 'NO_ACTUAL_EXTERNAL_QUIESCENCE_EVIDENCE'
New-Item -ItemType Directory -Path $ActualMetadata -ErrorAction Stop | Out-Null
$Started=[DateTime]::UtcNow.ToString('o')
Write-New (Join-Path $ActualMetadata 'START.json') ([ordered]@{utc=$Started;scope='CLOSURE_METADATA_ONLY_AFTER_EXTERNAL_QUIESCENCE';helper_invocations=1})
$Failure=$null
$Completed=$false
try{
 Check $GatePath $GateSha
 Check $ManifestPath $ManifestSha
 Check $PreparationPath $PreparationSha
 Check $PrePath $PreSha
 Check $RegistryPath $RegistrySha
 $Gate=Read-Control $GatePath
 $Manifest=Read-Control $ManifestPath
 $Pre=Read-Control $PrePath
 Need ($Gate.status -eq 'AUTHORIZED' -and $Gate.scope -eq 'NATIVE_NUMERIC04_FULL_N1E8_ONLY') 'GATE_SCOPE'
 Need ($Manifest.binding_count -eq 6456 -and @($Manifest.bindings).Count -eq 6456 -and
       $Pre.binding_count -eq 6456 -and @($Pre.captures).Count -eq 66 -and
       $Pre.gate_sha256 -eq $GateSha -and $Pre.preparation_sha256 -eq $PreparationSha -and
       $Pre.numeric_parent_invocations -eq 1) 'PRE_MANIFEST_SCOPE_CHANGED'
 Need (@($Gate.metadata_control_bindings).Count -eq 5) 'FIVE_METADATA_CONTROLS_REQUIRED'
 $KnownCreated=@()
 foreach($Label in @('producer','checker')){
  $CreatedPath=Join-Path $Actual ($Label+'_CREATED_SUSPENDED.json')
  if(Test-Path -LiteralPath $CreatedPath){$Created=Read-Control $CreatedPath;$KnownCreated += [int]$Created.pid}
 }
 Need ($KnownCreated.Count -ge 1 -and $KnownCreated.Count -le 2) 'CREATED_CHILD_COUNT'
 $ExpectedPids=@($KnownCreated | Sort-Object -Unique)
 $ObservedPids=@($Quiescence.known_created_child_pids | Sort-Object -Unique)
 Need ($ExpectedPids.Count -eq $ObservedPids.Count -and (@(Compare-Object $ExpectedPids $ObservedPids).Count -eq 0)) 'QUIESCENCE_PIDS_DO_NOT_MATCH_CALLBACKS'
 # Physical preservation is checked externally now. It is distinct from the
 # parent's earlier POST and remains so even after a watchdog stopped it.
 foreach($Binding in $Manifest.bindings){Check-Row $Binding}
 $CaptureBindings=@()
 foreach($Capture in $Pre.captures){
  Check $Capture.original $Capture.sha256
  Check $Capture.copy $Capture.sha256
  $CaptureBindings += [ordered]@{original=(Row $Capture.original);copy=(Row $Capture.copy)}
 }
 $MetadataControls=@()
 foreach($Control in $Gate.metadata_control_bindings){Check $Control.path $Control.sha256;$MetadataControls += Row $Control.path}
 $Registry=Read-Control $RegistryPath
 $ArchiveCount=0
 foreach($Property in $Registry.sha256.PSObject.Properties){
  $Archive=[IO.Path]::GetFullPath((Join-Path $TaskBase $Property.Name))
  Need ($Archive.StartsWith($TaskBase+'\',[StringComparison]::OrdinalIgnoreCase)) 'ARCHIVE_OUTSIDE_BASE'
  Check $Archive $Property.Value
  $ArchiveCount++
 }
 Need ($ArchiveCount -eq 3089) 'ARCHIVE_COUNT_CHANGED'
 $Outputs=@()
 foreach($Item in Get-ChildItem -LiteralPath $Actual -File -Recurse -Force){
  Need (($Item.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0) 'OUTPUT_REPARSE_POINT'
  $Outputs += Row $Item.FullName
 }
 # No binary payload is parsed. No C_A/C_B, radius, CRT, log or interval
 # arithmetic is recomputed; any coefficient values belong to the parent.
 $ReceiptPath=Join-Path $Actual 'receipt.json'
 $PostPath=Join-Path $Actual 'POST.json'
 $CoefficientPath=Join-Path $Actual 'coefficient_result.json'
 $WatchdogPath=Join-Path $Actual 'WATCHDOG_TERMINATION_REQUEST.json'
 $HasReceipt=Test-Path -LiteralPath $ReceiptPath
 $HasPost=Test-Path -LiteralPath $PostPath
 $HasCoefficient=Test-Path -LiteralPath $CoefficientPath
 $HasWatchdog=Test-Path -LiteralPath $WatchdogPath
 $Receipt=$null;$Post=$null;$ActualReceiptSha=$null
 if($HasReceipt){$Receipt=Read-Control $ReceiptPath;$ActualReceiptSha=Digest $ReceiptPath}
 if($HasPost){$Post=Read-Control $PostPath}
 $ParentPostVerified=$HasPost -and $null -eq $Post.conservation_error -and $Post.all_bindings_controls_originals_copies_archives_intact -eq $true
 $Success=$HasReceipt -and $ParentExitCode -eq 0 -and -not$HasWatchdog -and $ParentPostVerified -and $HasCoefficient -and
  $Receipt.status -eq 'PAPER_AUDITED_EXACT_INTEGER_PROJECTION_AUX_CHECKED_PENDING_NATIVE_REFINEMENT' -and
  $Receipt.parent_invocations -eq 1 -and $Receipt.retry_count -eq 0 -and $Receipt.children_returned -eq 2 -and
  $Receipt.produced_binary_processes_created -eq 2 -and $Receipt.produced_binary_processes_resumed -eq 2 -and
  $null -eq $Receipt.failure -and $null -eq $Receipt.conservation_error -and $Receipt.coefficient_result_present -eq $true
 if($Success){
  foreach($Label in @('producer','checker')){
   $Fin=Read-Control (Join-Path $Actual ($Label+'_FIN.json'))
   Need ($Fin.exit_code -eq 0 -and $Fin.wait_signalled -eq $true -and $Fin.job_empty_confirmed -eq $true -and
         $null -eq $Fin.termination_reason -and $null -eq $Fin.api_or_control_error -and @($Fin.pipe_faults).Count -eq 0) 'CLAIMED_SUCCESS_WITH_UNCLOSED_CHILD'
  }
 }
 if($HasReceipt){Need ($Receipt.parent_invocations -eq 1 -and $Receipt.retry_count -eq 0 -and $Receipt.gate_sha256 -eq $GateSha) 'ACTUAL_PARENT_RECEIPT_SCOPE'}
 foreach($Binding in $Outputs){Check-Row $Binding}
 foreach($Control in $MetadataControls){Check-Row $Control}
 Check $GatePath $GateSha
 Check $ManifestPath $ManifestSha
 Check $PrePath $PreSha
 Check $QuiescenceEvidencePath $QuiescenceEvidenceSha256
 Write-New $EvidenceBindingsPath ([ordered]@{schema='ROUND22_NATIVE_NUMERIC04_CLOSURE_EVIDENCE_BINDINGS';
  scope='EXTERNAL_PHYSICAL_METADATA_AFTER_QUIESCENCE';captures=$CaptureBindings;metadata_controls=$MetadataControls;
  gate=(Row $GatePath);manifest=(Row $ManifestPath);preparation=(Row $PreparationPath);PRE=(Row $PrePath);
  quiescence_evidence=(Row $QuiescenceEvidencePath);output_bindings=$Outputs;native_invocations_here=0})
 $Closure=[ordered]@{schema='ROUND22_NATIVE_NUMERIC04_EXTERNAL_METADATA_CLOSURE';
  status=if($Success){'CLOSED_PARENT_PAPER_AUX_RESULT_PENDING_NATIVE_REFINEMENT'}else{'CLOSED_STOP_NO_MATHEMATICAL_VERDICT'};
  utc=[DateTime]::UtcNow.ToString('o');gate_sha256=$GateSha;session_id=17351;session_closed_tool_chunk=$SessionClosedToolChunk;
  actual_parent_receipt_sha256=$ActualReceiptSha;actual_parent_receipt_present=$HasReceipt;parent_exit_code=$ParentExitCode;
  parent_invocations=1;retry_count=0;produced_binary_processes_created=$KnownCreated.Count;
  actual_processes_quiescent=$true;quiescence_scope='EXTERNAL_SESSION_CLOSED_AND_CALLBACK_PIDS_ABSENT;NOT_UNIVERSAL_PROCESS_GRAPH_PROOF';
  quiescence_evidence_path=$QuiescenceEvidencePath;quiescence_evidence_sha256=$QuiescenceEvidenceSha256;
  all_current_bytes_preserved=$true;inputs_verified=6456;capture_original_copy_pairs_verified=66;
  protected_archives_verified=$ArchiveCount;metadata_controls_verified=5;output_bindings=$Outputs;
  external_physical_preservation_distinct_from_parent_POST=$true;parent_POST_verified=$ParentPostVerified;
  parent_POST_present=$HasPost;watchdog_present=$HasWatchdog;coefficient_report_present=$HasCoefficient;
  parent_result_status=if($HasReceipt){$Receipt.status}else{$null};parent_failure=if($HasReceipt){$Receipt.failure}else{$null};
  coefficient_or_interval_arithmetic_recomputed_here=$false;synthetic_parent_receipt_created=$false;
  mathematical_falsity_established=$false;mutant_runs=0;compiler_invocations=0;native_invocations_here=0;
  native_Lean_refinement=$false;B40_real_log_refinement_Lean=$false;effective_loads_observed=$false;
  universal_loader_closure_verified=$false;spectral_H1=$false;D_N=$false;WIN=$false}
 Write-New $ClosurePath $Closure
 $Completed=$true
}catch{$Failure=$_.Exception.GetType().FullName+': '+$_.Exception.Message}
finally{
 Write-New (Join-Path $ActualMetadata 'FIN.json') ([ordered]@{utc_START=$Started;utc_FIN=[DateTime]::UtcNow.ToString('o');
  status=if($Completed){'EXTERNAL_METADATA_CLOSURE_COMPLETE'}else{'EXTERNAL_METADATA_FAILURE_NO_RETRY'};
  helper_invocations=1;retry_count=0;error=$Failure;parent_or_native_invocations_here=0;D_N=$false;WIN=$false})
}
if(-not$Completed){throw $Failure}
[ordered]@{closure_path=$ClosurePath;closure_sha256=(Digest $ClosurePath);evidence_bindings_path=$EvidenceBindingsPath;
 evidence_bindings_sha256=(Digest $EvidenceBindingsPath);status=$Closure.status;native_invocations_here=0} | ConvertTo-Json
