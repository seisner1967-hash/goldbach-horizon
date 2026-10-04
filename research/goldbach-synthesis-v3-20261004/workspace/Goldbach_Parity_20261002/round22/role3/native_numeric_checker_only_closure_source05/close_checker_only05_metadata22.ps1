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
$Consumer=Join-Path $TaskBase 'round22\role3\native_numeric_checker_only_consumer_source05_revision02'
$Actual=Join-Path $Consumer 'actual_numeric05_checker_only_attempt01'
$GatePath=Join-Path $TaskBase '.arbor\sessions\parity\.coordinator\messages\round22_native_numeric05_checker_only_authorization.json'
$GateSha='e417407398e27d22a19a932bed6da09f09b0866bce8abbb2c08cfaaee28551cc'
$ManifestPath=Join-Path $Consumer 'numeric_checker_only_manifest22.json'
$ManifestSha='a22738cdeabf910caa822ead788774cd4b574d54d4bb7a0aedaa242236d7e0d7'
$PreparationPath=Join-Path $Consumer 'numeric_checker_only_preparation22.json'
$PreparationSha='006a9177e9edeb07eb636ab11196b3cc17decbbdca008de066dc1ad85aadfb25'
$PrePath=Join-Path $Actual 'PRE.json'
$PreSha='48eb512cf9725773ce510d0163d23f54b6ba97f0c899f9fa00fc9a7d8e61575a'
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
Need ($Quiescence.schema -eq 'ROUND22_NATIVE_NUMERIC05_CHECKER_ONLY_QUIESCENCE_METADATA' -and
      $Quiescence.gate_sha256 -eq $GateSha -and $Quiescence.session_id -eq 81191 -and
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
 Need ($Gate.status -eq 'AUTHORIZED' -and $Gate.scope -eq 'NATIVE_NUMERIC05_CHECKER_ONLY_N1E8') 'GATE_SCOPE'
 Need ($Manifest.binding_count -eq 6576 -and @($Manifest.bindings).Count -eq 6576 -and
       $Pre.binding_count -eq 6576 -and @($Pre.captures).Count -eq 109 -and
       @($Pre.payload_original_copy_bindings).Count -eq 3 -and
       $Pre.gate_sha256 -eq $GateSha -and $Pre.preparation_sha256 -eq $PreparationSha -and
       $Pre.numeric_parent_invocations -eq 1 -and $Pre.compiler_invocations -eq 0 -and
       $Pre.producer_invocations -eq 0) 'PRE_MANIFEST_SCOPE_CHANGED'
 Need (@($Gate.metadata_control_bindings).Count -eq 5) 'FIVE_METADATA_CONTROLS_REQUIRED'
 $KnownCreated=@()
 foreach($Label in @('checker')){
  $CreatedPath=Join-Path $Actual ($Label+'_CREATED_SUSPENDED.json')
  if(Test-Path -LiteralPath $CreatedPath){$Created=Read-Control $CreatedPath;$KnownCreated += [int]$Created.pid}
 }
 Need ($KnownCreated.Count -eq 1 -and $KnownCreated[0] -eq 23088) 'ACTUAL_CREATED_CHECKER_PID_CHANGED'
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
 $PayloadPairs=@()
 foreach($Pair in $Pre.payload_original_copy_bindings){
  Check $Pair.original $Pair.sha256
  Check $Pair.copy $Pair.sha256
  Need ((Get-Item -LiteralPath $Pair.original).Length -eq $Pair.bytes -and
        (Get-Item -LiteralPath $Pair.copy).Length -eq $Pair.bytes) 'PAYLOAD_ORIGINAL_COPY_SIZE'
  $PayloadPairs += [ordered]@{original=(Row $Pair.original);copy=(Row $Pair.copy);mathematical_validation_here=$false}
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
 $Old04=Join-Path $TaskBase 'round22\role3\native_numeric_consumer_source01\actual_numeric04_attempt01'
 $Old04ClosurePath=Join-Path $TaskBase 'round22\role3\native_numeric_closure_source01\numeric_execution_closure22.json'
 Check $Old04ClosurePath 'a99a5e58768d09a16c7a1ae248448be41016cac228fc57c69372d6abb2774df3'
 $Old04Closed=Read-Control $Old04ClosurePath
 $Old04Expected=@($Old04Closed.output_bindings|ForEach-Object{$_.path.ToLowerInvariant()}|Sort-Object)
 $Old04Observed=@(Get-ChildItem -LiteralPath $Old04 -File -Recurse -Force|ForEach-Object{$_.FullName.ToLowerInvariant()}|Sort-Object)
 Need ($Old04Expected.Count -eq 83 -and (@(Compare-Object $Old04Expected $Old04Observed).Count -eq 0)) 'OLD04_OUTPUT_PATH_SET_CHANGED'
 foreach($Missing in @('receipt.json','POST.json','checker_FIN.json','coefficient_result.json')){
  Need (-not(Test-Path -LiteralPath (Join-Path $Old04 $Missing))) 'OLD04_MISSING_RESULT_RETROSPECTIVELY_ADDED'
 }
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
 $ParentFinPath=Join-Path $Actual 'parent_FIN.json'
 $HasReceipt=Test-Path -LiteralPath $ReceiptPath
 $HasPost=Test-Path -LiteralPath $PostPath
 $HasCoefficient=Test-Path -LiteralPath $CoefficientPath
 $HasWatchdog=Test-Path -LiteralPath $WatchdogPath
 $HasParentFin=Test-Path -LiteralPath $ParentFinPath
 $ParentFin=$null
 if($HasParentFin){$ParentFin=Read-Control $ParentFinPath}
 $Receipt=$null;$Post=$null;$ActualReceiptSha=$null
 if($HasReceipt){$Receipt=Read-Control $ReceiptPath;$ActualReceiptSha=Digest $ReceiptPath}
 if($HasPost){$Post=Read-Control $PostPath}
 $ParentPostVerified=$HasPost -and $null -eq $Post.conservation_error -and
  $Post.all_bindings_controls_originals_copies_payloads_archives_intact -eq $true -and
  $Post.backend_child_quiescence_confirmed -eq $true
 $Success=$HasReceipt -and $ParentExitCode -eq 0 -and -not$HasWatchdog -and $ParentPostVerified -and $HasCoefficient -and
  $HasParentFin -and $ParentFin.exit_code -eq 0 -and $ParentFin.parent_invocations -eq 1 -and
  $ParentFin.retry_count -eq 0 -and $ParentFin.child_quiescence_confirmed_by_backend -eq $true -and
  $Receipt.status -eq 'PAPER_AUDITED_EXACT_INTEGER_PROJECTION_AUX_CHECKED_PENDING_NATIVE_REFINEMENT' -and
  $Receipt.parent_invocations -eq 1 -and $Receipt.retry_count -eq 0 -and $Receipt.children_returned -eq 1 -and
  $Receipt.produced_binary_processes_created -eq 1 -and $Receipt.produced_binary_processes_resumed -eq 1 -and
  $Receipt.compiler_invocations -eq 0 -and $Receipt.producer_invocations -eq 0 -and
  $Receipt.backend_child_quiescence_confirmed -eq $true -and $Receipt.parent_POST_present -eq $true -and
  $null -eq $Receipt.failure -and $null -eq $Receipt.conservation_error -and $Receipt.coefficient_result_present -eq $true
 if($Success){
  foreach($Label in @('checker')){
   $Fin=Read-Control (Join-Path $Actual ($Label+'_FIN.json'))
   Need ($Fin.exit_code -eq 0 -and $Fin.wait_signalled -eq $true -and $Fin.job_empty_confirmed -eq $true -and
         $null -eq $Fin.termination_reason -and $null -eq $Fin.api_or_control_error -and @($Fin.pipe_faults).Count -eq 0) 'CLAIMED_SUCCESS_WITH_UNCLOSED_CHILD'
  }
 }
 if($HasReceipt){Need ($Receipt.parent_invocations -eq 1 -and $Receipt.retry_count -eq 0 -and
  $Receipt.gate_sha256 -eq $GateSha -and $Receipt.compiler_invocations -eq 0 -and
  $Receipt.producer_invocations -eq 0) 'ACTUAL_PARENT_RECEIPT_SCOPE'}
 foreach($Binding in $Outputs){Check-Row $Binding}
 foreach($Control in $MetadataControls){Check-Row $Control}
 Check $GatePath $GateSha
 Check $ManifestPath $ManifestSha
 Check $PrePath $PreSha
 Check $QuiescenceEvidencePath $QuiescenceEvidenceSha256
 Write-New $EvidenceBindingsPath ([ordered]@{schema='ROUND22_NATIVE_NUMERIC05_CHECKER_ONLY_CLOSURE_EVIDENCE_BINDINGS';
  scope='EXTERNAL_PHYSICAL_METADATA_AFTER_QUIESCENCE';captures=$CaptureBindings;payload_original_copy_pairs=$PayloadPairs;metadata_controls=$MetadataControls;
  gate=(Row $GatePath);manifest=(Row $ManifestPath);preparation=(Row $PreparationPath);PRE=(Row $PrePath);
  quiescence_evidence=(Row $QuiescenceEvidencePath);output_bindings=$Outputs;native_invocations_here=0})
 $Closure=[ordered]@{schema='ROUND22_NATIVE_NUMERIC05_CHECKER_ONLY_EXTERNAL_METADATA_CLOSURE';
  status=if($Success){'CLOSED_PARENT_PAPER_AUX_RESULT_PENDING_NATIVE_REFINEMENT'}else{'CLOSED_STOP_NO_MATHEMATICAL_VERDICT'};
  utc=[DateTime]::UtcNow.ToString('o');gate_sha256=$GateSha;session_id=81191;session_closed_tool_chunk=$SessionClosedToolChunk;
  actual_parent_receipt_sha256=$ActualReceiptSha;actual_parent_receipt_present=$HasReceipt;parent_exit_code=$ParentExitCode;
  parent_invocations=1;retry_count=0;produced_binary_processes_created=$KnownCreated.Count;
  actual_processes_quiescent=$true;quiescence_scope='EXTERNAL_SESSION_CLOSED_AND_CALLBACK_PIDS_ABSENT;NOT_UNIVERSAL_PROCESS_GRAPH_PROOF';
  quiescence_evidence_path=$QuiescenceEvidencePath;quiescence_evidence_sha256=$QuiescenceEvidenceSha256;
  all_current_bytes_preserved=$true;inputs_verified=6576;capture_original_copy_pairs_verified=109;
  payload_original_copy_pairs_verified=3;producer_invocations=0;compiler_processes_created=0;
  old04_outputs_preserved=83;old04_missing_receipt_POST_checkerFIN_coefficient_still_absent=$true;
  protected_archives_verified=$ArchiveCount;metadata_controls_verified=5;output_bindings=$Outputs;
  external_physical_preservation_distinct_from_parent_POST=$true;parent_POST_verified=$ParentPostVerified;
  parent_POST_present=$HasPost;parent_FIN_present=$HasParentFin;watchdog_present=$HasWatchdog;coefficient_report_present=$HasCoefficient;
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
