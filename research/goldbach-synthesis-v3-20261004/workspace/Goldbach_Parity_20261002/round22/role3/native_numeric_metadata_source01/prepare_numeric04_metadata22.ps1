param(
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{64}$')][string]$IndependentReviewSha256,
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{64}$')][string]$TrustReviewSha256
)
# SOURCE ONLY. Do not invoke until ROOT reads this whole frozen helper and
# authorizes one metadata invocation with the two actual independent reviews.
# No Python/native/Lean/PE-parser/API/compiler invocation exists in this source.
$ErrorActionPreference='Stop'
$TaskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$TaskHere=Split-Path -Parent $MyInvocation.MyCommand.Path
$SourceDir=Join-Path $TaskBase 'round22\role3\native_numeric_consumer_source01'
$NativeDir=Join-Path $TaskBase 'round22\role4\circle_native_revision02'
$BuildDir=Join-Path $TaskBase 'round22\role4\circle_native_build_source04'
$BuildActual=Join-Path $BuildDir 'actual_build04_attempt01'
$BuildMeta=Join-Path $TaskBase 'round22\role3\native_build_metadata04'
$SourceHandoffPath=Join-Path $SourceDir 'source_handoff22.json'
$SourceHandoffSha='0c839fc7c602c52c6c3f0d47d6f643342c8641a0cc8527b656a4e7cf70e74616'
$BuilderHandoffPath=Join-Path $TaskHere 'metadata_source_handoff22.json'
$BuildManifestPath=Join-Path $BuildMeta 'build_manifest22.json'
$BuildManifestSha='24ea81c9ae7134f71837baed91dabc9c64f45a2438ca6223e1aedc2154a85c2f'
$BuildClosurePath=Join-Path $BuildMeta 'build_execution_closure22_revision02.json'
$BuildClosureSha='dd506cebebcdbf7c75fd138d26cfb744552bdd6912e3cc37fbaa3a58fd8c0c15'
$BuildPrePath=Join-Path $BuildActual 'PRE.json'
$BuildPreSha='e751361aa2e9b20b7fae95b8c0fdda731338a0b7fb88c1f3aed4fb72d7ecc676'
$BuildReceiptPath=Join-Path $NativeDir 'build_receipt04.json'
$BuildReceiptSha='04ce22f9ee05215ee9c7c335b41755b1da4e001a82fa20085cfe7dccca1a7fc8'
$BuildPlanPath=Join-Path $BuildDir 'build_execution_plan22.json'
$BuildPlanSha='538cc14faf3466bb8a0505e8f6aae3007fc84b2b6246afb2da55d37be5718156'
$ParentPath=Join-Path $SourceDir 'run_native04_once22.py'
$ParentSha='97473b226ce5206e021e444720651e00ca1fdb4c1c1052e20db60d4effec3f55'
$PlanPath=Join-Path $SourceDir 'numeric_execution_plan22.json'
$PlanSha='c66808e4cd7312d76002559afccf909fdb5b6aa1e706301fc88813dcb519aaeb'
$PolicyPath=Join-Path $SourceDir 'numeric_trust_policy22.json'
$PolicySha='c6c97d0ef8846bbabb6db2ae7544de4aec631403c6f60ca460983c334059ebce'
$BackendPath=Join-Path $BuildDir 'windows_build_job22.py'
$BackendSha='88d857ce33eece8f90906bc5088d5cac905b868e60ede1b6439b1a3af3126cc3'
$ReviewPath=Join-Path $TaskBase 'round22\role4\native_numeric04_consumer_review_source01\source_review22.json'
$TrustPath=Join-Path $TaskBase 'round22\role4\native_numeric04_consumer_review_source01\trust_review22.json'
$CanonicalPython='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$PythonSha='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
$RegistryPath=Join-Path $TaskBase 'round22\previous_artifacts_sha256.json'
$RegistrySha='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
$BinaryPaths=@((Join-Path $NativeDir 'build-final04\producer_dit22.exe'),(Join-Path $NativeDir 'build-final04\checker_dif22.exe'))
$BinaryShas=@('44d2d571a0190f7dbbb975225559d16a012693bda4197738e6311c14892cadb0','2e7e095c2972fea09ee26500df9dae207ff52497d0f61f2052d76d464ebe6990')
$BinaryBytes=@(3649966,3669445)
$CppPaths=@((Join-Path $NativeDir 'producer_dit22.cpp'),(Join-Path $NativeDir 'checker_dif22.cpp'))
$CppShas=@('bdb7b022ae20ed8dce02959b77db62ca690a9798393292db62edf262d938ed74','4275ef5afc07f23c2d4b860de8f452ff1e2c07e8ab0d01686c16bdb0d09fe0eb')
$ManifestPath=Join-Path $TaskHere 'numeric_manifest22.json'
$PreparationPath=Join-Path $TaskHere 'numeric_preparation22.json'
$ConservationPath=Join-Path $TaskHere 'metadata_conservation22.json'
$ExecutionReceiptPath=Join-Path $TaskHere 'metadata_execution_receipt22.json'
$MetadataReadsPath=Join-Path $TaskHere 'metadata_read_receipts22.json'
$LocalManifest=Join-Path $SourceDir 'numeric_manifest22.json'
$LocalPreparation=Join-Path $SourceDir 'numeric_preparation22.json'
$FutureActual=Join-Path $SourceDir 'actual_numeric04_attempt01'
$FutureGate=Join-Path $TaskBase '.arbor\sessions\parity\.coordinator\messages\round22_native_numeric04_authorization.json'
$MetadataActual=Join-Path $TaskHere 'actual_metadata01_attempt01'
$Fixed=[ordered]@{
 scope='NATIVE_NUMERIC04_FULL_N1E8_ONLY';fixed_N=100000000;fixed_M=100000000;fixed_K=134217728;fixed_S='288230376151711744';
 max_children=2;max_retries=0;wall_seconds=3600;output_bytes=2147483648;commit_job_bytes=2147483648;
 rss_per_process_monitor_bytes=2147483648;sampled_job_rss_cap_bytes=4294967296;
 max_active_job_processes=16;max_total_job_processes=32;job_limit_flags_requested=8968;
 working_set_limit_flag_requested=$false;rss_os_enforced=$false;rss_control='SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM';
 log_bytes=1048576;metadata_bytes=16777216;capture_bytes=33554432;compiler_invocations=0
}

function Need([bool]$Condition,[string]$Message){if(-not$Condition){throw $Message}}
function Digest([string]$TaskPath){return (Get-FileHash -LiteralPath $TaskPath -Algorithm SHA256).Hash.ToLowerInvariant()}
function Check-Hash([string]$TaskPath,[string]$Expected){Need ((Digest $TaskPath) -eq $Expected) ('SHA_CHANGED '+$TaskPath)}
function Read-Metadata([string]$TaskPath){
 $Item=Get-Item -LiteralPath $TaskPath
 Need (-not$Item.PSIsContainer -and $Item.Length -le 16777216) ('CONTROL_FILE_SIZE '+$TaskPath)
 return (Get-Content -LiteralPath $TaskPath -Raw | ConvertFrom-Json)
}
function Path-Key([string]$TaskPath){return [IO.Path]::GetFullPath($TaskPath).ToLowerInvariant()}
function Write-Exclusive([string]$TaskPath,[byte[]]$TaskBytes){
 $Stream=[IO.File]::Open($TaskPath,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::None)
 try{$Stream.Write($TaskBytes,0,$TaskBytes.Length)}finally{$Stream.Dispose()}
}
function Write-Json([string]$TaskPath,$Value){
 $Text=($Value | ConvertTo-Json -Depth 10)+[Environment]::NewLine
 Write-Exclusive $TaskPath ([Text.UTF8Encoding]::new($false).GetBytes($Text))
}
function Check-Binding($Binding){
 $Item=Get-Item -LiteralPath $Binding.path
 Need (-not$Item.PSIsContainer -and ($Item.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0 -and
       $Item.Length -eq $Binding.bytes) ('SIZE_REPARSE_CHANGED '+$Binding.path)
 Check-Hash $Binding.path $Binding.sha256
}
$Map=@{}
$DuplicateOccurrences=0
function Add-Binding($Binding){
 $Key=Path-Key $Binding.path
 if($Map.ContainsKey($Key)){
  Need ($Map[$Key].bytes -eq $Binding.bytes -and $Map[$Key].sha256 -eq $Binding.sha256) ('CONFLICTING_BINDING '+$Binding.path)
  $Map[$Key].capture=[bool]($Map[$Key].capture -or $Binding.capture)
  $script:DuplicateOccurrences++
 }else{
  $Map[$Key]=[ordered]@{path=[IO.Path]::GetFullPath($Binding.path);bytes=[long]$Binding.bytes;sha256=$Binding.sha256;capture=[bool]$Binding.capture}
 }
}
function Add-Control([string]$TaskPath,[string]$Expected,[bool]$Capture){
 Check-Hash $TaskPath $Expected
 Add-Binding ([ordered]@{path=$TaskPath;bytes=(Get-Item -LiteralPath $TaskPath).Length;sha256=$Expected;capture=$Capture})
}
function Check-Archives{
 Check-Hash $RegistryPath $RegistrySha
 $Registry=Read-Metadata $RegistryPath
 $Count=0
 foreach($Property in $Registry.sha256.PSObject.Properties){
  $ArchivePath=[IO.Path]::GetFullPath((Join-Path $TaskBase $Property.Name))
  Need ($ArchivePath.StartsWith($TaskBase+'\',[StringComparison]::OrdinalIgnoreCase)) 'ARCHIVE_OUTSIDE_BASE'
  Check-Hash $ArchivePath $Property.Value
  $Count++
 }
 Need ($Count -eq 3089) 'ARCHIVE_COUNT_CHANGED'
 return $Count
}
function Require-False($Object,[string]$Name){Need ($Object.$Name -is [bool] -and $Object.$Name -eq $false) ('FALSE_FIELD_REQUIRED '+$Name)}

# No command below calls a candidate. ROOT's explicit metadata authorization
# is procedural and recorded in its own coordinator; no ROOT gate is forged.
foreach($Path in @($ManifestPath,$PreparationPath,$ConservationPath,$ExecutionReceiptPath,$MetadataReadsPath,$MetadataActual,
                  $LocalManifest,$LocalPreparation,$FutureActual,$FutureGate)){
 Need (-not(Test-Path -LiteralPath $Path)) ('EXCLUSIVE_PATH_ALREADY_EXISTS '+$Path)
}
New-Item -ItemType Directory -Path $MetadataActual -ErrorAction Stop | Out-Null
$Started=[DateTime]::UtcNow.ToString('o')
Write-Json (Join-Path $MetadataActual 'START.json') ([ordered]@{utc=$Started;scope='METADATA_ONLY';helper_invocations=1;retry_count=0;candidate_invocations=0})
$ErrorText=$null
$Completed=$false
try{
 Check-Hash $SourceHandoffPath $SourceHandoffSha
 Check-Hash $ParentPath $ParentSha
 Check-Hash $PlanPath $PlanSha
 Check-Hash $PolicyPath $PolicySha
 Check-Hash $BackendPath $BackendSha
 Check-Hash $ReviewPath $IndependentReviewSha256
 Check-Hash $TrustPath $TrustReviewSha256
 $Review=Read-Metadata $ReviewPath
 $Trust=Read-Metadata $TrustPath
 Need ($null -ne $Review.unresolved_execution_blockers -and $null -ne $Trust.unresolved_execution_blockers) 'MISSING_EXECUTION_BLOCKER_ARRAY'
 Need ($Review.status -eq 'NUMERIC04_SOURCE_REVIEW_CLOSED_WITH_NATIVE_REFINEMENT_OPEN' -and
       $Review.scope -eq $Fixed.scope -and $Review.reviewer -eq 'ROLE4' -and
       $Review.source_handoff_sha256 -eq $SourceHandoffSha -and $Review.parent_sha256 -eq $ParentSha -and
       $Review.backend_sha256 -eq $BackendSha -and @($Review.unresolved_execution_blockers).Count -eq 0) 'SOURCE_REVIEW_OPEN_OR_MISMATCH'
 Need ($Trust.status -eq 'NUMERIC04_FIXED_IMAGES_REVIEWED_WITH_EXPLICIT_WINDOWS_NATIVE_TRUST' -and
       $Trust.scope -eq $Fixed.scope -and $Trust.reviewer -eq 'ROLE4' -and $Trust.policy_sha256 -eq $PolicySha -and
       $Trust.backend_sha256 -eq $BackendSha -and $Trust.installed_Windows_and_frozen_native_runtime_trusted -is [bool] -and
       $Trust.installed_Windows_and_frozen_native_runtime_trusted -eq $true -and
       @($Trust.unresolved_execution_blockers).Count -eq 0 -and $Trust.produced_binary_invocations -eq 0) 'NUMERIC_TRUST_REVIEW_OPEN_OR_MISMATCH'
 foreach($Name in @('effective_loads_observed','universal_loader_closure_verified','all_non_OS_imports_bound','numeric_authorization')){
  Require-False $Trust $Name
 }
 foreach($Name in @('job_limit_flags_requested','working_set_limit_flag_requested','rss_os_enforced','rss_control')){
  Need ($Review.$Name -eq $Fixed[$Name] -and $Trust.$Name -eq $Fixed[$Name]) ('REVIEW_RESOURCE_MISMATCH '+$Name)
 }
 for($Index=0;$Index -lt 2;$Index++){
  Need ($Trust.binary_sha256[$Index] -eq $BinaryShas[$Index] -and $Trust.source_sha256[$Index] -eq $CppShas[$Index]) 'TRUST_IMAGE_SOURCE_ORDER_MISMATCH'
 }
 Need (@($Trust.binary_sha256).Count -eq 2 -and @($Trust.source_sha256).Count -eq 2) 'TRUST_IMAGE_SOURCE_COUNTS'
 Check-Hash $BuildManifestPath $BuildManifestSha
 Check-Hash $BuildClosurePath $BuildClosureSha
 Check-Hash $BuildPrePath $BuildPreSha
 $Old=Read-Metadata $BuildManifestPath
 $Closed=Read-Metadata $BuildClosurePath
 $BuildPre=Read-Metadata $BuildPrePath
 $Source=Read-Metadata $SourceHandoffPath
 Need (@($Old.bindings).Count -eq 6375 -and @($Source.bindings).Count -eq 25) 'OLD_OR_SOURCE_BINDING_COUNT'
 Need ($Closed.parent_invocations -eq 1 -and $Closed.parent_exit_code -eq 0 -and $Closed.compiler_processes_created -eq 2 -and
       $Closed.produced_binary_invocations -eq 0 -and @($Closed.output_bindings).Count -eq 17 -and @($Closed.binary_bindings).Count -eq 2) 'NO_CLOSED_REAL_BUILD04'
 Need (@($BuildPre.captures).Count -eq 47) 'BUILD04_CAPTURE_COUNT'
 foreach($Row in @($Old.bindings)+@($Source.bindings)){Add-Binding $Row}
 $OldAndSourceUnion=$Map.Count
 foreach($Row in @($Closed.output_bindings)+@($Closed.binary_bindings)){
  Add-Binding ([ordered]@{path=$Row.path;bytes=$Row.bytes;sha256=$Row.sha256;capture=$false})
 }
 foreach($Row in $BuildPre.captures){
  Add-Control $Row.original $Row.sha256 $true
  Add-Control $Row.copy $Row.sha256 $false
 }
 foreach($Control in @(
  @($BuildManifestPath,$BuildManifestSha),@($BuildClosurePath,$BuildClosureSha),@($SourceHandoffPath,$SourceHandoffSha),
  @($ReviewPath,$IndependentReviewSha256),@($TrustPath,$TrustReviewSha256))){Add-Control $Control[0] $Control[1] $true}

 # A second independent path-set construction follows the parent definition.
 # It uses keys only, never Sort-Object path -Unique on OrderedDictionary.
 $Expected=@{}
 foreach($Row in @($Old.bindings)+@($Source.bindings)+@($Closed.output_bindings)+@($Closed.binary_bindings)){
  $Expected[(Path-Key $Row.path)]=$true
 }
 foreach($Row in $BuildPre.captures){$Expected[(Path-Key $Row.original)]=$true;$Expected[(Path-Key $Row.copy)]=$true}
 foreach($Path in @($BuildManifestPath,$BuildClosurePath,$SourceHandoffPath,$ReviewPath,$TrustPath)){$Expected[(Path-Key $Path)]=$true}
 Need ($Map.Count -eq $Expected.Count) 'PARENT_EXACT_PATH_COUNT_MISMATCH'
 foreach($Key in $Map.Keys){Need ($Expected.ContainsKey($Key)) 'EXTRANEOUS_RUNTIME_BINDING'}
 foreach($Key in $Expected.Keys){Need ($Map.ContainsKey($Key)) 'MISSING_RUNTIME_BINDING'}
 $Rows=@($Map.Keys | Sort-Object | ForEach-Object {$Map[$_]})
 foreach($Row in $Rows){Check-Binding $Row}
 Check-Hash $CanonicalPython $PythonSha
 Check-Hash $BuildReceiptPath $BuildReceiptSha
 Check-Hash (Join-Path $BuildActual 'receipt.json') $BuildReceiptSha
 Check-Hash $BuildPlanPath $BuildPlanSha
 $BuildReceipt=Read-Metadata $BuildReceiptPath
 Need ($BuildReceipt.status -eq 'NATIVE_BUILD_EXIT0' -and $null -eq $BuildReceipt.error -and $null -eq $BuildReceipt.post_error -and
       $BuildReceipt.actual_build_plan_sha256 -eq $BuildPlanSha -and $BuildReceipt.produced_binary_invocations -eq 0 -and
       $BuildReceipt.child_exit_codes.Count -eq 2 -and $BuildReceipt.child_exit_codes[0] -eq 0 -and $BuildReceipt.child_exit_codes[1] -eq 0) 'BUILD04_RECEIPT_MISMATCH'
 Require-False $BuildReceipt 'numeric_authorization'
 for($Index=0;$Index -lt 2;$Index++){
  Check-Hash $BinaryPaths[$Index] $BinaryShas[$Index]
  Need ((Get-Item -LiteralPath $BinaryPaths[$Index]).Length -eq $BinaryBytes[$Index]) 'IMAGE_SIZE_CHANGED'
  Check-Hash $CppPaths[$Index] $CppShas[$Index]
  Need ($BuildReceipt.binary_sha256[$Index] -eq $BinaryShas[$Index] -and $BuildReceipt.source_sha256[$Index] -eq $CppShas[$Index]) 'BUILD04_IMAGE_SOURCE_LINK'
 }
 $DirectoryImages=@(Get-ChildItem -LiteralPath (Split-Path -Parent $BinaryPaths[0]) -Force)
 Need ($DirectoryImages.Count -eq 2 -and @($DirectoryImages | Where-Object {$_.PSIsContainer}).Count -eq 0 -and
       @($DirectoryImages | Where-Object {$_.Name -notin @('producer_dit22.exe','checker_dif22.exe')}).Count -eq 0) 'BUILD_FINAL04_PATH_SET'
 $ArchiveCount=Check-Archives

 # Metadata-provenance inputs are separate from the parent's runtime set.
 # Adding them to that set would violate the already reviewed frozen parent.
 $BuilderHandoff=Read-Metadata $BuilderHandoffPath
 Need ($BuilderHandoff.schema -eq 'ROUND22_NATIVE_NUMERIC04_METADATA_HELPER_SOURCE_HANDOFF') 'NO_FROZEN_METADATA_HELPER_HANDOFF'
 foreach($Row in $BuilderHandoff.bindings){Check-Binding $Row}
 $BuilderHandoffSha=Digest $BuilderHandoffPath
 $RuntimePrefix='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\'
 $RuntimeCount=@($Rows | Where-Object {$_.path.StartsWith($RuntimePrefix,[StringComparison]::OrdinalIgnoreCase)}).Count
 Need ($RuntimeCount -eq 972) 'CANONICAL_RUNTIME_FILE_COUNT'
 $PriorConsumerPaths=@((Join-Path $NativeDir 'run_native_once22.py'),(Join-Path $NativeDir 'windows_job22.py'),
  (Join-Path $TaskBase 'round22\role4\circle_native_source01\producer_dit22.cpp'),
  (Join-Path $TaskBase 'round22\role4\circle_native_source01\checker_dif22.cpp'),
  (Join-Path $TaskBase 'round22\role4\circle_native_source01\source_handoff22.json'))
 foreach($Path in $PriorConsumerPaths){Need ($Map.ContainsKey((Path-Key $Path))) ('PRIOR_CONSUMER_OMITTED '+$Path)}
 $CaptureCount=@($Rows | Where-Object {$_.capture}).Count
 $CaptureBytes=0L
 foreach($Row in $Rows){if($Row.capture){$CaptureBytes+=$Row.bytes}}
 # Parent also captures future preparation/manifest/gate; their exact sizes
 # cannot be asserted until they exist. The runtime parent guards32MiB itself.
 Need ($CaptureBytes -lt $Fixed.capture_bytes) 'SOURCE_CAPTURE_BYTES_ALREADY_EXHAUSTED'
 $Manifest=[ordered]@{schema='ROUND22_NATIVE_NUMERIC04_EXACT_RUNTIME_MANIFEST';status='METADATA_ONLY_NO_CANDIDATE_RUN';
  source_handoff_sha256=$SourceHandoffSha;binding_count=$Rows.Count;bindings=$Rows}
 Write-Json $ManifestPath $Manifest
 Write-Exclusive $LocalManifest ([IO.File]::ReadAllBytes($ManifestPath))
 $ManifestSha=Digest $ManifestPath
 Check-Hash $LocalManifest $ManifestSha
 $Preparation=[ordered]@{schema='ROUND22_ROLE6_NATIVE_NUMERIC04_METADATA_PREPARATION';status='NATIVE_NUMERIC04_METADATA_PREPARED';
  actor='ROLE6';utc=[DateTime]::UtcNow.ToString('o');manifest_path=$LocalManifest;manifest_sha256=$ManifestSha;binding_count=$Rows.Count;
  source_handoff_sha256=$SourceHandoffSha;numeric_execution_plan_sha256=$PlanSha;numeric_trust_policy_sha256=$PolicySha;
  build_receipt_path=$BuildReceiptPath;build_receipt_sha256=$BuildReceiptSha;actual_build_plan_sha256=$BuildPlanSha;binary_sha256=$BinaryShas;
  independent_numeric_source_review_path=$ReviewPath;independent_numeric_source_review_sha256=$IndependentReviewSha256;
  numeric_trust_review_path=$TrustPath;numeric_trust_review_sha256=$TrustReviewSha256;
  accept_installed_Windows_and_frozen_native_runtime_trust=$true;
  metadata_source_handoff_path=$BuilderHandoffPath;metadata_source_handoff_sha256=$BuilderHandoffSha;
  metadata_helper_path=$MyInvocation.MyCommand.Path;metadata_helper_sha256=(Digest $MyInvocation.MyCommand.Path);
  metadata_inputs_are_ROOT_controls_not_runtime_manifest_rows=$true;
  expected_future_gate_path=$FutureGate;expected_future_actual_path=$FutureActual;
  future_python_argv=@($CanonicalPython,'-I','-S','-B','-X','utf8',$ParentPath);future_parent_working_directory=$SourceDir;
  protected_registry_sha256=$RegistrySha;protected_archive_count=$ArchiveCount;python_runtime_file_count=$RuntimeCount;
  effective_loads_observed=$false;universal_loader_closure_verified=$false;all_non_OS_imports_bound=$false;
  numeric_authorization=$false;produced_binary_invocations=0;ROOT_gate_created=$false;native_Lean_refinement=$false;D_N=$false;WIN=$false}
 foreach($Name in $Fixed.Keys){$Preparation[$Name]=$Fixed[$Name]}
 Write-Json $PreparationPath $Preparation
 Write-Exclusive $LocalPreparation ([IO.File]::ReadAllBytes($PreparationPath))
 $PreparationSha=Digest $PreparationPath
 Check-Hash $LocalPreparation $PreparationSha

 # Genuine metadata POST: every original runtime binding and source control,
 # plus all old BUILD04 original/copy pairs and both new exclusive copies.
 foreach($Row in $Rows){Check-Binding $Row}
 foreach($Row in $BuildPre.captures){Check-Hash $Row.original $Row.sha256;Check-Hash $Row.copy $Row.sha256}
 foreach($Row in $BuilderHandoff.bindings){Check-Binding $Row}
 Check-Hash $BuilderHandoffPath $BuilderHandoffSha
 Check-Hash $SourceHandoffPath $SourceHandoffSha
 Check-Hash $ReviewPath $IndependentReviewSha256
 Check-Hash $TrustPath $TrustReviewSha256
 Check-Hash $ManifestPath $ManifestSha
 Check-Hash $LocalManifest $ManifestSha
 Check-Hash $PreparationPath $PreparationSha
 Check-Hash $LocalPreparation $PreparationSha
 Need ((Check-Archives) -eq $ArchiveCount) 'ARCHIVES_CHANGED_DURING_METADATA'
 Need (-not(Test-Path -LiteralPath $FutureGate) -and -not(Test-Path -LiteralPath $FutureActual)) 'NUMERIC_GATE_OR_ACTUAL_CREATED_DURING_METADATA'
 $Conservation=[ordered]@{schema='ROUND22_NATIVE_NUMERIC04_METADATA_CONSERVATION';status='METADATA_PREPARED_NO_NUMERIC_AUTHORIZATION';
  utc=[DateTime]::UtcNow.ToString('o');old_BUILD04_bindings=6375;source01_bindings=25;old_and_source_union=$OldAndSourceUnion;
  closed_BUILD04_output_bindings=17;closed_BUILD04_images=2;closed_BUILD04_original_copy_pairs=47;
  duplicate_occurrences=$DuplicateOccurrences;exact_parent_set_count=$Rows.Count;exact_parent_path_set_equal=$true;
  all_runtime_binding_original_bytes_rehashed_PRE_POST=$true;all_BUILD04_original_copy_pairs_rehashed_PRE_POST=$true;
  protected_archive_count=$ArchiveCount;all_archives_rehashed_PRE_POST=$true;python_runtime_file_count=$RuntimeCount;
  prior_consumer_paths_bound=$PriorConsumerPaths;prior_consumer_sources_intact=$true;
  source_capture_row_count=$CaptureCount;source_capture_bytes_before_new_controls=$CaptureBytes;
  isolated_manifest_path=$ManifestPath;parent_local_manifest_path=$LocalManifest;manifest_sha256=$ManifestSha;
  isolated_preparation_path=$PreparationPath;parent_local_preparation_path=$LocalPreparation;preparation_sha256=$PreparationSha;
  parent_local_copies_byteidentical=$true;metadata_source_handoff_sha256=$BuilderHandoffSha;
  metadata_source_inputs_checked_separately_not_added_to_parent_runtime_set=$true;
  current_source01_frozen_files_BYTE_identical=$true;future_gate_and_actual_absent=$true;
  compiler_invocations=0;candidate_imports_or_parses=0;Windows_API_probes=0;produced_binary_invocations=0;
  numeric_authorization=$false;ROOT_gate_created=$false;rss_os_enforced=$false;effective_loads_observed=$false;universal_loader_closure_verified=$false;
  native_Lean_refinement=$false;D_N=$false;WIN=$false}
 Write-Json $ConservationPath $Conservation
 $MetadataReads=[ordered]@{schema='ROUND22_NATIVE_NUMERIC04_METADATA_ACTUAL_READ_RECEIPTS';
  status='METADATA_READS_NO_CANDIDATE_EVALUATION';utc=[DateTime]::UtcNow.ToString('o');
  inventories=[ordered]@{
   BUILD04_manifest=[ordered]@{path=$BuildManifestPath;sha256=$BuildManifestSha;scope='PARSED_METADATA_ALL_BINDINGS';count=6375};
   SOURCE01_handoff=[ordered]@{path=$SourceHandoffPath;sha256=$SourceHandoffSha;scope='PARSED_METADATA_ALL_BINDINGS';count=25};
   BUILD04_closure=[ordered]@{path=$BuildClosurePath;sha256=$BuildClosureSha;scope='PARSED_METADATA_ALL_OUTPUT_AND_IMAGE_BINDINGS';outputs=17;images=2};
   BUILD04_PRE=[ordered]@{path=$BuildPrePath;sha256=$BuildPreSha;scope='PARSED_METADATA_ALL_ORIGINAL_COPY_PAIRS';pairs=47};
   protected_registry=[ordered]@{path=$RegistryPath;sha256=$RegistrySha;scope='PARSED_METADATA_ALL_ARCHIVE_KEYS_WITH_PRE_POST_BYTES_SHA';count=$ArchiveCount}};
  controls=@(
   [ordered]@{path=$ReviewPath;sha256=$IndependentReviewSha256;scope='PARSED_METADATA_REQUIRED_FIELDS'},
   [ordered]@{path=$TrustPath;sha256=$TrustReviewSha256;scope='PARSED_METADATA_REQUIRED_FIELDS'},
   [ordered]@{path=$BuildReceiptPath;sha256=$BuildReceiptSha;scope='PARSED_METADATA_BUILD_EXIT_LINK'},
   [ordered]@{path=$BuilderHandoffPath;sha256=$BuilderHandoffSha;scope='PARSED_METADATA_WITH_ALL_METADATA_SOURCE_BINDINGS_BYTES_SHA'});
  exact_parent_runtime_set_count=$Rows.Count;all_runtime_rows_PRE_POST_bytes_SHA=$true;runtime_files=$RuntimeCount;
  candidate_sources_parsed=$false;candidate_sources_imported=$false;native_image_bytes_SHA_only=$true;
  raw_text_FULL_inventory_claimed=$false;effective_loads_observed=$false;universal_loader_closure_verified=$false;
  produced_binary_invocations=0;compiler_invocations=0;numeric_authorization=$false;D_N=$false;WIN=$false}
 Write-Json $MetadataReadsPath $MetadataReads
 $Completed=$true
}catch{
 $ErrorText=$_.Exception.GetType().FullName+': '+$_.Exception.Message
}finally{
 $Finished=[DateTime]::UtcNow.ToString('o')
 $Receipt=[ordered]@{schema='ROUND22_NATIVE_NUMERIC04_METADATA_HELPER_ACTUAL_RECEIPT';
  status=if($Completed){'NATIVE_NUMERIC04_METADATA_PREPARED_NOT_AUTHORIZED'}else{'METADATA_FAILURE_NO_CANDIDATE_NO_RETRY'};
  utc_START=$Started;utc_FIN=$Finished;helper_invocations=1;retry_count=0;error=$ErrorText;
  independent_review_sha256=$IndependentReviewSha256;trust_review_sha256=$TrustReviewSha256;
  metadata_read_receipts_path=$MetadataReadsPath;
  numerical_parent_invocations=0;native_invocations=0;compiler_invocations=0;candidate_imports_or_parses=0;
  metadata_preparation_exists=(Test-Path -LiteralPath $PreparationPath);numeric_authorization=$false;ROOT_gate_created=$false;
  partial_metadata_files_preserved_not_reused=(-not$Completed);D_N=$false;WIN=$false}
 Write-Json $ExecutionReceiptPath $Receipt
 Write-Json (Join-Path $MetadataActual 'FIN.json') $Receipt
}
if(-not$Completed){throw $ErrorText}
[ordered]@{status='NATIVE_NUMERIC04_METADATA_PREPARED';manifest_path=$ManifestPath;parent_local_manifest_path=$LocalManifest;
 manifest_sha256=$ManifestSha;preparation_path=$PreparationPath;parent_local_preparation_path=$LocalPreparation;preparation_sha256=$PreparationSha;
 exact_parent_set_count=$Rows.Count;python_runtime_files=$RuntimeCount;archives=$ArchiveCount;reviews_bound=$true;
 numeric_authorization=$false;compiler_invocations=0;candidate_invocations=0;ROOT_gate_created=$false} | ConvertTo-Json -Depth 5
