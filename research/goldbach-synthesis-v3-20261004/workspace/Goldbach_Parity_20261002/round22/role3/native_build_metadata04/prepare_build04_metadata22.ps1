param(
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{64}$')][string]$IndependentReviewSha256,
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{64}$')][string]$TrustReviewSha256
)
$ErrorActionPreference='Stop'
$TaskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$TaskHere=Split-Path -Parent $MyInvocation.MyCommand.Path
$NativeDir=Join-Path $TaskBase 'round22\role4\circle_native_revision02'
$BuildDir=Join-Path $TaskBase 'round22\role4\circle_native_build_source04'
$ManifestPath=Join-Path $TaskHere 'build_manifest22.json'
$PreparationPath=Join-Path $TaskHere 'build_preparation22.json'
$ObservationPath=Join-Path $TaskHere 'metadata_conservation22.json'
foreach($OutPath in @($ManifestPath,$PreparationPath,$ObservationPath)){
 if(Test-Path -LiteralPath $OutPath){throw ('Immutable metadata already exists: '+$OutPath)}
}
$FixedControls=@(
 [ordered]@{path=Join-Path $NativeDir 'closure_snapshot22.json';sha256='12bd8ab8c067e4881b837689ce705e7f029826b20482b85fbc6a6d18e3717e06';count=6332},
 [ordered]@{path=Join-Path $NativeDir 'source_handoff22.json';sha256='889d4e221911bdfe75104361d62f36accf3770a17f48f29d84a9ba8d1952da88';count=12},
 [ordered]@{path=Join-Path $BuildDir 'source_handoff22.json';sha256='277af8bac79d344907222f1b3c481d97e551afb2d8b1cf5a2aca299dac7508b6';count=29}
)
$ReviewPath=Join-Path $TaskBase 'round22\judge5\circle_native_build_controls_source_review04.md'
${ReviewHash}=$IndependentReviewSha256
$TrustReviewPath=Join-Path $TaskBase 'round22\judge5\circle_native_build_trust_review04.json'
${TrustReviewHash}=$TrustReviewSha256
$PolicyPath=Join-Path $BuildDir 'compiler_trust_policy22.json'
$PolicyHash='72fd49d993e3291a174d4ba5a139a649ab916e9e757274c0e89f0a6092b4f6a6'
$PlanPath=Join-Path $BuildDir 'build_execution_plan22.json'
$PlanHash='538cc14faf3466bb8a0505e8f6aae3007fc84b2b6246afb2da55d37be5718156'
$DeclaredPath=Join-Path $TaskBase 'round22\role3\native_build_metadata01\pe_static_import_observation22.json'
$DeclaredHash='36032c45c476e72c97393f60d02fbf5ff2e2679e82d2c3dd5eaea558cfdcadbc'
$CanonicalPython='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$PythonHash='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
$RegistryPath=Join-Path $TaskBase 'round22\previous_artifacts_sha256.json'
$RegistryHash='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'

function Check-Hash([string]$TaskPath,[string]$Expected){
 if((Get-FileHash -LiteralPath $TaskPath -Algorithm SHA256).Hash.ToLowerInvariant() -ne $Expected){throw ('Hash changed: '+$TaskPath)}
}
function Binding-Now([string]$TaskPath,[bool]$Capture){
 $Item=Get-Item -LiteralPath $TaskPath
 return [ordered]@{path=[IO.Path]::GetFullPath($TaskPath);bytes=$Item.Length;sha256=(Get-FileHash -LiteralPath $TaskPath -Algorithm SHA256).Hash.ToLowerInvariant();capture=$Capture}
}
$Map=@{}
$Duplicates=0
function Add-Binding($Binding){
 $Key=[IO.Path]::GetFullPath($Binding.path).ToLowerInvariant()
 if($Map.ContainsKey($Key)){
  if($Map[$Key].bytes -ne $Binding.bytes -or $Map[$Key].sha256 -ne $Binding.sha256){throw ('Conflicting binding: '+$Binding.path)}
  $Map[$Key].capture=[bool]($Map[$Key].capture -or $Binding.capture)
  $script:Duplicates++
 }else{
  $Map[$Key]=[ordered]@{path=[IO.Path]::GetFullPath($Binding.path);bytes=[long]$Binding.bytes;sha256=$Binding.sha256;capture=[bool]$Binding.capture}
 }
}
foreach($Control in $FixedControls){
 Check-Hash $Control.path $Control.sha256
 $Document=Get-Content -LiteralPath $Control.path -Raw | ConvertFrom-Json
 if(@($Document.bindings).Count -ne $Control.count){throw 'Frozen control count mismatch'}
 foreach($Binding in $Document.bindings){Add-Binding $Binding}
}
$FrozenUnionCount=$Map.Count
Check-Hash $ReviewPath $ReviewHash
Check-Hash $TrustReviewPath $TrustReviewHash
foreach($Control in $FixedControls){Add-Binding (Binding-Now $Control.path $true)}
Add-Binding (Binding-Now $ReviewPath $true)
Add-Binding (Binding-Now $TrustReviewPath $true)
Check-Hash $PolicyPath $PolicyHash
Check-Hash $PlanPath $PlanHash
Check-Hash $DeclaredPath $DeclaredHash
Check-Hash $CanonicalPython $PythonHash

$Policy=Get-Content -LiteralPath $PolicyPath -Raw | ConvertFrom-Json
$TrustReview=Get-Content -LiteralPath $TrustReviewPath -Raw | ConvertFrom-Json
if($TrustReview.status -ne 'BUILD_ONLY_DECLARED_IMPORTS_REVIEWED_WITH_EXPLICIT_WINDOWS_GCC_TRUST' -or
 $TrustReview.scope -ne 'NATIVE_BUILD_ONLY_TWO_FIXED_TARGETS' -or
 $TrustReview.compiler_trust_policy_sha256 -ne $PolicyHash -or
 $TrustReview.declared_import_metadata_sha256 -ne $DeclaredHash -or
 $TrustReview.installed_Windows_and_GCC_trusted -ne $true -or
 $TrustReview.effective_loads_observed -ne $false -or
 $TrustReview.universal_loader_closure_verified -ne $false -or
 $TrustReview.all_non_OS_imports_bound -eq $true -or
 $TrustReview.numeric_authorization -ne $false -or
 $TrustReview.produced_binary_invocations -ne 0){throw 'Scoped trust review mismatch'}
$Plan=Get-Content -LiteralPath $PlanPath -Raw | ConvertFrom-Json
if($Plan.schema -ne 'ROUND22_BUILD_ONLY04_EXECUTION_PLAN_SOURCE_ONLY' -or
 $Plan.rss_os_enforced -ne $false -or
 $Plan.rss_control -ne 'SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM' -or
 $Plan.working_set_limit_flag_requested -ne $false -or
 $Plan.job_limit_flags_requested -ne 8968 -or
 $Plan.commit_job_bytes -ne 2147483648){throw 'BUILD04 commit/RSS SOURCE scope mismatch'}
$Declared=Get-Content -LiteralPath $DeclaredPath -Raw | ConvertFrom-Json
if($Declared.nodes.Count -ne 66 -or $Declared.edges.Count -ne 825 -or @($Declared.parser_or_declared_import_gaps).Count -ne 0){throw 'Declared static counts mismatch'}
$NodeMap=@{}
$Descriptors=[Collections.Generic.List[string]]::new()
foreach($Node in $Declared.nodes){
 $Key=[IO.Path]::GetFullPath($Node.path).ToLowerInvariant()
 if($NodeMap.ContainsKey($Key) -or -not$Map.ContainsKey($Key)){throw 'Unbound or duplicate PE metadata node'}
 if($Node.sha256 -ne $Map[$Key].sha256 -or $Node.bytes -ne $Map[$Key].bytes){throw 'PE node differs from frozen binding'}
 $NodeMap[$Key]=$Node
 foreach($Kind in @('normal_imports','delay_imports')){
  foreach($Name in $Node.$Kind){$Descriptors.Add($Key+'|'+$Kind+'|'+$Name.ToLowerInvariant())}
 }
}
$EdgeKeys=[Collections.Generic.List[string]]::new()
$LocalCount=0
$OsCount=0
foreach($Edge in $Declared.edges){
 $Key=[IO.Path]::GetFullPath($Edge.from).ToLowerInvariant()
 $EdgeKeys.Add($Key+'|'+$Edge.kind+'|'+$Edge.dll_name.ToLowerInvariant())
 if($Edge.classification -eq 'DECLARED_LOCAL_IMPORT_BOUND_CANDIDATE'){
  $Candidate=[IO.Path]::GetFullPath($Edge.candidate).ToLowerInvariant()
  if(-not$NodeMap.ContainsKey($Candidate) -or -not$Map.ContainsKey($Candidate) -or
   [IO.Path]::GetFileName($Candidate) -ne $Edge.dll_name.ToLowerInvariant() -or
   $Edge.actual_windows_loader_resolution_verified -ne $false){throw 'Unbound local declared candidate'}
  $LocalCount++
 }elseif($Edge.classification -eq 'WINDOWS_OR_API_SET_TRUST_BOUNDARY'){
  if($null -ne $Edge.candidate -or $Edge.os_transitive_closure_verified -ne $false){throw 'OS trust edge promoted to closure'}
  $OsCount++
 }else{throw 'Unexpected static import classification'}
}
if($LocalCount -ne 119 -or $OsCount -ne 706 -or
 @(Compare-Object @($Descriptors.ToArray() | Sort-Object) @($EdgeKeys.ToArray() | Sort-Object)).Count -ne 0){throw 'Descriptor/edge multiset mismatch'}

$Rows=@($Map.Keys | Sort-Object | ForEach-Object {$Map[$_]})
foreach($Binding in $Rows){
 $Item=Get-Item -LiteralPath $Binding.path
 if(($Item.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0 -or $Item.Length -ne $Binding.bytes){throw ('Changed/reparse binding: '+$Binding.path)}
 Check-Hash $Binding.path $Binding.sha256
}
Check-Hash $RegistryPath $RegistryHash
$Registry=Get-Content -LiteralPath $RegistryPath -Raw | ConvertFrom-Json
$ArchiveCount=0
foreach($Property in $Registry.sha256.PSObject.Properties){
 Check-Hash (Join-Path $TaskBase $Property.Name) $Property.Value
 $ArchiveCount++
}
if($ArchiveCount -ne 3089){throw 'Archive count mismatch'}
$OldCounts=@()
foreach($OldDir in @('circle_native_build_source01','circle_native_build_source02','circle_native_build_source03')){
 $OldHandoff=Get-Content -LiteralPath (Join-Path $TaskBase ('round22\role4\'+$OldDir+'\source_handoff22.json')) -Raw | ConvertFrom-Json
 foreach($Binding in $OldHandoff.bindings){
  if((Get-Item -LiteralPath $Binding.path).Length -ne $Binding.bytes){throw 'Old build bytes changed'}
  Check-Hash $Binding.path $Binding.sha256
 }
 $OldCounts+=@($OldHandoff.bindings).Count
}
# Preserve the prior true BUILD03 attempt separately, without adding paths
# outside the exact new parent manifest set or invoking any old controller.
$Old03Dir=Join-Path $TaskBase 'round22\role4\circle_native_build_source03'
$Old03Actual=Join-Path $Old03Dir 'actual_build03_attempt01'
$Old03ClosurePath=Join-Path $TaskBase 'round22\role3\native_build_metadata03\build_execution_closure22.json'
Check-Hash $Old03ClosurePath '94cdc97045004ddfca7556bac5a14339c247b7ead776373ec49d093edc25361e'
$Old03Closure=Get-Content -LiteralPath $Old03ClosurePath -Raw | ConvertFrom-Json
foreach($OldOutput in $Old03Closure.output_bindings){
 if((Get-Item -LiteralPath $OldOutput.path).Length -ne $OldOutput.bytes){throw 'Old BUILD03 output bytes changed'}
 Check-Hash $OldOutput.path $OldOutput.sha256
}
$Old03Pre=Get-Content -LiteralPath (Join-Path $Old03Actual 'PRE.json') -Raw | ConvertFrom-Json
foreach($OldCopy in $Old03Pre.captures){
 Check-Hash $OldCopy.original $OldCopy.sha256
 Check-Hash $OldCopy.copy $OldCopy.sha256
}
$Old03ManifestPath=Join-Path $TaskBase 'round22\role3\native_build_metadata03\build_manifest22.json'
Check-Hash $Old03ManifestPath 'fdbdbb9f0fee7becc32f320b259ef0b2072dc18f257d8790c6ae9d4ba9607d50'
$Old03Manifest=Get-Content -LiteralPath $Old03ManifestPath -Raw | ConvertFrom-Json
if($Old03Manifest.bindings.Count -ne 6358 -or $Old03Pre.captures.Count -ne 30){throw 'Old BUILD03 preservation count mismatch'}
foreach($OldBinding in $Old03Manifest.bindings){
 if((Get-Item -LiteralPath $OldBinding.path).Length -ne $OldBinding.bytes){throw 'Old BUILD03 input bytes changed'}
 Check-Hash $OldBinding.path $OldBinding.sha256
}
$DraftPath=Join-Path $TaskBase 'round22\judge5\circle_native_build_trust_review03_draft_metadata_error.json'
$DraftHash='abdfbffecbe18ed94df9829819e596ee285b52a94aa108514452a9121721c789'
Check-Hash $DraftPath $DraftHash
$FuturePaths=@((Join-Path $BuildDir 'actual_build04_attempt01'),(Join-Path $NativeDir 'build-final04'),(Join-Path $NativeDir 'build_receipt04.json'),(Join-Path $BuildDir 'build_preparation22.json'),(Join-Path $TaskBase '.arbor\sessions\parity\.coordinator\messages\round22_native_build04_authorization.json'))
foreach($FuturePath in $FuturePaths){if(Test-Path -LiteralPath $FuturePath){throw ('Future control/attempt already exists: '+$FuturePath)}}

$RuntimePrefix='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\'
$RuntimeCount=@($Rows | Where-Object {$_.path.StartsWith($RuntimePrefix,[StringComparison]::OrdinalIgnoreCase)}).Count
$Manifest=[ordered]@{schema='ROUND22_BUILD_ONLY04_EXACT_INPUT_MANIFEST';status='METADATA_ONLY_NO_COMPILER_OR_NUMERIC_RUN';binding_count=$Rows.Count;bindings=$Rows}
[IO.File]::WriteAllText($ManifestPath,($Manifest | ConvertTo-Json -Depth 8),[Text.UTF8Encoding]::new($false))
$ManifestHash=(Get-FileHash -LiteralPath $ManifestPath -Algorithm SHA256).Hash.ToLowerInvariant()
$Preparation=[ordered]@{
 schema='ROUND22_ROLE6_BUILD_ONLY04_METADATA_PREPARATION';status='BUILD_ONLY_METADATA_PREPARED';actor='ROLE6';utc=[DateTime]::UtcNow.ToString('o');
 manifest_path=$ManifestPath;manifest_sha256=$ManifestHash;binding_count=$Rows.Count;
 closure_snapshot_sha256=$FixedControls[0].sha256;native_source_handoff_sha256=$FixedControls[1].sha256;build_source_handoff_sha256=$FixedControls[2].sha256;
 actual_build_plan_sha256=$PlanHash;compiler_trust_policy_sha256=$PolicyHash;accept_installed_Windows_and_GCC_trust=$true;
 independent_build_source_review_path=$ReviewPath;independent_build_source_review_sha256=$ReviewHash;
 compiler_build_trust_review_path=$TrustReviewPath;compiler_build_trust_review_sha256=$TrustReviewHash;
 scope='NATIVE_BUILD_ONLY_TWO_FIXED_TARGETS';max_driver_invocations=2;max_retries=0;wall_seconds=300;max_active_job_processes=16;max_total_job_processes=32;
 commit_job_bytes=2147483648;rss_per_process_bytes=2147483648;sampled_job_rss_bytes=4294967296;
 rss_os_enforced=$false;rss_control='SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM';working_set_limit_flag_requested=$false;job_limit_flags_requested=8968;log_bytes=1048576;capture_bytes=33554432;metadata_bytes=16777216;
 binary_bytes_each=67108864;temporary_bytes=67108864;output_bytes=268435456;produced_binary_invocations=0;
 expected_future_gate_path=$FuturePaths[4];expected_parent_local_preparation_path=$FuturePaths[3];
 future_python_argv=@($CanonicalPython,'-I','-S','-B','-X','utf8',(Join-Path $BuildDir 'run_build_only_once22.py'));canonical_python_sha256=$PythonHash;
 protected_registry_sha256=$RegistryHash;protected_archive_count=$ArchiveCount;python_runtime_file_count=$RuntimeCount;
 effective_loads_observed=$false;universal_loader_closure_verified=$false;all_non_OS_imports_bound=$false;numeric_authorization=$false;
 compiler_invocations=0;native_program_invocations=0;ROOT_gate_created=$false;D_N=$false;WIN=$false
}
[IO.File]::WriteAllText($PreparationPath,($Preparation | ConvertTo-Json -Depth 8),[Text.UTF8Encoding]::new($false))
$PreparationHash=(Get-FileHash -LiteralPath $PreparationPath -Algorithm SHA256).Hash.ToLowerInvariant()
$Observation=[ordered]@{
 schema='ROUND22_ROLE6_BUILD_ONLY04_METADATA_CONSERVATION';status='EXACT_METADATA_ONLY_NO_BUILD';utc=[DateTime]::UtcNow.ToString('o');
 frozen_control_counts=@(6332,12,29);frozen_union_count=$FrozenUnionCount;duplicate_occurrences_in_union_and_controls=$Duplicates;exact_parent_set_count=$Rows.Count;
 fixed_controls=$FixedControls;manifest_sha256=$ManifestHash;preparation_sha256=$PreparationHash;
 all_exact_parent_binding_bytes_rehashed_intact=$true;python_runtime_files=$RuntimeCount;protected_archive_count=$ArchiveCount;all_archives_rehashed_intact=$true;
 old_build01_build02_build03_binding_counts=$OldCounts;old_build01_build02_build03_bindings_intact=$true;old03_actual_originals_and_copies=30;old03_actual_binding_count=6358;old03_actual_preserved=$true;
 declared_images=66;declared_edges=825;declared_local_candidate_edges=$LocalCount;Windows_API_set_trust_edges=$OsCount;descriptor_edge_multiset_equal=$true;
 preserved_independent_draft_metadata_error=[ordered]@{path=$DraftPath;bytes=(Get-Item -LiteralPath $DraftPath).Length;sha256=$DraftHash;included_in_exact_parent_manifest=$false};
 future_controls_and_attempts_absent=$FuturePaths;compiler_invocations=0;candidate_imports_or_parses=0;PE_parser_reexecutions=0;
 installed_Windows_GCC_trust_assumed_not_observed=$true;effective_loads_observed=$false;universal_loader_closure_verified=$false;all_non_OS_imports_bound=$false;
 numeric_authorization=$false;ROOT_gate_created=$false;D_N=$false;WIN=$false
}
[IO.File]::WriteAllText($ObservationPath,($Observation | ConvertTo-Json -Depth 8),[Text.UTF8Encoding]::new($false))
[ordered]@{status='BUILD_ONLY_METADATA_PREPARED';manifest_path=$ManifestPath;manifest_sha256=$ManifestHash;preparation_path=$PreparationPath;preparation_sha256=$PreparationHash;observation_path=$ObservationPath;observation_sha256=(Get-FileHash -LiteralPath $ObservationPath -Algorithm SHA256).Hash.ToLowerInvariant();frozen_union_count=$FrozenUnionCount;exact_parent_set_count=$Rows.Count;python_runtime_files=$RuntimeCount;archives=$ArchiveCount;compiler_invocations=0;candidate_invocations=0;ROOT_gate_created=$false} | ConvertTo-Json -Depth 5
