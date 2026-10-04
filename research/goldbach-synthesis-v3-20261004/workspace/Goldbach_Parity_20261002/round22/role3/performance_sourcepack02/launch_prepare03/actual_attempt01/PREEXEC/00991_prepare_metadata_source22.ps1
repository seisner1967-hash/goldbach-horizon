# DRAFT SOURCE ONLY. No invocation before actual independent review + ROOT.
# Metadata hashing only; no Python, Lean, gate or mathematical child.
param(
  [Parameter(Mandatory=$true)][string]$IndependentReviewReceipt,
  [Parameter(Mandatory=$true)][string]$IndependentReviewReceiptSha256
)
$ErrorActionPreference='Stop'
$launcherDirectory=$PSScriptRoot
$packetDirectory=Split-Path $launcherDirectory -Parent
$roundDirectory=Split-Path (Split-Path $packetDirectory -Parent) -Parent
$researchBase=Split-Path $roundDirectory -Parent
$runtimePath='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$runtimeRoot=Split-Path $runtimePath -Parent
$sourceManifestPath=Join-Path $packetDirectory 'source_manifest22.json'
$sourceManifestSha='914c210931fb8029f59727a58b473402f8ec28c8e3e86328144e350d0fec362f'
$manifestPath=Join-Path $launcherDirectory 'prepared_manifest22.json'
$preparationPath=Join-Path $launcherDirectory 'preparation22.json'
$actualDirectory=Join-Path $launcherDirectory 'actual_attempt01'
$gatePath=Join-Path $researchBase '.arbor\sessions\parity\.coordinator\messages\round22_global_thermal_h1_authorization02.json'
$closedDirectory=Join-Path $researchBase 'round22\role4\h1_global_numeric\launch_prepare02\actual_attempt01'
$scope='ROUND22_GLOBAL_THERMAL_H1_NUMERIC_ONLY'
$bankId='THERMAL_GLOBAL_H1_22_SOURCEPACK02'
$evaluationLevel='PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER'
$analyticLevel='PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION'
$expectedAliases=@('dyadic_r01','analytic_r01','kernel_r01','unit_transport_source22','arithmetic_catalogue_source22','transport_catalogue_source22','envelopes_source22','producer_source22','structural_checker_source22')
$expectedTools=@('prepare_metadata_source22.ps1','run_global_once_source22.py','thermal_child_source22.py','launch_contract_source22.md','resource_addendum_source22.md')
$limits=[ordered]@{max_children=1;retry_count=0;max_wall_seconds=10800;max_artifact_bytes=2147483648;expected_vertical_nodes=204800;expected_arch_nodes=12288;expected_arithmetic_integers=999999;catalogue_parameter_change_allowed=$false}
$bindingByPath=[ordered]@{}
$expectedAllPaths=[Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)

function Binding([string]$Path,[string]$Kind,[string]$Alias='') {
  $resolved=(Resolve-Path -LiteralPath $Path).Path
  [ordered]@{path=$resolved;sha256=(Get-FileHash -LiteralPath $resolved -Algorithm SHA256).Hash.ToLowerInvariant();bytes=(Get-Item -LiteralPath $resolved).Length;kind=$Kind;module_alias=$Alias;source_packet=$false}
}
function CheckBinding($Entry) {
  $actual=Binding $Entry.path 'VERIFY_ONLY'
  if($actual.sha256 -ne $Entry.sha256 -or $actual.bytes -ne $Entry.bytes) {throw "Changed binding: $($Entry.path)"}
}
function AddBinding($Entry) {
  $key=([string]$Entry['path']).ToLowerInvariant()
  if(-not $key) {throw 'Empty path'}
  [void]$expectedAllPaths.Add($key)
  if($bindingByPath.Contains($key)) {
    $prior=$bindingByPath[$key]
    if($prior.sha256 -ne $Entry.sha256 -or $prior.bytes -ne $Entry.bytes -or $prior.module_alias -ne $Entry.module_alias) {throw "Conflicting shared binding: $key"}
    if($Entry.source_packet) {$prior.source_packet=$true}
  } else {$bindingByPath[$key]=$Entry}
}
function CreateJson([string]$Path,$Value) {
  $data=[Text.UTF8Encoding]::new($false).GetBytes(($Value|ConvertTo-Json -Depth 40)+"`n")
  $stream=[IO.File]::Open($Path,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write)
  try {$stream.Write($data,0,$data.Length)} finally {$stream.Dispose()}
}
function CheckClosedAttempt {
  $known=[ordered]@{'receipt.json'='2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93';'FIN.json'='2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93';'PREEXEC.json'='b3734e005f391ddeef49c2342a8775218640c2c0e42e9146077008bb47dda4e3';'POSTEXEC.json'='3465bc934e6cab3dd204c3d0f3a939704a392b0beac32f123b081f3c6199eacf';'START.json'='7ccb60ee859d294902753afbb0cc939d5f5911d0c1ed7f81a3cef2c488d15683';'child_START.json'='119fa6abf5b4783c5fa0f8dec7322eb6aafdc125e2beeebf5eb181902413d730';'child_context.json'='902ab13f6ca89da54ca6a5fe41a28896e32d32ea8894c9cfe687ee9d7521cf9b'}
  $known['attempt_reservation.json']='aa506752807f540c48deead34c52a03e938d45315f8d7f39c1f1d692600325a7'
  foreach($name in $known.Keys) {
    $entry=Binding (Join-Path $closedDirectory $name) 'CLOSED_ATTEMPT_METADATA_READONLY'
    if($entry.sha256 -ne $known[$name]) {throw "Closed metadata changed: $name"}
    AddBinding $entry
  }
  $receipt=Get-Content -LiteralPath (Join-Path $closedDirectory 'receipt.json') -Raw|ConvertFrom-Json
  $pre=Get-Content -LiteralPath (Join-Path $closedDirectory 'PREEXEC.json') -Raw|ConvertFrom-Json
  if($receipt.resource_failure -ne 'MAX_WALL_SECONDS' -or $receipt.mathematical_children_started -ne 1 -or $receipt.retries -ne 0 -or $pre.bindings.Count -ne 1003 -or $pre.captures.Count -ne 1005) {throw 'Wrong closed attempt provenance'}
  foreach($entry in $pre.bindings) {
    $value=Binding $entry.path 'VERIFY_CLOSED_ONLY'
    if($value.sha256 -ne $entry.expected_sha256 -or $value.bytes -ne $entry.bytes) {throw 'Closed original changed'}
  }
  foreach($entry in $pre.captures) {
    $value=Binding $entry.copy 'VERIFY_CLOSED_ONLY'
    if($value.sha256 -ne $entry.sha256 -or $value.bytes -ne $entry.bytes) {throw 'Closed capture changed'}
    $original=Binding $entry.original 'VERIFY_CLOSED_ONLY'
    if($original.sha256 -ne $entry.sha256 -or $original.bytes -ne $entry.bytes) {throw 'Closed capture original/preparation/gate changed'}
  }
  foreach($entry in $receipt.outputs) {CheckBinding $entry}
  foreach($name in @('resource_closure22.md','resource_closure_receipt22.json')) {
    AddBinding (Binding (Join-Path $researchBase ('round22\role3\global_h1_execution02\'+$name)) 'CLOSED_ATTEMPT_DOCUMENTARY_CLOSURE')
  }
}

foreach($path in @($manifestPath,$preparationPath,$actualDirectory,$gatePath)) {if(Test-Path -LiteralPath $path) {throw "Reserved output/gate exists: $path"}}
$sourceBinding=Binding $sourceManifestPath 'SOURCE_MANIFEST'
if($sourceBinding.sha256 -ne $sourceManifestSha) {throw 'Exact selected candidate manifest changed'}
AddBinding $sourceBinding
$source=Get-Content -LiteralPath $sourceManifestPath -Raw|ConvertFrom-Json
if($source.status -ne 'SOURCE_REVIEW_READY_NOT_PREPARED' -or $source.core_bindings_count -ne 14 -or $source.support_bindings_count -ne 7 -or $source.total_bound_files -ne 21 -or $source.runtime_modules -ne 9) {throw 'Source scope/count changed'}
$sourceEntries=@($source.core_bindings)+@($source.support_bindings)
if($sourceEntries.Count -ne 21) {throw '21 explicit source paths required'}
$sourcePaths=@($sourceEntries|ForEach-Object {$_.path.ToLowerInvariant()}|Sort-Object)
if(@($sourcePaths|Sort-Object -Unique).Count -ne 21) {throw 'Duplicate candidate source paths'}
foreach($entry in $sourceEntries) {
  CheckBinding $entry
  $alias=[string]$entry.module_alias
  if($alias -and ([IO.Path]::GetFullPath($entry.path) -ne [IO.Path]::GetFullPath((Join-Path $packetDirectory ($alias+'.py'))))) {throw 'Runtime alias outside nine local copies'}
  $binding=Binding $entry.path 'SOURCE_PACKET_INPUT' $alias
  $binding.source_packet=$true
  AddBinding $binding
}
if($source.parameters.N -ne 100000000 -or $source.parameters.Y -ne 10000 -or $source.parameters.T -ne 100 -or $source.parameters.X -ne 1000000 -or $source.parameters.Q -ne 1000000 -or $source.parameters.R -ne 1000000 -or $source.parameters.tau -ne '1/1000000') {throw 'Mathematical parameters changed'}
if($source.catalogue.vertical_nodes -ne 204800 -or $source.catalogue.arch_nodes -ne 12288 -or $source.catalogue.arithmetic_integers -ne 999999 -or $source.catalogue.track_advances -ne 26181632 -or $source.catalogue.EM_seeds -ne 32512 -or $source.catalogue.Y_seeds -ne 256) {throw 'Complete fixed catalogue changed'}
foreach($name in $expectedTools) {AddBinding (Binding (Join-Path $launcherDirectory $name) 'NEW_LAUNCH_TOOLS_SOURCE')}
AddBinding (Binding (Join-Path $launcherDirectory 'tool_read_receipts22.json') 'LAUNCH_TOOL_READ_RECEIPTS')

# A real ROLE5 receipt must audit this exact source/addendum/tool revision.
$reviewBinding=Binding $IndependentReviewReceipt 'INDEPENDENT_SOURCE_REVIEW_RECEIPT'
if($reviewBinding.sha256 -ne $IndependentReviewReceiptSha256.ToLowerInvariant()) {throw 'Independent receipt SHA mismatch'}
$review=Get-Content -LiteralPath $reviewBinding.path -Raw|ConvertFrom-Json
$requiredFields=@('schema','status','reviewer','source_author','reviewer_distinct_from_SOURCE_AUTHOR','source_manifest_sha256','unresolved_blockers','primitive_enclosures_source_audited','analytic_remainders_source_audited','integer_endpoint_equivalence_source_audited','Gamma_value_projection_source_audited','fresh_constant_cache_source_audited','launch_tools_source_audited','resource_addendum_source_audited','same_math_parameters','global_h1_formal_proof','review_report_path','review_report_sha256','domain_addendum_path','domain_addendum_sha256','resource_addendum_path','resource_addendum_sha256','tool_bindings','future_evaluation_level','analytic_certification_level','structural_checker_is_interval_certificate','structural_PASS_is_enclosure_PASS')
foreach($name in $requiredFields) {if($review.PSObject.Properties.Name -notcontains $name) {throw "Actual review field absent: $name"}}
if($review.schema -ne 'ROUND22_PERFORMANCE_SOURCEPACK02_INDEPENDENT_REVIEW22' -or $review.status -ne 'SOURCE_REVIEW_NUMERICAL_ENCLOSURES_CLOSED' -or $review.reviewer -ne 'ROLE5' -or $review.source_author -ne 'ROLE3' -or $review.reviewer_distinct_from_SOURCE_AUTHOR -ne $true -or $review.source_manifest_sha256 -ne $sourceManifestSha -or $review.unresolved_blockers.Count -ne 0) {throw 'Actual independent candidate review not closed'}
foreach($name in @('primitive_enclosures_source_audited','analytic_remainders_source_audited','integer_endpoint_equivalence_source_audited','Gamma_value_projection_source_audited','fresh_constant_cache_source_audited','launch_tools_source_audited','resource_addendum_source_audited','same_math_parameters')) {if($review.$name -ne $true) {throw "Unpaid source obligation: $name"}}
if($review.global_h1_formal_proof -ne $false -or $review.structural_checker_is_interval_certificate -ne $false -or $review.structural_PASS_is_enclosure_PASS -ne $false -or $review.future_evaluation_level -ne $evaluationLevel -or $review.analytic_certification_level -ne $analyticLevel) {throw 'Paper/formal/structural boundary changed'}
AddBinding $reviewBinding
$reportBinding=Binding $review.review_report_path 'INDEPENDENT_SOURCE_REVIEW_REPORT'
$domainBinding=Binding $review.domain_addendum_path 'INDEPENDENT_SOURCE_REVIEW_DOMAIN_ADDENDUM'
$resourceBinding=Binding $review.resource_addendum_path 'INDEPENDENT_RESOURCE_ADDENDUM'
if($reportBinding.sha256 -ne $review.review_report_sha256 -or $domainBinding.sha256 -ne $review.domain_addendum_sha256 -or $resourceBinding.sha256 -ne $review.resource_addendum_sha256 -or $resourceBinding.path -ne (Join-Path $launcherDirectory 'resource_addendum_source22.md')) {throw 'Independent underlying reports/addendum changed'}
AddBinding $reportBinding; AddBinding $domainBinding; AddBinding $resourceBinding
$toolPaths=@($expectedTools|ForEach-Object {(Join-Path $launcherDirectory $_).ToLowerInvariant()}|Sort-Object)
$reviewToolPaths=@($review.tool_bindings|ForEach-Object {$_.path.ToLowerInvariant()}|Sort-Object)
if($review.tool_bindings.Count -ne 5 -or @($reviewToolPaths|Sort-Object -Unique).Count -ne 5 -or @(Compare-Object $toolPaths $reviewToolPaths).Count -ne 0) {throw 'Independent five-tool exact path set missing'}
foreach($entry in $review.tool_bindings) {CheckBinding $entry}
if($review.PSObject.Properties.Name -contains 'support_bindings') {foreach($entry in $review.support_bindings) {CheckBinding $entry;AddBinding (Binding $entry.path 'INDEPENDENT_REVIEW_SUPPORT')}}

$registry=Binding (Join-Path $roundDirectory 'previous_artifacts_sha256.json') 'PROTECTED_ARCHIVE_REGISTRY'
if($registry.sha256 -ne '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99') {throw 'Archive registry changed'}
$archive=Get-Content -LiteralPath $registry.path -Raw|ConvertFrom-Json
if($archive.file_count -ne 3089 -or @($archive.sha256.PSObject.Properties).Count -ne 3089) {throw 'Archive count changed'}
foreach($entry in $archive.sha256.PSObject.Properties) {
  $path=[IO.Path]::GetFullPath((Join-Path $researchBase $entry.Name))
  if(-not $path.StartsWith($researchBase+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)) {throw 'Archive path outside base'}
  if((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $entry.Value) {throw 'Archive bytes changed'}
}
AddBinding $registry
CheckClosedAttempt
$runtime=Binding $runtimePath 'CANONICAL_PYTHON_EXECUTABLE'
if($runtime.sha256 -ne '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c') {throw 'Canonical runtime changed'}
AddBinding $runtime
$runtimeFiles=@(Get-ChildItem -LiteralPath $runtimeRoot -File|Where-Object {$_.Extension -in @('.exe','.dll','.zip','.pth','.cfg','.pyd','.py','.pyc')})
foreach($name in @('DLLs','Lib')) {
  $directory=Join-Path $runtimeRoot $name
  if(Test-Path -LiteralPath $directory) {
    $runtimeFiles+=@(Get-ChildItem -LiteralPath $directory -File)
    foreach($child in @(Get-ChildItem -LiteralPath $directory -Directory|Where-Object {$name -ne 'Lib' -or $_.Name -ne 'site-packages'})) {$runtimeFiles+=@(Get-ChildItem -LiteralPath $child.FullName -File -Recurse)}
  }
}
$runtimeFiles=@($runtimeFiles|Sort-Object FullName -Unique)
if($runtimeFiles.Count -ne 972) {throw 'Exact972 conservatively inventoried runtime files required'}
foreach($file in $runtimeFiles) {if($file.FullName -ne $runtime.path) {AddBinding (Binding $file.FullName 'CANONICAL_PYTHON_STDLIB_NATIVE_BYTES')}}
$bindings=@(foreach($key in @($bindingByPath.Keys|Sort-Object)) {$bindingByPath[$key]})
$finalPaths=@($bindings|ForEach-Object {([string]$_['path']).ToLowerInvariant()}|Sort-Object)
$allExpected=@($expectedAllPaths|Sort-Object)
if($bindings.Count -ne $allExpected.Count -or @(Compare-Object $allExpected $finalPaths).Count -ne 0) {throw 'Exact all paths changed on ordering'}
$finalSource=@($bindings|Where-Object {$_.source_packet}|ForEach-Object {([string]$_['path']).ToLowerInvariant()}|Sort-Object)
if($finalSource.Count -ne 21 -or @(Compare-Object $sourcePaths $finalSource).Count -ne 0) {throw '21 source path set changed'}
$finalAliases=@($bindings|Where-Object {$_.module_alias}|ForEach-Object {$_.module_alias}|Sort-Object)
if($finalAliases.Count -ne 9 -or @($finalAliases|Sort-Object -Unique).Count -ne 9 -or @(Compare-Object ($expectedAliases|Sort-Object) $finalAliases).Count -ne 0) {throw 'Nine local alias set changed'}
$runtimePaths=@($runtimeFiles|ForEach-Object {$_.FullName.ToLowerInvariant()}|Sort-Object)
$finalRuntime=@($bindings|Where-Object {$_.kind -in @('CANONICAL_PYTHON_EXECUTABLE','CANONICAL_PYTHON_STDLIB_NATIVE_BYTES')}|ForEach-Object {([string]$_['path']).ToLowerInvariant()}|Sort-Object)
if(@(Compare-Object $runtimePaths $finalRuntime).Count -ne 0) {throw 'Runtime path set changed'}
$finalTools=@($bindings|Where-Object {$_.kind -eq 'NEW_LAUNCH_TOOLS_SOURCE'}|ForEach-Object {([string]$_['path']).ToLowerInvariant()}|Sort-Object)
if(@(Compare-Object $toolPaths $finalTools).Count -ne 0) {throw 'Five-tool path set changed'}
foreach($entry in $bindings) {CheckBinding $entry}
$timeUtc=[DateTime]::UtcNow.ToString('o')
$manifest=[ordered]@{schema='ROUND22_GLOBAL_THERMAL_PREPARED_MANIFEST_22';status='PREPARED_METADATA_ONLY_NOT_EXECUTED';created_utc=$timeUtc;actor='ROLE6';metadata_owner='ROLE3';scope=$scope;bank_id=$bankId;bindings=$bindings;binding_count=$bindings.Count;source_packet_bindings=21;source_manifest_sha256=$sourceManifestSha;runtime_module_aliases=$expectedAliases;runtime_files=972;independent_review_receipt_sha256=$reviewBinding.sha256;independent_review_report_sha256=$reportBinding.sha256;independent_domain_addendum_sha256=$domainBinding.sha256;resource_addendum_sha256=$resourceBinding.sha256;future_evaluation_level=$evaluationLevel;analytic_certification_level=$analyticLevel;structural_PASS_is_enclosure_PASS=$false;protected_archive_count=3089;closed_attempt_integrity_verified=$true;new_math_invocations=0;new_Lean_invocations=0;WIN=$false}
CreateJson $manifestPath $manifest
$manifestBinding=Binding $manifestPath 'PREPARED_MANIFEST'
$prep=[ordered]@{schema='ROUND22_GLOBAL_THERMAL_PREPARATION_22';status='PREPARED_METADATA_ONLY_NOT_EXECUTED';created_utc=$timeUtc;actor='ROLE6';metadata_owner='ROLE3';scope=$scope;bank_id=$bankId;bindings=($bindings+@($manifestBinding));binding_count=($bindings.Count+1);source_packet_bindings=21;source_packet_paths=$sourcePaths;runtime_files=972;prepared_manifest_sha256=$manifestBinding.sha256;runtime_path=$runtimePath;runtime_flags=@('-I','-S','-B','-X','utf8');root_gate_path=$gatePath;future_actual_directory=$actualDirectory;source_manifest_sha256=$sourceManifestSha;independent_review_receipt_sha256=$reviewBinding.sha256;independent_review_report_sha256=$reportBinding.sha256;independent_domain_addendum_sha256=$domainBinding.sha256;resource_addendum_sha256=$resourceBinding.sha256;future_evaluation_level=$evaluationLevel;analytic_certification_level=$analyticLevel;structural_PASS_is_enclosure_PASS=$false;child_path=(Join-Path $launcherDirectory 'thermal_child_source22.py');launcher_path=(Join-Path $launcherDirectory 'run_global_once_source22.py');runtime_alias_order=$expectedAliases;limits=$limits;closed_attempt_directory=$closedDirectory;structural_checker_alone_authorizes_PASS=$false;enclosure_review_required=$true;actual_boxtail_guard_required=$true;formal_H1='OPEN';horizontal_volet='UNIMPLEMENTED';coefficient_N='OPEN';D_N='UNPAID';WIN=$false;command_template=@($runtimePath,'-I','-S','-B','-X','utf8',(Join-Path $launcherDirectory 'run_global_once_source22.py'),'--root-authorization','EXACT_ROOT_GATE','--root-authorization-sha256','EXACT_ROOT_GATE_SHA')}
CreateJson $preparationPath $prep
[ordered]@{metadata_only=$true;binding_count=$prep.binding_count;all_path_sets_verified=$true;source_paths=21;runtime_aliases=9;runtime_files=972;protected_archives=3089;closed_attempt_intact=$true;prepared_manifest_sha256=$manifestBinding.sha256;preparation_sha256=(Get-FileHash -LiteralPath $preparationPath -Algorithm SHA256).Hash.ToLowerInvariant();new_math_invocations=0;new_Lean_invocations=0;gate_created=$false;actual_created=$false}|ConvertTo-Json -Depth 8
