# SOURCE ONLY. Do not invoke until the independent review and ROOT metadata gate.
# This builder hashes/copies no mathematical values, starts no Python/Lean, and
# never creates an authorization. New files are exclusive-create, no overwrite.
param(
    [Parameter(Mandatory=$true)][string]$IndependentReviewReceipt,
    [Parameter(Mandatory=$true)][string]$IndependentReviewReceiptSha256,
    [Parameter(Mandatory=$true)][ValidateRange(60,432000)][int]$MaxWallSeconds,
    [Parameter(Mandatory=$true)][ValidateRange(4194304,1099511627776)][long]$MaxArtifactBytes
)
$ErrorActionPreference='Stop'
$launcherDirectory=$PSScriptRoot
$packetDirectory=Split-Path $launcherDirectory -Parent
$roundDirectory=Split-Path (Split-Path $packetDirectory -Parent) -Parent
$researchBase=Split-Path $roundDirectory -Parent
$runtimePath='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$runtimeRoot=Split-Path $runtimePath -Parent
$gatePath=Join-Path $researchBase '.arbor\sessions\parity\.coordinator\messages\round22_global_thermal_h1_authorization01.json'
$sourceManifestPath=Join-Path $packetDirectory 'source_manifest22.json'
$manifestPath=Join-Path $launcherDirectory 'prepared_manifest22.json'
$preparationPath=Join-Path $launcherDirectory 'preparation22.json'
$actualDirectory=Join-Path $launcherDirectory 'actual_attempt01'
$scope='ROUND22_GLOBAL_THERMAL_H1_NUMERIC_ONLY'
$bankId='THERMAL_GLOBAL_H1_22_SOURCEPACK01'
$evaluationLevel='PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER'
$analyticLevel='PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION'

function Binding([string]$Path,[string]$Kind,[string]$Alias='') {
    $resolved=(Resolve-Path -LiteralPath $Path).Path
    return [ordered]@{path=$resolved;sha256=(Get-FileHash -LiteralPath $resolved -Algorithm SHA256).Hash.ToLowerInvariant();bytes=(Get-Item -LiteralPath $resolved).Length;kind=$Kind;module_alias=$Alias}
}
function CreateJson([string]$Path,$Data) {
    $content=[Text.UTF8Encoding]::new($false).GetBytes(($Data|ConvertTo-Json -Depth 40)+"`n")
    $stream=[IO.File]::Open($Path,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write)
    try {$stream.Write($content,0,$content.Length)} finally {$stream.Dispose()}
}
function CheckBinding($Expected) {
    $actual=Binding $Expected.path 'VERIFY_ONLY'
    if($actual.sha256 -ne $Expected.sha256 -or $actual.bytes -ne $Expected.bytes) {throw "Input bytes changed: $($Expected.path)"}
}
foreach($path in @($manifestPath,$preparationPath,$actualDirectory,$gatePath)) {
    if(Test-Path -LiteralPath $path) {throw "Reserved output/gate exists; no overwrite or retry: $path"}
}
$sourceManifestBinding=Binding $sourceManifestPath 'SOURCE_MANIFEST'
if($sourceManifestBinding.sha256 -ne 'e1caa3d115dd492cfa6d91478240b0e8418614b6faf8798f48e15312dfe11a51') {throw 'Selected14binding source manifest changed; prepare a distinct revision.'}
$source=Get-Content -LiteralPath $sourceManifestPath -Raw|ConvertFrom-Json
if($source.status -ne 'SOURCE_REVIEW_READY_THERMAL_C3_ONLY' -or $source.bindings.Count -ne 14 -or $source.runtime_python_modules -ne 9) {throw 'Wrong source scope/count.'}
$bindings=@()
foreach($entry in $source.bindings) {
    CheckBinding $entry
    $bindings+=Binding $entry.path 'SOURCE_PACKET_INPUT' $entry.module_alias
}
$bindings+=$sourceManifestBinding
$sourceReads=Binding (Join-Path $packetDirectory 'read_receipts22.json') 'SOURCE_TEXT_READ_RECEIPTS'
if($sourceReads.sha256 -ne 'b54727ef3b21284fcd3f2f02cbfbab9356f3bfea793014e0e572e4cbec4a5ecd') {throw 'Source read receipts changed.'}
$bindings+=$sourceReads
$aliases=@($bindings|Where-Object {$_.module_alias}|ForEach-Object {$_.module_alias})
$expectedAliases=@('dyadic_r01','analytic_r01','kernel_r01','unit_transport_source22','arithmetic_catalogue_source22','transport_catalogue_source22','envelopes_source22','producer_source22','structural_checker_source22')
if($aliases.Count -ne 9 -or @($aliases|Sort-Object -Unique).Count -ne 9) {throw 'Exactly nine distinct runtime aliases required.'}
foreach($alias in $expectedAliases) {if($aliases -notcontains $alias) {throw "Missing runtime alias: $alias"}}

# This actual administrative review cannot be synthesized by the builder.
# ROOT must read its underlying report before authorizing a numerical child.
$reviewBinding=Binding $IndependentReviewReceipt 'INDEPENDENT_SOURCE_REVIEW_RECEIPT'
if($reviewBinding.sha256 -ne $IndependentReviewReceiptSha256.ToLowerInvariant()) {throw 'Independent review receipt byte mismatch.'}
$review=Get-Content -LiteralPath $reviewBinding.path -Raw|ConvertFrom-Json
foreach($name in @('schema','status','reviewer','reviewer_distinct_from_ROLE4','source_manifest_sha256','unresolved_blockers','primitive_enclosures_source_audited','analytic_remainders_source_audited','global_h1_formal_proof','review_report_path','review_report_sha256','domain_addendum_path','domain_addendum_sha256','future_evaluation_level','analytic_certification_level','structural_checker_is_interval_certificate','structural_PASS_is_enclosure_PASS')) {
    if($review.PSObject.Properties.Name -notcontains $name) {throw "Required actual review field absent: $name"}
}
if($review.schema -ne 'ROUND22_GLOBAL_THERMAL_SOURCE_REVIEW_22' -or $review.status -ne 'SOURCE_REVIEW_NUMERICAL_ENCLOSURES_CLOSED' -or $review.reviewer -eq 'ROLE4' -or -not $review.reviewer) {throw 'Concrete independent enclosure review not closed.'}
if($review.source_manifest_sha256 -ne $sourceManifestBinding.sha256 -or $review.unresolved_blockers.Count -ne 0 -or $review.primitive_enclosures_source_audited -ne $true -or $review.analytic_remainders_source_audited -ne $true -or $review.global_h1_formal_proof -ne $false) {throw 'Review scope/closure/formal boundary invalid.'}
if($review.reviewer_distinct_from_ROLE4 -ne $true -or $review.future_evaluation_level -ne $evaluationLevel -or $review.analytic_certification_level -ne $analyticLevel -or $review.structural_checker_is_interval_certificate -ne $false -or $review.structural_PASS_is_enclosure_PASS -ne $false) {throw 'Independent paper/structural certification boundary invalid.'}
$reportBinding=Binding $review.review_report_path 'INDEPENDENT_SOURCE_REVIEW_REPORT'
if($reportBinding.sha256 -ne $review.review_report_sha256) {throw 'Underlying independent report changed.'}
$domainBinding=Binding $review.domain_addendum_path 'INDEPENDENT_SOURCE_REVIEW_DOMAIN_ADDENDUM'
if($domainBinding.sha256 -ne $review.domain_addendum_sha256) {throw 'Underlying independent domain addendum changed.'}
$bindings+=$reviewBinding
$bindings+=$reportBinding
$bindings+=$domainBinding
if($review.PSObject.Properties.Name -contains 'support_bindings') {
    foreach($entry in $review.support_bindings) {
        CheckBinding $entry
        $bindings+=Binding $entry.path 'INDEPENDENT_SOURCE_REVIEW_SUPPORT'
    }
}

$registry=Binding (Join-Path $roundDirectory 'previous_artifacts_sha256.json') 'PROTECTED_ARCHIVE_REGISTRY'
if($registry.sha256 -ne '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99') {throw 'Protected registry changed.'}
$archiveData=Get-Content -LiteralPath $registry.path -Raw|ConvertFrom-Json
if($archiveData.file_count -ne 3089 -or @($archiveData.sha256.PSObject.Properties).Count -ne 3089) {throw 'Protected archive count changed.'}
foreach($entry in $archiveData.sha256.PSObject.Properties) {
    $archivePath=[IO.Path]::GetFullPath((Join-Path $researchBase $entry.Name))
    if(-not $archivePath.StartsWith($researchBase+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)) {throw 'Registry path outside research base.'}
    if((Get-FileHash -LiteralPath $archivePath -Algorithm SHA256).Hash.ToLowerInvariant() -ne $entry.Value) {throw "Protected bytes changed: $($entry.Name)"}
}
$bindings+=$registry
foreach($name in @('prepare_metadata_source22.ps1','run_global_once_source22.py','thermal_child_source22.py','launch_contract_source22.md')) {
    $bindings+=Binding (Join-Path $launcherDirectory $name) 'NEW_LAUNCH_TOOLS_SOURCE'
}
$runtime=Binding $runtimePath 'CANONICAL_PYTHON_EXECUTABLE'
if($runtime.sha256 -ne '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c') {throw 'Canonical runtime changed.'}
$bindings+=$runtime

# Conservative installed stdlib/native inventory, read/hash only, no imports.
# -I -S suppress site/user startup. OS libraries are outside this byte inventory.
$runtimeFiles=@()
$runtimeFiles+=@(Get-ChildItem -LiteralPath $runtimeRoot -File|Where-Object {$_.Extension -in @('.exe','.dll','.zip','.pth','.cfg','.pyd','.py','.pyc')})
foreach($name in @('DLLs','Lib')) {
    $directory=Join-Path $runtimeRoot $name
    if(Test-Path -LiteralPath $directory) {
        $runtimeFiles+=@(Get-ChildItem -LiteralPath $directory -File)
        foreach($childDirectory in @(Get-ChildItem -LiteralPath $directory -Directory|Where-Object {$name -ne 'Lib' -or $_.Name -ne 'site-packages'})) {
            $runtimeFiles+=@(Get-ChildItem -LiteralPath $childDirectory.FullName -File -Recurse)
        }
    }
}
$runtimeFiles=@($runtimeFiles|Sort-Object FullName -Unique)
if($runtimeFiles.Count -lt 1) {throw 'Runtime file inventory absent.'}
foreach($file in $runtimeFiles) {
    if($file.FullName -ne $runtime.path) {$bindings+=Binding $file.FullName 'CANONICAL_PYTHON_STDLIB_NATIVE_BYTES'}
}
$bindings=@($bindings|Sort-Object path -Unique)
$timeUtc=[DateTime]::UtcNow.ToString('o')
$manifest=[ordered]@{schema='ROUND22_GLOBAL_THERMAL_PREPARED_MANIFEST_22';created_utc=$timeUtc;status='PREPARED_METADATA_ONLY_NOT_EXECUTED';actor='ROLE6';metadata_owner='ROLE4';scope=$scope;bank_id=$bankId;bindings=$bindings;binding_count=$bindings.Count;source_manifest_sha256=$sourceManifestBinding.sha256;source_packet_bindings=14;runtime_module_aliases=$expectedAliases;independent_review_receipt_sha256=$reviewBinding.sha256;independent_review_report_sha256=$reportBinding.sha256;independent_domain_addendum_sha256=$domainBinding.sha256;future_evaluation_level=$evaluationLevel;analytic_certification_level=$analyticLevel;structural_PASS_is_enclosure_PASS=$false;protected_archive_count=3089;protected_registry_sha256=$registry.sha256;runtime_inventory_scope='bundled stdlib/native bytes; site disabled; no OS system-library inventory';cost_measured=$false;new_math_invocations=0;new_Lean_invocations=0;WIN=$false}
CreateJson $manifestPath $manifest
$manifestBinding=Binding $manifestPath 'PREPARED_MANIFEST'
$prep=[ordered]@{schema='ROUND22_GLOBAL_THERMAL_PREPARATION_22';created_utc=$timeUtc;status='PREPARED_METADATA_ONLY_NOT_EXECUTED';actor='ROLE6';metadata_owner='ROLE4';scope=$scope;bank_id=$bankId;bindings=($bindings+@($manifestBinding));binding_count=($bindings.Count+1);prepared_manifest_sha256=$manifestBinding.sha256;runtime_path=$runtimePath;runtime_flags=@('-I','-S','-B','-X','utf8');root_gate_path=$gatePath;future_actual_directory=$actualDirectory;source_manifest_sha256=$sourceManifestBinding.sha256;independent_review_receipt_sha256=$reviewBinding.sha256;independent_review_report_sha256=$reportBinding.sha256;independent_domain_addendum_sha256=$domainBinding.sha256;future_evaluation_level=$evaluationLevel;analytic_certification_level=$analyticLevel;structural_PASS_is_enclosure_PASS=$false;child_path=(Join-Path $launcherDirectory 'thermal_child_source22.py');launcher_path=(Join-Path $launcherDirectory 'run_global_once_source22.py');runtime_alias_order=$expectedAliases;limits=@{max_children=1;retry_count=0;max_wall_seconds=$MaxWallSeconds;max_artifact_bytes=$MaxArtifactBytes;expected_vertical_nodes=204800;expected_arch_nodes=12288;expected_arithmetic_integers=999999;catalogue_parameter_change_allowed=$false};structural_checker_alone_authorizes_PASS=$false;enclosure_review_required=$true;actual_boxtail_guard_required=$true;formal_H1='OPEN';horizontal_volet='UNIMPLEMENTED';coefficient_N='OPEN';D_N='UNPAID';WIN=$false;command_template=@($runtimePath,'-I','-S','-B','-X','utf8',(Join-Path $launcherDirectory 'run_global_once_source22.py'),'--root-authorization','EXACT_ROOT_GATE','--root-authorization-sha256','EXACT_ROOT_GATE_SHA')}
CreateJson $preparationPath $prep
[ordered]@{metadata_only=$true;binding_count=$prep.binding_count;prepared_manifest_sha256=$manifestBinding.sha256;preparation_sha256=(Get-FileHash -LiteralPath $preparationPath -Algorithm SHA256).Hash.ToLowerInvariant();runtime_inventory_files=$runtimeFiles.Count;protected_archive_count=3089;no_runtime_invocation=$true;gate_created=$false;actual_created=$false;new_math_invocations=0;new_Lean_invocations=0} |ConvertTo-Json -Depth 8
