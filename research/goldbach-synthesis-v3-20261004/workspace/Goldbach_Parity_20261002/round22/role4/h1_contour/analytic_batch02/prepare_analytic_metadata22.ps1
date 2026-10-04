# Metadata only: exact source copies, import headers, SHA256, judged artifacts.
# This script never invokes Lean or Python and never evaluates mathematics.
param(
    [Parameter(Mandatory=$true)][string]$DerivativeFinPath,
    [Parameter(Mandatory=$true)][string]$DerivativeReceiptPath,
    [Parameter(Mandatory=$true)][string]$DerivativeLogPath,
    [Parameter(Mandatory=$true)][string]$ContourSourcePath,
    [Parameter(Mandatory=$true)][string]$ContourSourceReadFull
)
$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$taskOwn = Join-Path $taskBase 'round22\role4'
$taskBatch = Join-Path $taskOwn 'h1_contour\analytic_batch02'
$taskSources = Join-Path $taskBatch 'source-final'
$taskPackages = 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages'
$taskToolchain = 'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0'
$taskPackageNames = @('aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq')
$taskBindings = @{}
$taskGraph = @{}
$taskLocal = @{}
$taskLocalOleans = @{}
$taskQueue = [System.Collections.Generic.Queue[string]]::new()
$taskManifestPath = Join-Path $taskBatch 'prepared_manifest22.json'
$taskReadPath = Join-Path $taskBatch 'read_receipts22.json'
if ((Test-Path -LiteralPath $taskManifestPath) -or (Test-Path -LiteralPath $taskReadPath)) {
    throw 'Preparation/read receipt already frozen; no overwrite.'
}
foreach ($name in @('ROLE4_BATCH02_LAUNCHER_FULL','ROLE4_BATCH02_HELPER_FULL','ROLE4_BATCH02_PREP_FULL',
    'ROLE4_BATCH02_DERIVATIVE_FIN_FULL','ROLE4_BATCH02_DERIVATIVE_RECEIPT_FULL','ROLE4_BATCH02_DERIVATIVE_LOG_FULL')) {
    if (-not [Environment]::GetEnvironmentVariable($name)) { throw "Actual FULL receipt absent: $name" }
}

function TaskSha([string]$p) {
    return (Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash.ToLowerInvariant()
}
function BindTask([string]$p) {
    $p = [System.IO.Path]::GetFullPath($p)
    $taskBindings[$p] = TaskSha $p
}
function TaskImports([string]$p) {
    $t = [System.IO.File]::ReadAllText($p)
    $depth = 0
    foreach ($line in ($t -split '\r?\n')) {
        $clean = [System.Text.StringBuilder]::new()
        for ($j=0;$j -lt $line.Length;$j++) {
            $ch = $line[$j]
            $next = if($j+1 -lt $line.Length){$line[$j+1]}else{[char]0}
            if ($ch -eq '/' -and $next -eq '-') { $depth++;$j++;continue }
            if ($depth -gt 0) {
                if ($ch -eq '-' -and $next -eq '/') { $depth--;$j++ }
                continue
            }
            if ($ch -eq '-' -and $next -eq '-') { break }
            [void]$clean.Append($ch)
        }
        $header = $clean.ToString().Trim()
        if (-not $header -or $header -eq 'prelude') { continue }
        if ($header -notmatch '^import\s+(.+)$') { break }
        foreach ($name in ($Matches[1].Trim() -split '\s+')) {
            if ($name -notmatch '^[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*$') {
                throw "Unsupported import syntax in $p"
            }
            $name
        }
    }
}
function ResolveTaskModule([string]$name) {
    $relative = $name.Replace('.','\')
    foreach ($pkg in $taskPackageNames) {
        $root = Join-Path $taskPackages $pkg
        $source = Join-Path $root ($relative + '.lean')
        $olean = Join-Path $root ('.lake\build\lib\' + $relative + '.olean')
        if ((Test-Path -LiteralPath $source) -and (Test-Path -LiteralPath $olean)) {
            return @{source=$source;olean=$olean;origin=$pkg}
        }
    }
    $source = Join-Path $taskToolchain ('src\lean\' + $relative + '.lean')
    $olean = Join-Path $taskToolchain ('lib\lean\' + $relative + '.olean')
    if ((Test-Path -LiteralPath $source) -and (Test-Path -LiteralPath $olean)) {
        return @{source=$source;olean=$olean;origin='PINNED_TOOLCHAIN'}
    }
    throw "Unresolved exact source/olean module $name"
}
function CheckedTaskCopy([string]$original,[string]$target) {
    if (-not (Test-Path -LiteralPath $target)) { Copy-Item -LiteralPath $original -Destination $target }
    if ((TaskSha $original) -ne (TaskSha $target)) { throw "Source copy differs: $target" }
    BindTask $original
    BindTask $target
}

# A true independent GammaDerivative FIN is checked before any preparation copy.
$taskDerivativeFin = Get-Content -LiteralPath $DerivativeFinPath -Raw | ConvertFrom-Json
if ($taskDerivativeFin.module -ne 'GammaDerivative22' -or
    $taskDerivativeFin.status -ne 'INDEPENDENT_LEAN_AUX_PASS' -or
    $taskDerivativeFin.exit_code -ne 0 -or -not $taskDerivativeFin.exact_axiom_coverage_standard_only -or
    $taskDerivativeFin.source_sha256 -ne '026ced6097c7d658b41501254bfbcdefe86ff2e68fb9fbe3fab01023a4cb0975') {
    throw 'GammaDerivative independent PASS is not actually available for exact author source.'
}
if ((TaskSha $DerivativeLogPath) -ne $taskDerivativeFin.stdout_sha256) {
    throw 'GammaDerivative actual independent log does not match FIN.'
}
if (-not (Test-Path -LiteralPath $taskSources)) { New-Item -ItemType Directory -Path $taskSources | Out-Null }
$taskSelections = @(
    @{module='GammaBoxBounds22';path=(Join-Path $taskOwn 'h1_contour\analytic_revision02\GammaBoxBounds22.lean');read='f2080d';count=12},
    @{module='GammaContourComponent22';path=$ContourSourcePath;read=$ContourSourceReadFull;count=11},
    @{module='MellinThermal22';path=(Join-Path $taskOwn 'h1_contour\MellinThermal22.lean');read='f2080d';count=12},
    @{module='MellinThermalInversion22';path=(Join-Path $taskOwn 'h1_contour\MellinThermalInversion22.lean');read='f2080d';count=4}
)
$taskModuleRows = @()
$taskCaptureRows = @()
foreach ($item in $taskSelections) {
    $target = Join-Path $taskSources ($item.module + '.lean')
    CheckedTaskCopy $item.path $target
    $text = [System.IO.File]::ReadAllText($target)
    $decls = @([regex]::Matches($text,'(?m)^(?:theorem|def)\s+(\w+)') | ForEach-Object {$_.Groups[1].Value})
    $prints = @([regex]::Matches($text,'(?m)^#print axioms GoldbachContinuous22\.(\w+)\s*$') | ForEach-Object {$_.Groups[1].Value})
    if ($decls.Count -ne $item.count -or ($decls -join '|') -ne ($prints -join '|')) {
        throw "Declaration/print coverage mismatch $($item.module)"
    }
    if ($text -match '\b(sorry|admit|axiom|unsafe|native_decide)\b') { throw 'Forbidden proof token.' }
    $taskLocal[$item.module] = $target
    $taskModuleRows += @{module=$item.module;original_source_path=$item.path;staged_source_path=$target;
        source_sha256=(TaskSha $target);declarations=$decls;qualified_print_count=$prints.Count;
        read_scope='FULL';read_capture=$item.read;compiled=$false}
    $taskCaptureRows += @{path=$target;name=($item.module+'.lean')}
}

$taskGammaJudge = Join-Path $taskBase 'round22\judge5\batch02_attempt01'
$taskDependencySpecs = @(
    @{module='GammaPrerequisites22';fin=(Join-Path $taskGammaJudge 'GammaPrerequisites22_FIN.json');
      receipt=(Join-Path $taskGammaJudge 'receipt.json');log=(Join-Path $taskGammaJudge 'GammaPrerequisites22.log');
      expected_source_sha='9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7';
      count=23;log_key='log_sha256';fin_read='c686d1';receipt_read='57db21';log_read_scope='TARGETED_80a204_ROOT_FULL_INDEPENDENT_AUDIT'},
    @{module='GammaDerivative22';fin=$DerivativeFinPath;receipt=$DerivativeReceiptPath;log=$DerivativeLogPath;
      expected_source_sha='026ced6097c7d658b41501254bfbcdefe86ff2e68fb9fbe3fab01023a4cb0975';
      count=8;log_key='stdout_sha256';fin_read=$env:ROLE4_BATCH02_DERIVATIVE_FIN_FULL;
      receipt_read=$env:ROLE4_BATCH02_DERIVATIVE_RECEIPT_FULL;log_read_scope=$env:ROLE4_BATCH02_DERIVATIVE_LOG_FULL}
)
$taskDependencyRows = @()
foreach ($item in $taskDependencySpecs) {
    $fin = Get-Content -LiteralPath $item.fin -Raw | ConvertFrom-Json
    if ($fin.module -ne $item.module -or $fin.status -ne 'INDEPENDENT_LEAN_AUX_PASS' -or
        $fin.exit_code -ne 0 -or -not $fin.exact_axiom_coverage_standard_only -or
        $fin.source_sha256 -ne $item.expected_source_sha) { throw 'Dependency is not exact actual judged PASS.' }
    $originalSource = [string]$fin.command[-1]
    $oleanIndex = [Array]::IndexOf(@($fin.command),'-o') + 1
    if ($oleanIndex -le 0) { throw 'Actual FIN does not identify an olean output.' }
    $originalOlean = [string]$fin.command[$oleanIndex]
    $targetSource = Join-Path $taskSources ($item.module+'.lean')
    $targetOlean = Join-Path $taskSources ($item.module+'.olean')
    CheckedTaskCopy $originalSource $targetSource
    CheckedTaskCopy $originalOlean $targetOlean
    if ((TaskSha $targetSource) -ne $fin.source_sha256 -or (TaskSha $targetOlean) -ne $fin.olean_sha256 -or
        (TaskSha $item.log) -ne $fin.($item.log_key)) { throw 'Actual judged source/olean/log bytes do not match FIN.' }
    $depText = [System.IO.File]::ReadAllText($targetSource)
    $depDecls = @([regex]::Matches($depText,'(?m)^(?:theorem|def)\s+(\w+)') | ForEach-Object {'GoldbachContinuous22.'+$_.Groups[1].Value})
    if ($depDecls.Count -ne $item.count -or
        ($depDecls -join '|') -ne (@($fin.axiom_rows | ForEach-Object {$_.declaration}) -join '|')) {
        throw 'Actual judged declaration coverage differs from staged dependency source.'
    }
    foreach ($row in $fin.axiom_rows) {
        foreach ($axiom in $row.axioms) { if ($axiom -notin @('propext','Classical.choice','Quot.sound')) {throw 'Nonstandard dependency axiom.'} }
    }
    $taskLocal[$item.module] = $targetSource
    $taskLocalOleans[$item.module] = $targetOlean
    foreach ($p in @($item.fin,$item.receipt,$item.log)) { BindTask $p }
    $taskDependencyRows += @{module=$item.module;staged_source_path=$targetSource;source_sha256=(TaskSha $targetSource);
        staged_olean_path=$targetOlean;olean_sha256=(TaskSha $targetOlean);independent_fin_path=$item.fin;
        independent_fin_sha256=(TaskSha $item.fin);independent_receipt_path=$item.receipt;
        independent_receipt_sha256=(TaskSha $item.receipt);independent_log_path=$item.log;
        independent_log_sha256=(TaskSha $item.log);independent_log_fin_field=$item.log_key;fin_read_full=$item.fin_read;
        receipt_read_full=$item.receipt_read;log_read_scope=$item.log_read_scope;recompile=$false}
    foreach ($entry in @(@{path=$targetSource;name=($item.module+'.lean')},@{path=$targetOlean;name=($item.module+'.olean')},
        @{path=$item.fin;name=($item.module+'_judged_FIN.json')},@{path=$item.receipt;name=($item.module+'_judged_receipt.json')},
        @{path=$item.log;name=($item.module+'_judged.log')})) { $taskCaptureRows += $entry }
}

foreach ($name in $taskLocal.Keys) { $taskQueue.Enqueue($name) }
# The implicit Init import is an explicit root; Init.Prelude is reached transitively.
$taskQueue.Enqueue('Init')
while ($taskQueue.Count -gt 0) {
    $name = $taskQueue.Dequeue()
    if ($taskGraph.ContainsKey($name)) { continue }
    if ($taskLocal.ContainsKey($name)) {
        $source = $taskLocal[$name]
        $olean = if($taskLocalOleans.ContainsKey($name)){$taskLocalOleans[$name]}else{$null}
        $origin = 'NEW_LOCAL_SOURCE_OR_ACTUAL_JUDGED_DEPENDENCY'
    } else {
        $resolved = ResolveTaskModule $name
        $source=$resolved.source;$olean=$resolved.olean;$origin=$resolved.origin
        BindTask $source
        BindTask $olean
    }
    $imports = @(TaskImports $source)
    $taskGraph[$name] = @{module=$name;source_path=$source;source_sha256=(TaskSha $source);
        olean_path=$olean;olean_sha256=$(if($olean){TaskSha $olean}else{$null});origin=$origin;
        imports=$imports;cache_read_scope='IMPORT_HEADERS_ONLY_NOT_FULL_API_TEXT'}
    foreach ($import in $imports) { $taskQueue.Enqueue($import) }
}
if (-not $taskGraph.ContainsKey('Init') -or -not $taskGraph.ContainsKey('Init.Prelude')) { throw 'Implicit Init closure absent.' }

$taskLean = Join-Path $taskToolchain 'bin\lean.exe'
$taskPython = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$taskRegistry = Join-Path $taskBase 'round22\previous_artifacts_sha256.json'
$taskRegistryData = Get-Content -LiteralPath $taskRegistry -Raw | ConvertFrom-Json
if ($taskRegistryData.file_count -ne 3089) { throw 'Unexpected archive registry count.' }
foreach ($prop in $taskRegistryData.sha256.PSObject.Properties) {
    if ((TaskSha (Join-Path $taskBase $prop.Name)) -ne $prop.Value) { throw "Changed protected archive $($prop.Name)" }
}
$taskPreviousReceipt = Join-Path $taskOwn 'h1_contour\analytic_batch01\actual_attempt01\receipt.json'
$taskPreviousPost = Join-Path $taskOwn 'h1_contour\analytic_batch01\actual_attempt01\POSTEXEC.json'
foreach ($p in @($taskLean,$taskPython,$taskRegistry,$taskPreviousReceipt,$taskPreviousPost,
    (Join-Path $taskBatch 'run_analytic_batch_once22.py'),$PSCommandPath,(Join-Path $taskBatch 'preparation22.md'),
    (Join-Path $taskOwn 'h1_contour\read_receipts22_v3.json'),(Join-Path $taskOwn 'h1_contour\read_receipts22_v4.json'),
    (Join-Path $taskOwn 'h1_contour\analytic_revision02\read_receipts22.json'),
    (Join-Path $taskOwn 'h1_contour\analytic_revision02\diagnostic22.md'),
    (Join-Path $taskBatch 'preserved_draft_9124\GammaContourComponent22.lean'))) { BindTask $p }
$taskReadReceipt = @{schema='ROUND22_ROLE4_ANALYTIC_BATCH02_READS';time_utc=[DateTime]::UtcNow.ToString('o');
    sources=$taskModuleRows;judged_dependencies=$taskDependencyRows;launcher_read=$env:ROLE4_BATCH02_LAUNCHER_FULL;
    helper_read=$env:ROLE4_BATCH02_HELPER_FULL;preparation_read=$env:ROLE4_BATCH02_PREP_FULL;
    critical_differentiableAt_api_read='TARGETED_037a81';cache_scope='IMPORT_HEADERS_ONLY_AND_BYTE_HASHES_NOT_FULL_API';
    previous_metadata_failure='0e0a0b: empty pipe parse before execution, corrected795901; no Lean/math/file mutation';
    new_lean_invocations=0;new_mathematical_python_invocations=0}
[System.IO.File]::WriteAllText($taskReadPath,($taskReadReceipt|ConvertTo-Json -Depth 20)+"`n",[System.Text.UTF8Encoding]::new($false))
BindTask $taskReadPath
foreach ($name in @('run_analytic_batch_once22.py','prepare_analytic_metadata22.ps1','preparation22.md','read_receipts22.json')) {
    $taskCaptureRows += @{path=(Join-Path $taskBatch $name);name=$name}
}
$taskCaptureRows += @{path=$taskRegistry;name='previous_artifacts_registry.json'}
$taskCaptureRows += @{path=$taskPreviousReceipt;name='previous_author_batch01_receipt.json'}
$taskCaptureRows += @{path=$taskPreviousPost;name='previous_author_batch01_POSTEXEC.json'}
$taskCaptureRows += @{path=(Join-Path $taskBatch 'preserved_draft_9124\GammaContourComponent22.lean');name='preserved_draft_GammaContour9124.lean'}
$taskManifest = @{schema='ROUND22_ROLE4_ANALYTIC_BATCH02_PREPARED';time_utc=[DateTime]::UtcNow.ToString('o');
    status='PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED';node='15.3';modules=$taskModuleRows;
    declaration_count=39;compiler_invocations_max=4;stop_first_failure=$true;retry_count=0;
    judged_dependencies=$taskDependencyRows;import_module_count=$taskGraph.Count;
    import_graph=@($taskGraph.Values|Sort-Object module);unresolved_modules=@();implicit_Init_root_bound=$true;
    cache_read_scope='IMPORT_HEADERS_ONLY_AND_SHA_NOT_FULL';
    immutable_inputs=@($taskBindings.Keys|Sort-Object|ForEach-Object {@{path=$_;sha256=$taskBindings[$_]}});
    capture_inputs=$taskCaptureRows;lean_sha256=(TaskSha $taskLean);python_sha256=(TaskSha $taskPython);
    previous_author_receipt_path=$taskPreviousReceipt;previous_author_receipt_sha256=(TaskSha $taskPreviousReceipt);
    numeric_status_is_not_a_premise=$true;archives_verified=3089;new_lean_invocations=0;
    new_mathematical_python_invocations=0;role4_lean_invocations_previously=5;
    global_h1_certified=$false;D_N_paid=$false;win=$false}
[System.IO.File]::WriteAllText($taskManifestPath,($taskManifest|ConvertTo-Json -Depth 30)+"`n",[System.Text.UTF8Encoding]::new($false))
[pscustomobject]@{status=$taskManifest.status;modules=4;declarations=39;judged_dependencies=2;
    import_modules=$taskGraph.Count;immutable_bindings=$taskBindings.Count;manifest_sha256=(TaskSha $taskManifestPath);
    read_receipts_sha256=(TaskSha $taskReadPath);archives_verified=3089;new_lean_invocations=0;new_math_invocations=0}|ConvertTo-Json
