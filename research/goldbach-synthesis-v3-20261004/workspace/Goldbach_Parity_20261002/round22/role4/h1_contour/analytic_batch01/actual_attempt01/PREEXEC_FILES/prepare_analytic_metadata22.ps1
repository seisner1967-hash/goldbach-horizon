# Metadata only: source copies, import headers, SHA256 and closed manifest.
# No Lean, Python import, mathematical evaluation, Git, or installation.
$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$taskOwn = Join-Path $taskBase 'round22\role4'
$taskBatch = Join-Path $taskOwn 'h1_contour\analytic_batch01'
$taskSources = Join-Path $taskBatch 'sources'
$taskPackages = 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages'
$taskToolchain = 'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0'
$taskPackageNames = @('aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq')
$taskBindings = @{}
$taskGraph = @{}
$taskLocal = @{}
$taskQueue = [System.Collections.Generic.Queue[string]]::new()
$taskManifestPath = Join-Path $taskBatch 'prepared_manifest22.json'
if (Test-Path -LiteralPath $taskManifestPath) { throw 'Preparation already frozen; no overwrite.' }

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
if (-not (Test-Path -LiteralPath $taskSources)) {
    New-Item -ItemType Directory -Path $taskSources | Out-Null
}
$taskSelections = @(
    @{module='GammaDerivative22';path=(Join-Path $taskOwn 'GammaDerivative22.lean');read='57db21';count=8},
    @{module='GammaBoxBounds22';path=(Join-Path $taskOwn 'GammaBoxBounds22.lean');read='57db21';count=12},
    @{module='GammaContourComponent22';path=(Join-Path $taskOwn 'h1_contour\gamma_revision01\GammaContourComponent22.lean');read='aac0f5';count=11},
    @{module='MellinThermal22';path=(Join-Path $taskOwn 'h1_contour\MellinThermal22.lean');read='80a3b6';count=12},
    @{module='MellinThermalInversion22';path=(Join-Path $taskOwn 'h1_contour\MellinThermalInversion22.lean');read='af5253';count=4}
)
$taskModuleRows = @()
$taskCaptureRows = @()
foreach ($item in $taskSelections) {
    $target = Join-Path $taskSources ($item.module + '.lean')
    if (-not (Test-Path -LiteralPath $target)) { Copy-Item -LiteralPath $item.path -Destination $target }
    if ((TaskSha $item.path) -ne (TaskSha $target)) { throw 'Source copy changed bytes.' }
    $text = [System.IO.File]::ReadAllText($target)
    $decls = @([regex]::Matches($text,'(?m)^(?:theorem|def)\s+(\w+)') | ForEach-Object {$_.Groups[1].Value})
    $prints = @([regex]::Matches($text,'(?m)^#print axioms GoldbachContinuous22\.(\w+)\s*$') | ForEach-Object {$_.Groups[1].Value})
    if ($decls.Count -ne $item.count -or ($decls -join '|') -ne ($prints -join '|')) {
        throw "Declaration/print coverage mismatch $($item.module)"
    }
    if ($text -match '\b(sorry|admit|axiom|unsafe|native_decide)\b') { throw 'Forbidden proof token.' }
    BindTask $item.path
    BindTask $target
    $taskLocal[$item.module] = $target
    $taskModuleRows += @{module=$item.module;original_source_path=$item.path;staged_source_path=$target;
        source_sha256=(TaskSha $target);declarations=$decls;qualified_print_count=$prints.Count;
        read_scope='FULL';read_capture=$item.read;compiled=$false}
    $taskCaptureRows += @{path=$target;name=($item.module+'.lean')}
}
$taskJudge = Join-Path $taskBase 'round22\judge5\batch02_attempt01'
$taskGammaOriginal = Join-Path $taskOwn 'revision02\GammaPrerequisites22.lean'
$taskGammaSource = Join-Path $taskSources 'GammaPrerequisites22.lean'
$taskGammaOlean = Join-Path $taskSources 'GammaPrerequisites22.olean'
$taskGammaFin = Join-Path $taskJudge 'GammaPrerequisites22_FIN.json'
$taskGammaReceipt = Join-Path $taskJudge 'receipt.json'
if (-not (Test-Path -LiteralPath $taskGammaSource)) {
    Copy-Item -LiteralPath $taskGammaOriginal -Destination $taskGammaSource
}
if (-not (Test-Path -LiteralPath $taskGammaOlean)) {
    Copy-Item -LiteralPath (Join-Path $taskJudge 'GammaPrerequisites22.olean') -Destination $taskGammaOlean
}
$taskGammaRow = Get-Content -LiteralPath $taskGammaFin -Raw | ConvertFrom-Json
if ($taskGammaRow.status -ne 'INDEPENDENT_LEAN_AUX_PASS' -or $taskGammaRow.exit_code -ne 0 -or
    -not $taskGammaRow.exact_axiom_coverage_standard_only -or
    (TaskSha $taskGammaSource) -ne $taskGammaRow.source_sha256 -or
    (TaskSha $taskGammaOlean) -ne $taskGammaRow.olean_sha256) { throw 'Gamma dependency is not actual judged PASS bytes.' }
$taskLocal['GammaPrerequisites22'] = $taskGammaSource
foreach ($p in @($taskGammaOriginal,$taskGammaSource,$taskGammaOlean,$taskGammaFin,$taskGammaReceipt,
    (Join-Path $taskJudge 'GammaPrerequisites22.olean'),(Join-Path $taskJudge 'GammaPrerequisites22.log'))) { BindTask $p }
foreach ($name in $taskLocal.Keys) { $taskQueue.Enqueue($name) }
# Lean automatically imports Init for each non-prelude module.
$taskQueue.Enqueue('Init')
while ($taskQueue.Count -gt 0) {
    $name = $taskQueue.Dequeue()
    if ($taskGraph.ContainsKey($name)) { continue }
    if ($taskLocal.ContainsKey($name)) {
        $source = $taskLocal[$name]
        $olean = if ($name -eq 'GammaPrerequisites22') {$taskGammaOlean} else {$null}
        $origin = 'NEW_LOCAL_SOURCE_OR_JUDGED_DEPENDENCY'
    } else {
        $resolved = ResolveTaskModule $name
        $source = $resolved.source
        $olean = $resolved.olean
        $origin = $resolved.origin
        BindTask $source
        BindTask $olean
    }
    $imports = @(TaskImports $source)
    $taskGraph[$name] = @{module=$name;source_path=$source;source_sha256=(TaskSha $source);
        olean_path=$olean;olean_sha256=$(if($olean){TaskSha $olean}else{$null});origin=$origin;
        imports=$imports;cache_read_scope='IMPORT_HEADERS_ONLY_NOT_FULL_API_TEXT'}
    foreach ($import in $imports) { $taskQueue.Enqueue($import) }
}
$taskLean = Join-Path $taskToolchain 'bin\lean.exe'
$taskPython = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$taskOldBank = Join-Path $taskBase 'round22\role6\gamma_h2\actual_gamma22\gamma_result22.json'
$taskTechnicalFailure = Join-Path $taskBase 'round22\role6\thermal_h1\actual_component22\actual_receipt.json'
$taskFailureClosure = Join-Path $taskBase 'round22\role6\thermal_h1\component_failure_receipt22.json'
$taskRegistry = Join-Path $taskBase 'round22\previous_artifacts_sha256.json'
$taskRegistryData = Get-Content -LiteralPath $taskRegistry -Raw | ConvertFrom-Json
if ($taskRegistryData.file_count -ne 3089) { throw 'Unexpected archive registry count.' }
foreach ($prop in $taskRegistryData.sha256.PSObject.Properties) {
    if ((TaskSha (Join-Path $taskBase $prop.Name)) -ne $prop.Value) { throw "Changed protected archive $($prop.Name)" }
}
foreach ($p in @($taskLean,$taskPython,$taskOldBank,$taskTechnicalFailure,$taskFailureClosure,$taskRegistry,
    (Join-Path $taskBatch 'run_analytic_batch_once22.py'),$PSCommandPath,
    (Join-Path $taskBatch 'preparation22.md'),(Join-Path $taskOwn 'h1_contour\read_receipts22_v3.json'),
    (Join-Path $taskOwn 'h1_contour\read_receipts22_v4.json'))) { BindTask $p }
$taskReadReceipt = @{schema='ROUND22_ROLE4_ANALYTIC_BATCH01_READS';time_utc=[DateTime]::UtcNow.ToString('o');
    sources=$taskModuleRows;gamma_fin_read='FULL_af5253';gamma_judge_receipt_read='FULL_57db21';
    launcher_read='FULL_PENDING_REPLACED_BEFORE_PREPARED';helper_read='FULL_PENDING_REPLACED_BEFORE_PREPARED';
    cache_scope='IMPORT_HEADERS_ONLY_AND_BYTE_HASHES_NOT_FULL_API';
    previous_metadata_failure='b26830: doc-comment line import cycle falsely parsed; no manifest/Lean/math; lexical header parsing repaired, source bytes unchanged';
    lean_invocations=0;mathematical_python_invocations=0}
# The caller must give the actual FULL read identifiers; absence stops preparation.
if (-not $env:ROLE4_BATCH_LAUNCHER_FULL -or -not $env:ROLE4_BATCH_HELPER_FULL -or -not $env:ROLE4_BATCH_PREP_FULL) {
    throw 'Actual FULL launcher/helper/preparation read receipts absent.'
}
$taskReadReceipt.launcher_read = $env:ROLE4_BATCH_LAUNCHER_FULL
$taskReadReceipt.helper_read = $env:ROLE4_BATCH_HELPER_FULL
$taskReadReceipt.preparation_read = $env:ROLE4_BATCH_PREP_FULL
$taskReadPath = Join-Path $taskBatch 'read_receipts22.json'
[System.IO.File]::WriteAllText($taskReadPath,($taskReadReceipt|ConvertTo-Json -Depth 20)+"`n",[System.Text.UTF8Encoding]::new($false))
BindTask $taskReadPath
foreach ($name in @('run_analytic_batch_once22.py','prepare_analytic_metadata22.ps1','preparation22.md','read_receipts22.json')) {
    $taskCaptureRows += @{path=(Join-Path $taskBatch $name);name=$name}
}
$taskCaptureRows += @{path=$taskGammaSource;name='GammaPrerequisites22.lean'}
$taskCaptureRows += @{path=$taskGammaOlean;name='GammaPrerequisites22.olean'}
$taskCaptureRows += @{path=$taskGammaFin;name='judged_Gamma_FIN.json'}
$taskCaptureRows += @{path=$taskGammaReceipt;name='judged_batch02_receipt.json'}
$taskCaptureRows += @{path=$taskRegistry;name='previous_artifacts_registry.json'}
$taskCaptureRows += @{path=$taskFailureClosure;name='component_failure_closure.json'}
$taskManifest = @{schema='ROUND22_ROLE4_ANALYTIC_BATCH01_PREPARED';time_utc=[DateTime]::UtcNow.ToString('o');
    status='PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED';node='15.3';modules=$taskModuleRows;
    declaration_count=47;compiler_invocations_max=5;stop_first_failure=$true;retry_count=0;
    gamma_dependency=@{staged_source_path=$taskGammaSource;source_sha256=(TaskSha $taskGammaSource);
        staged_olean_path=$taskGammaOlean;olean_sha256=(TaskSha $taskGammaOlean);
        independent_receipt_path=$taskGammaReceipt;independent_receipt_sha256=(TaskSha $taskGammaReceipt);recompile=$false};
    import_module_count=$taskGraph.Count;import_graph=@($taskGraph.Values|Sort-Object module);unresolved_modules=@();implicit_Init_root_bound=$true;
    cache_read_scope='IMPORT_HEADERS_ONLY_AND_SHA_NOT_FULL';
    immutable_inputs=@($taskBindings.Keys|Sort-Object|ForEach-Object {@{path=$_;sha256=$taskBindings[$_]}});
    capture_inputs=$taskCaptureRows;lean_sha256=(TaskSha $taskLean);python_sha256=(TaskSha $taskPython);
    existing_gamma_bank_path=$taskOldBank;existing_gamma_bank_sha256=(TaskSha $taskOldBank);
    component_technical_failure_receipt_path=$taskTechnicalFailure;component_technical_failure_receipt_sha256=(TaskSha $taskTechnicalFailure);
    numeric_component_pass=$false;numeric_failure_not_a_formula_counterexample=$true;
    archives_verified=3089;new_lean_invocations=0;new_mathematical_python_invocations=0;
    global_h1_certified=$false;D_N_paid=$false;win=$false}
[System.IO.File]::WriteAllText($taskManifestPath,($taskManifest|ConvertTo-Json -Depth 30)+"`n",[System.Text.UTF8Encoding]::new($false))
[pscustomobject]@{status=$taskManifest.status;modules=5;declarations=47;import_modules=$taskGraph.Count;
    immutable_bindings=$taskBindings.Count;manifest_sha256=(TaskSha $taskManifestPath);
    read_receipts_sha256=(TaskSha $taskReadPath);archives_verified=3089;new_lean_invocations=0;new_math_invocations=0}|ConvertTo-Json
