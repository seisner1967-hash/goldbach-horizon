param(
    [string[]] $NewModules = @('ParityWeights'),
    [string[]] $ExtraDependencies = @(),
    [string] $Compiler = 'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe',
    [string] $CacheRoot = 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages',
    [string] $DependencySources = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Research_20260930\sprint15\agents\full_project_replayfresh'
)

# Offline independent replay. New/dependency .olean files are always rebuilt
# from their corresponding .lean source. Only mathlib package cache is reused.
$ErrorActionPreference = 'Stop'
$TaskRoot = $PSScriptRoot
$JudgeRoot = Join-Path $TaskRoot 'judge'
$Dependencies = Join-Path $JudgeRoot 'dependencies'
$Outputs = Join-Path $JudgeRoot 'output'
$Logs = Join-Path $JudgeRoot 'logs'
$Utf8 = [System.Text.UTF8Encoding]::new($false)
foreach ($Directory in @($JudgeRoot, $Dependencies, $Outputs, $Logs)) {
    [void](New-Item -ItemType Directory -Path $Directory -Force)
}
$Packages = @('aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq')
$PackagePaths = @($Packages | ForEach-Object { Join-Path $CacheRoot "$_\.lake\build\lib" })
foreach ($Path in @($Compiler, $DependencySources) + $PackagePaths) {
    if (-not (Test-Path -LiteralPath $Path)) { throw "Missing offline prerequisite: $Path" }
}
$Version = (& $Compiler '--version' 2>&1 | Out-String).Trim()
if ($LASTEXITCODE -ne 0 -or $Version -notmatch 'version 4\.15\.0') {
    throw "Unexpected Lean compiler: $Version"
}
$NumericalPath = Join-Path $TaskRoot 'numerical\numerical.json'
$Numerical = Get-Content -LiteralPath $NumericalPath -Raw | ConvertFrom-Json -AsHashtable
if ($Numerical.status -ne 'PASS' -or $Numerical.N -ne 100000000) {
    throw 'Numeric falsification gate has not passed at N=100000000'
}
$SupplementalGates = [System.Collections.Generic.List[object]]::new()
if ($NewModules -contains 'ChenWeight') {
    $ChenGatePath = Join-Path $TaskRoot 'numerical\chen_multiplicity.json'
    $ChenGate = Get-Content -LiteralPath $ChenGatePath -Raw | ConvertFrom-Json -AsHashtable
    if ($ChenGate.status -ne 'PASS' -or $ChenGate.N -ne 100000000 -or $ChenGate.case_count -lt 1) {
        throw 'Chen multiplicity falsification gate has not passed at N=100000000'
    }
    $SupplementalGates.Add([ordered]@{
        module = 'ChenWeight'; path = $ChenGatePath; status = $ChenGate.status
        N = $ChenGate.N; alpha = $ChenGate.alpha; case_count = $ChenGate.case_count
        sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $ChenGatePath).Hash.ToLowerInvariant()
        numerical_script_sha256 = $ChenGate.script_sha256
        scope = $ChenGate.scope
    })
}
$PreviousLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = (@($Dependencies, $Outputs) + $PackagePaths) -join ';'
$Receipts = [System.Collections.Generic.List[object]]::new()
$ApprovedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
$AuditFailures = [System.Collections.Generic.List[string]]::new()

function Get-LeanCode {
    param([string] $Text)
    # Skip nested Lean block comments, line comments, and quoted strings.
    # This is a token audit of code, not a rejection of explanatory prose.
    $Builder = [System.Text.StringBuilder]::new()
    $Depth = 0
    $LineComment = $false
    $InString = $false
    $Index = 0
    while ($Index -lt $Text.Length) {
        $Character = $Text[$Index]
        $Pair = if ($Index + 1 -lt $Text.Length) { $Text.Substring($Index, 2) } else { '' }
        if ($LineComment) {
            if ($Character -eq "`n") { $LineComment = $false; [void]$Builder.Append($Character) }
            else { [void]$Builder.Append(' ') }
            $Index++; continue
        }
        if ($Depth -gt 0) {
            if ($Pair -eq '/-') { $Depth++; [void]$Builder.Append('  '); $Index += 2; continue }
            if ($Pair -eq '-/') { $Depth--; [void]$Builder.Append('  '); $Index += 2; continue }
            if ($Character -eq "`n") { [void]$Builder.Append($Character) }
            else { [void]$Builder.Append(' ') }
            $Index++; continue
        }
        if ($InString) {
            if ($Character -eq [char]92 -and $Index + 1 -lt $Text.Length) { [void]$Builder.Append('  '); $Index += 2; continue }
            if ($Character -eq [char]34) { $InString = $false }
            if ($Character -eq "`n") { [void]$Builder.Append($Character) }
            else { [void]$Builder.Append(' ') }
            $Index++; continue
        }
        if ($Pair -eq '--') { $LineComment = $true; [void]$Builder.Append('  '); $Index += 2; continue }
        if ($Pair -eq '/-') { $Depth = 1; [void]$Builder.Append('  '); $Index += 2; continue }
        if ($Character -eq [char]34) { $InString = $true; [void]$Builder.Append(' '); $Index++; continue }
        [void]$Builder.Append($Character)
        $Index++
    }
    return $Builder.ToString()
}

function Invoke-CheckedLean {
    param([string] $Module, [string] $Source, [string] $Output, [bool] $IsNew)
    $SourceText = Get-Content -LiteralPath $Source -Raw
    $CodeText = Get-LeanCode $SourceText
    $Forbidden = [regex]::Matches($CodeText, '\b(sorry|admit|axiom|native_decide)\b')
    if ($Forbidden.Count -ne 0) { throw "Forbidden source token in $Source" }
    $HashBefore = (Get-FileHash -Algorithm SHA256 -LiteralPath $Source).Hash.ToLowerInvariant()
    $LogPath = Join-Path $Logs "$Module.log"
    $Clock = [System.Diagnostics.Stopwatch]::StartNew()
    $RawOutput = & $Compiler '-o' $Output $Source 2>&1
    $ExitCode = $LASTEXITCODE
    $Clock.Stop()
    $LogText = ($RawOutput | ForEach-Object { [string]$_ }) -join "`n"
    [System.IO.File]::WriteAllText($LogPath, $LogText + "`n", $Utf8)
    $HashAfter = (Get-FileHash -Algorithm SHA256 -LiteralPath $Source).Hash.ToLowerInvariant()
    if ($HashBefore -ne $HashAfter) { throw "Source changed during replay: $Source" }
    $AxiomRecords = [System.Collections.Generic.List[object]]::new()
    foreach ($Match in [regex]::Matches($LogText, "'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")) {
        $Axioms = @($Match.Groups[2].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ })
        $AxiomRecords.Add([ordered]@{ theorem = $Match.Groups[1].Value; axioms = $Axioms })
        foreach ($Axiom in $Axioms) {
            if ($ApprovedAxioms -notcontains $Axiom) { $AuditFailures.Add("$Module`: unexpected axiom $Axiom") }
        }
    }
    if ($IsNew) {
        $TheoremCount = [regex]::Matches($CodeText, '(?m)^(?:@\[[^\r\n]*\]\s*)?(?:private\s+)?theorem\s+').Count
        if ($TheoremCount -ne $AxiomRecords.Count) {
            $AuditFailures.Add("$Module`: theorem count $TheoremCount differs from audited count $($AxiomRecords.Count)")
        }
    }
    $Record = [ordered]@{
        module = $Module; source = $Source; source_sha256 = $HashAfter
        olean = $Output; exit_code = $ExitCode; elapsed_seconds = $Clock.Elapsed.TotalSeconds
        log = $LogPath; log_sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $LogPath).Hash.ToLowerInvariant()
        forbidden_source_tokens = $Forbidden.Count; theorem_axioms = @($AxiomRecords.ToArray())
        source_recompiled = $true
    }
    if ($ExitCode -eq 0 -and (Test-Path -LiteralPath $Output)) {
        $Record['olean_sha256'] = (Get-FileHash -Algorithm SHA256 -LiteralPath $Output).Hash.ToLowerInvariant()
    }
    $Receipts.Add($Record)
    Write-Output "$Module`: Lean exit=$ExitCode, audited theorems=$($AxiomRecords.Count), seconds=$([math]::Round($Clock.Elapsed.TotalSeconds, 3))"
    if ($ExitCode -ne 0) { throw "Lean failed for $Module; read $LogPath" }
}

try {
    foreach ($Module in @('GoldbachBridge', 'GoldbachArithmetic') + $ExtraDependencies) {
        $SourceOriginal = Join-Path $DependencySources "$Module.lean"
        $SourceCopy = Join-Path $Dependencies "$Module.lean"
        Copy-Item -LiteralPath $SourceOriginal -Destination $SourceCopy -Force
        Invoke-CheckedLean -Module $Module -Source $SourceCopy -Output (Join-Path $Dependencies "$Module.olean") -IsNew $false
    }
    foreach ($Module in $NewModules) {
        if ($Module -notmatch '^[A-Za-z][A-Za-z0-9_]*$') { throw "Invalid module name: $Module" }
        Invoke-CheckedLean -Module $Module -Source (Join-Path $TaskRoot "lean\$Module.lean") -Output (Join-Path $Outputs "$Module.olean") -IsNew $true
    }
    if ($AuditFailures.Count -ne 0) { throw ($AuditFailures -join "`n") }
    $Receipt = [ordered]@{
        status = 'COMPILED_AND_AXIOMS_AUDITED'
        victory = $false
        victory_note = 'A compiler audit establishes these finite identities; analytic parity control is a separate semantic obligation.'
        recorded_at_utc = [DateTime]::UtcNow.ToString('o')
        compiler = $Compiler; compiler_version = $Version
        compiler_sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $Compiler).Hash.ToLowerInvariant()
        lean_path = $env:LEAN_PATH; package_cache_reused = $Packages
        new_or_goldbach_dependency_olean_reused = $false
        numerical_gate = [ordered]@{
            path = $NumericalPath; status = $Numerical.status; N = $Numerical.N
            sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $NumericalPath).Hash.ToLowerInvariant()
        }
        supplemental_numerical_gates = @($SupplementalGates.ToArray())
        approved_standard_axioms = $ApprovedAxioms
        modules = @($Receipts.ToArray()); axiom_audit_failures = @($AuditFailures.ToArray())
    }
    [System.IO.File]::WriteAllText((Join-Path $TaskRoot 'judge_receipt.json'), ($Receipt | ConvertTo-Json -Depth 12) + "`n", $Utf8)
}
finally {
    $env:LEAN_PATH = $PreviousLeanPath
}
