<#
Loop-LakeBuild.ps1 — Phase 0 tool for the G26 sorry-cleanup track.

Runs `lake build` over a list of Lake targets, with a guard that refuses
to proceed when changes are present (staged or in the working tree) on
files whose basename is in the forbidden list below.

The forbidden list extends the original 3 build-system files with the
5 CD12 / Mertens-Landau Lean files: those belong to a separate Lean
project (F-MT-004 / M_short_F) and must not be touched from this track.

Matching is by basename (Split-Path -Leaf) because `git diff --name-only`
returns paths relative to the repo root (e.g. Goldbach/M3cTerminalCD12Interval.lean),
and a strict `-contains` against bare filenames would miss them.

Usage:
  # default: assert + lake build Goldbach
  pwsh -NoProfile -File tools\g26_cleanup\Loop-LakeBuild.ps1

  # assertion only (no build)
  pwsh -NoProfile -File tools\g26_cleanup\Loop-LakeBuild.ps1 -AssertOnly

  # alternate targets
  pwsh -NoProfile -File tools\g26_cleanup\Loop-LakeBuild.ps1 -Targets @('Goldbach')

  # dot-source to call the functions from tests:
  . .\tools\g26_cleanup\Loop-LakeBuild.ps1 -NoRun
  Assert-NoForbiddenChanges
#>

[CmdletBinding()]
param(
    [string[]]$Targets = @('Goldbach'),
    [int]$MaxIterations = 1,
    [switch]$AssertOnly,
    [switch]$NoRun
)

$ErrorActionPreference = 'Stop'

$script:Forbidden = @(
    'lakefile.lean',
    'lean-toolchain',
    'lake-manifest.json',
    'M3cTerminalCD12Interval.lean',
    'M3cTerminalCD12AbelInterval.lean',
    'M3cTerminalCD12Conditional.lean',
    'M3cTerminalCD12PublicV022.lean',
    'MertensLandauNOverPhiKernelBound.lean'
)

function Get-ChangedPaths {
    [CmdletBinding()]
    param()
    $staged  = @(& git diff --cached --name-only)
    $working = @(& git diff --name-only HEAD)
    $all = @()
    if ($staged)  { $all += $staged }
    if ($working) { $all += $working }
    $all | Where-Object { $_ -and $_.Trim() -ne '' } | Sort-Object -Unique
}

function Test-IsForbiddenPath {
    [CmdletBinding()]
    param([Parameter(Mandatory)][string]$Path)
    $leaf = Split-Path -Leaf $Path
    return ($script:Forbidden -contains $leaf)
}

function Assert-NoForbiddenChanges {
    [CmdletBinding()]
    param()
    $hits = @()
    foreach ($p in (Get-ChangedPaths)) {
        if (Test-IsForbiddenPath -Path $p) { $hits += $p }
    }
    if ($hits.Count -gt 0) {
        $msg = "Forbidden file changes detected (CD12/build-system off-limits):`n - " + ($hits -join "`n - ")
        throw $msg
    }
    Write-Verbose 'Assert-NoForbiddenChanges: clean.'
}

function Invoke-LakeBuildOnce {
    [CmdletBinding()]
    param([Parameter(Mandatory)][string]$Target)
    Write-Host "[Loop-LakeBuild] lake build $Target"
    & lake build $Target
    return $LASTEXITCODE
}

function Invoke-LoopLakeBuild {
    [CmdletBinding()]
    param(
        [string[]]$Targets,
        [int]$MaxIterations = 1
    )
    for ($i = 1; $i -le $MaxIterations; $i++) {
        Write-Host "[Loop-LakeBuild] iteration $i / $MaxIterations"
        Assert-NoForbiddenChanges
        foreach ($t in $Targets) {
            $code = Invoke-LakeBuildOnce -Target $t
            if ($code -ne 0) {
                throw "lake build $t failed with exit code $code (iteration $i)"
            }
        }
    }
}

if (-not $NoRun) {
    if ($AssertOnly) {
        Assert-NoForbiddenChanges
        Write-Host '[Loop-LakeBuild] Assert-NoForbiddenChanges: OK.'
    } else {
        Invoke-LoopLakeBuild -Targets $Targets -MaxIterations $MaxIterations
    }
}
