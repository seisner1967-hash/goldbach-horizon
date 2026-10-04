param()
$ErrorActionPreference = 'Stop'
$TaskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$TaskHere = Split-Path -Parent $MyInvocation.MyCommand.Path
$SnapshotPath = Join-Path $TaskBase 'round22\role4\circle_native_revision02\closure_snapshot22.json'
$SnapshotExpected = '12bd8ab8c067e4881b837689ce705e7f029826b20482b85fbc6a6d18e3717e06'
$ResultPath = Join-Path $TaskHere 'pe_static_import_observation22.json'
if (Test-Path -LiteralPath $ResultPath) { throw 'Immutable result already exists' }
if ((Get-FileHash -LiteralPath $SnapshotPath -Algorithm SHA256).Hash.ToLowerInvariant() -ne $SnapshotExpected) { throw 'Snapshot hash mismatch' }
$Snapshot = Get-Content -LiteralPath $SnapshotPath -Raw | ConvertFrom-Json
$Bound = @{}
foreach ($Binding in $Snapshot.bindings) {
  $Key = [IO.Path]::GetFullPath($Binding.path).ToLowerInvariant()
  if ($Bound.ContainsKey($Key)) { throw ('Duplicate snapshot path: '+$Key) }
  $Bound[$Key] = $Binding
}
if ($Bound.Count -ne 6332) { throw 'Unexpected binding count' }

function Read-PeNode([string]$TaskPath) {
  # Binary format parsing only. No Add-Type, external parser, LoadLibrary, or execution.
  $script:PeData = [IO.File]::ReadAllBytes($TaskPath)
  function Range-Check([long]$Off, [long]$Length) {
    if ($Off -lt 0 -or $Length -lt 0 -or $Off + $Length -gt $script:PeData.LongLength) { throw 'PE byte range outside file' }
  }
  function U16([long]$Off) { Range-Check $Off 2; return [BitConverter]::ToUInt16($script:PeData,[int]$Off) }
  function U32([long]$Off) { Range-Check $Off 4; return [BitConverter]::ToUInt32($script:PeData,[int]$Off) }
  function U64([long]$Off) { Range-Check $Off 8; return [BitConverter]::ToUInt64($script:PeData,[int]$Off) }
  function Ascii-Z([long]$Off) {
    Range-Check $Off 1
    $End = $Off
    while ($End -lt $script:PeData.LongLength -and $End - $Off -lt 4096 -and $script:PeData[[int]$End] -ne 0) { $End++ }
    if ($End -ge $script:PeData.LongLength -or $End - $Off -ge 4096) { throw 'Unterminated PE name' }
    return [Text.Encoding]::ASCII.GetString($script:PeData,[int]$Off,[int]($End-$Off))
  }
  function Rva-Offset([long]$Rva) {
    if ($Rva -lt $script:PeHeaders) { Range-Check $Rva 1; return $Rva }
    foreach ($Section in $script:PeSections) {
      $Span = [Math]::Max([long]$Section.virtual_size,[long]$Section.raw_size)
      if ($Rva -ge $Section.virtual_address -and $Rva -lt $Section.virtual_address+$Span) {
        $Delta = $Rva-$Section.virtual_address
        if ($Delta -ge $Section.raw_size) { throw 'RVA points to unbacked section bytes' }
        $Off = $Section.raw_pointer+$Delta
        Range-Check $Off 1
        return $Off
      }
    }
    throw ('Unmapped RVA: '+$Rva)
  }
  if ((U16 0) -ne 0x5a4d) { throw 'Missing MZ signature' }
  $Pe = [long](U32 0x3c)
  if ((U32 $Pe) -ne 0x4550) { throw 'Missing PE signature' }
  $Machine = U16 ($Pe+4)
  $Count = U16 ($Pe+6)
  $OptionalSize = U16 ($Pe+20)
  $Optional = $Pe+24
  Range-Check $Optional $OptionalSize
  $Magic = U16 $Optional
  if ($Magic -eq 0x20b) { $Directory = $Optional+112; $DirectoryCount = U32 ($Optional+108); $ImageBase = U64 ($Optional+24) }
  elseif ($Magic -eq 0x10b) { $Directory = $Optional+96; $DirectoryCount = U32 ($Optional+92); $ImageBase = [ulong](U32 ($Optional+28)) }
  else { throw 'Unsupported optional-header magic' }
  $script:PeHeaders = [long](U32 ($Optional+60))
  $script:PeSections = @()
  $SectionOffset = $Optional+$OptionalSize
  for ($Index=0; $Index -lt $Count; $Index++) {
    $Off = $SectionOffset+40*$Index
    Range-Check $Off 40
    $script:PeSections += [ordered]@{virtual_size=[long](U32 ($Off+8));virtual_address=[long](U32 ($Off+12));raw_size=[long](U32 ($Off+16));raw_pointer=[long](U32 ($Off+20))}
  }
  $Normal = [Collections.Generic.List[string]]::new()
  $Delayed = [Collections.Generic.List[string]]::new()
  if ($DirectoryCount -gt 1) {
    $ImportRva = [long](U32 ($Directory+8))
    $ImportSize = [long](U32 ($Directory+12))
    if ($ImportRva -ne 0) {
      if ($ImportSize -lt 20) { throw 'Invalid import directory size' }
      $Terminated = $false
      for ($Index=0; $Index -lt [Math]::Floor($ImportSize/20); $Index++) {
        $Off = Rva-Offset ($ImportRva+20*$Index)
        Range-Check $Off 20
        $Values = @((U32 $Off),(U32 ($Off+4)),(U32 ($Off+8)),(U32 ($Off+12)),(U32 ($Off+16)))
        if (($Values | Measure-Object -Sum).Sum -eq 0) { $Terminated=$true; break }
        if ($Values[3] -eq 0) { throw 'Import descriptor without DLL name' }
        $Normal.Add((Ascii-Z (Rva-Offset ([long]$Values[3]))))
      }
      if (-not $Terminated) { throw 'Import descriptors not terminated in declared directory' }
    }
  }
  if ($DirectoryCount -gt 13) {
    $DelayRva = [long](U32 ($Directory+13*8))
    $DelaySize = [long](U32 ($Directory+13*8+4))
    if ($DelayRva -ne 0) {
      if ($DelaySize -lt 32) { throw 'Invalid delay directory size' }
      $Terminated = $false
      for ($Index=0; $Index -lt [Math]::Floor($DelaySize/32); $Index++) {
        $Off = Rva-Offset ($DelayRva+32*$Index)
        Range-Check $Off 32
        $Values = @(0..7 | ForEach-Object { U32 ($Off+4*$_) })
        if (($Values | Measure-Object -Sum).Sum -eq 0) { $Terminated=$true; break }
        $NameRva = [long]$Values[1]
        if (($Values[0] -band 1) -eq 0) {
          if ([ulong]$NameRva -lt $ImageBase) { throw 'Delay VA below image base' }
          $NameRva = [long]([ulong]$NameRva-$ImageBase)
        }
        $Delayed.Add((Ascii-Z (Rva-Offset $NameRva)))
      }
      if (-not $Terminated) { throw 'Delay descriptors not terminated in declared directory' }
    }
  }
  return [ordered]@{path=$TaskPath;machine=$Machine;optional_header_magic=$Magic;section_count=$Count;normal_imports=@($Normal.ToArray());delay_imports=@($Delayed.ToArray())}
}

$Seeds = @(
 'C:\msys64\ucrt64\bin\g++.exe','C:\msys64\ucrt64\bin\gcc.exe',
 'C:\msys64\ucrt64\bin\as.exe','C:\msys64\ucrt64\bin\ld.exe',
 'C:\msys64\ucrt64\lib\gcc\x86_64-w64-mingw32\15.2.0\cc1plus.exe',
 'C:\msys64\ucrt64\lib\gcc\x86_64-w64-mingw32\15.2.0\collect2.exe',
 'C:\msys64\ucrt64\lib\gcc\x86_64-w64-mingw32\15.2.0\lto-wrapper.exe',
 'C:\msys64\ucrt64\lib\gcc\x86_64-w64-mingw32\15.2.0\lto1.exe',
 'C:\msys64\ucrt64\lib\gcc\x86_64-w64-mingw32\15.2.0\plugin\gengtype.exe',
 'C:\msys64\ucrt64\lib\bfd-plugins\liblto_plugin.dll',
 'C:\msys64\ucrt64\lib\gcc\x86_64-w64-mingw32\15.2.0\liblto_plugin.dll'
)
$LocalDlls = @($Snapshot.bindings | Where-Object {$_.path -match '^C:\\msys64\\ucrt64\\bin\\[^\\]+\.dll$'} | ForEach-Object {$_.path})
$Queue = [Collections.Generic.Queue[string]]::new()
foreach ($TaskPath in @($Seeds)+@($LocalDlls)) { $Queue.Enqueue([IO.Path]::GetFullPath($TaskPath)) }
$Seen = @{}
$Nodes = [Collections.Generic.List[object]]::new()
$Edges = [Collections.Generic.List[object]]::new()
$Gaps = [Collections.Generic.List[string]]::new()
while ($Queue.Count -gt 0) {
  $TaskPath = $Queue.Dequeue()
  $Key = $TaskPath.ToLowerInvariant()
  if ($Seen.ContainsKey($Key)) { continue }
  $Seen[$Key]=$true
  try {
    if (-not $Bound.ContainsKey($Key)) { throw ('PE image absent from frozen snapshot: '+$TaskPath) }
    $Binding = $Bound[$Key]
    $Item = Get-Item -LiteralPath $TaskPath
    $Hash = (Get-FileHash -LiteralPath $TaskPath -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Item.Length -ne $Binding.bytes -or $Hash -ne $Binding.sha256) { throw ('Image hash mismatch: '+$TaskPath) }
    $Node = Read-PeNode $TaskPath
    $Node.bytes=$Item.Length
    $Node.sha256=$Hash
    $Nodes.Add($Node)
    foreach ($Kind in @('normal_imports','delay_imports')) {
      foreach ($Name in $Node[$Kind]) {
        if ($Name -ne [IO.Path]::GetFileName($Name)) { throw ('Non-bare import name: '+$Name) }
        $ReferenceCandidate = Join-Path ([IO.Path]::GetDirectoryName($TaskPath)) $Name
        $UcrtCandidate = Join-Path 'C:\msys64\ucrt64\bin' $Name
        $Selected = $null
        foreach ($Candidate in @($ReferenceCandidate,$UcrtCandidate)) {
          $CandidateKey = [IO.Path]::GetFullPath($Candidate).ToLowerInvariant()
          if ($Bound.ContainsKey($CandidateKey)) { $Selected=$Bound[$CandidateKey].path; break }
        }
        if ($Selected) {
          $Edges.Add([ordered]@{from=$TaskPath;kind=$Kind;dll_name=$Name;classification='DECLARED_LOCAL_IMPORT_BOUND_CANDIDATE';candidate=$Selected;actual_windows_loader_resolution_verified=$false})
          $Queue.Enqueue($Selected)
        } elseif ($Name -match '^(api-ms-win-|ext-ms-win-)' -or (Test-Path -LiteralPath (Join-Path 'C:\Windows\System32' $Name))) {
          $Edges.Add([ordered]@{from=$TaskPath;kind=$Kind;dll_name=$Name;classification='WINDOWS_OR_API_SET_TRUST_BOUNDARY';candidate=$null;os_transitive_closure_verified=$false})
        } else {
          $Edges.Add([ordered]@{from=$TaskPath;kind=$Kind;dll_name=$Name;classification='UNRESOLVED_DECLARED_IMPORT';candidate=$null})
          $Gaps.Add(('Unresolved declared import '+$Name+' from '+$TaskPath))
        }
      }
    }
  } catch { $Gaps.Add($_.Exception.Message) }
}
$Result = [ordered]@{
 schema='ROUND22_PE_BYTE_STATIC_IMPORT_OBSERVATION';status='STATIC_BYTES_OBSERVED_RUNTIME_CLOSURE_OPEN';actor='ROLE6';
 observed_utc=[DateTime]::UtcNow.ToString('o');snapshot_path=$SnapshotPath;snapshot_sha256=$SnapshotExpected;snapshot_binding_count=$Bound.Count;
 seed_count=$Seeds.Count;all_bound_bin_dll_seed_count=$LocalDlls.Count;pe_image_count=$Nodes.Count;edge_count=$Edges.Count;
 all_observed_declared_non_OS_import_candidates_bound=($Gaps.Count -eq 0);parser_or_declared_import_gaps=@($Gaps.ToArray());
 windows_loader_resolution_verified=$false;dynamic_LoadLibrary_closure_verified=$false;gcc_default_specs_or_subprocess_selection_verified=$false;
 full_OS_transitive_import_closure_verified=$false;compiler_invocations=0;candidate_invocations=0;external_binary_analysis_invocations=0;
 nodes=@($Nodes.ToArray());edges=@($Edges.ToArray());
 explicit_scope='Normal and delay PE descriptor names from frozen compiler/helper/plugin images and all frozen UCRT bin DLLs. Non-OS candidate paths are bound and recursively parsed. This is not an observed loader trace, complete OS closure, GCC specs proof, or build result.'
}
$Json = $Result | ConvertTo-Json -Depth 12
[IO.File]::WriteAllText($ResultPath,$Json,[Text.UTF8Encoding]::new($false))
[ordered]@{result_path=$ResultPath;result_sha256=(Get-FileHash -LiteralPath $ResultPath -Algorithm SHA256).Hash.ToLowerInvariant();bytes=(Get-Item -LiteralPath $ResultPath).Length;pe_images=$Nodes.Count;edges=$Edges.Count;gaps=@($Gaps.ToArray());compiler_invocations=0;candidate_invocations=0} | ConvertTo-Json -Depth 4
