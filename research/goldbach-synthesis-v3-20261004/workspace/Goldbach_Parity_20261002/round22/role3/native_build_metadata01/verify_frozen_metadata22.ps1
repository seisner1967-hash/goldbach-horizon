param()
$ErrorActionPreference='Stop'
$TaskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$TaskHere=Split-Path -Parent $MyInvocation.MyCommand.Path
$ResultPath=Join-Path $TaskHere 'frozen6348_conservation22.json'
if(Test-Path -LiteralPath $ResultPath){throw 'Immutable observation already exists'}
$Controls=@(
 [ordered]@{path=Join-Path $TaskBase 'round22\role4\circle_native_revision02\closure_snapshot22.json';sha256='12bd8ab8c067e4881b837689ce705e7f029826b20482b85fbc6a6d18e3717e06';count=6332},
 [ordered]@{path=Join-Path $TaskBase 'round22\role4\circle_native_revision02\source_handoff22.json';sha256='889d4e221911bdfe75104361d62f36accf3770a17f48f29d84a9ba8d1952da88';count=12},
 [ordered]@{path=Join-Path $TaskBase 'round22\role4\circle_native_build_source01\source_handoff22.json';sha256='12a414e0b96d068f65f0130474683bd3db27223ad9fc76f4f2b09c5946d3b8d1';count=5}
)
$Map=@{}
$Duplicates=0
foreach($Control in $Controls){
 if((Get-FileHash -LiteralPath $Control.path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $Control.sha256){throw ('Control hash mismatch: '+$Control.path)}
 $Document=Get-Content -LiteralPath $Control.path -Raw | ConvertFrom-Json
 if(@($Document.bindings).Count -ne $Control.count){throw 'Control binding count mismatch'}
 foreach($Binding in $Document.bindings){
  $Key=[IO.Path]::GetFullPath($Binding.path).ToLowerInvariant()
  if($Map.ContainsKey($Key)){
   if($Map[$Key].bytes -ne $Binding.bytes -or $Map[$Key].sha256 -ne $Binding.sha256){throw ('Conflicting binding: '+$Binding.path)}
   $Map[$Key].capture=[bool]($Map[$Key].capture -or $Binding.capture)
   $Duplicates++
  }else{$Map[$Key]=[ordered]@{path=[IO.Path]::GetFullPath($Binding.path);bytes=[long]$Binding.bytes;sha256=$Binding.sha256;capture=[bool]$Binding.capture}}
 }
}
if($Map.Count -ne 6348){throw 'Unexpected current frozen union count'}
$Rows=[Collections.Generic.List[object]]::new()
$Failures=[Collections.Generic.List[string]]::new()
foreach($Key in @($Map.Keys | Sort-Object)){
 $Binding=$Map[$Key]
 if(-not(Test-Path -LiteralPath $Binding.path -PathType Leaf)){$Failures.Add(('Missing: '+$Binding.path));continue}
 $Item=Get-Item -LiteralPath $Binding.path
 $Hash=(Get-FileHash -LiteralPath $Binding.path -Algorithm SHA256).Hash.ToLowerInvariant()
 $Intact=($Item.Length -eq $Binding.bytes -and $Hash -eq $Binding.sha256)
 if(-not$Intact){$Failures.Add(('Changed: '+$Binding.path))}
 $Rows.Add([ordered]@{path=$Binding.path;bytes=$Item.Length;sha256=$Hash;intact=$Intact;capture=$Binding.capture})
}
$RegistryPath=Join-Path $TaskBase 'round22\previous_artifacts_sha256.json'
$RegistryHash='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
if((Get-FileHash -LiteralPath $RegistryPath -Algorithm SHA256).Hash.ToLowerInvariant() -ne $RegistryHash){throw 'Registry changed'}
$Registry=Get-Content -LiteralPath $RegistryPath -Raw | ConvertFrom-Json
$ArchiveRows=[Collections.Generic.List[object]]::new()
foreach($Property in $Registry.sha256.PSObject.Properties){
 $ArchivePath=Join-Path $TaskBase $Property.Name
 if(-not(Test-Path -LiteralPath $ArchivePath -PathType Leaf)){$Failures.Add(('Missing archive: '+$ArchivePath));continue}
 $Hash=(Get-FileHash -LiteralPath $ArchivePath -Algorithm SHA256).Hash.ToLowerInvariant()
 $Intact=($Hash -eq $Property.Value)
 if(-not$Intact){$Failures.Add(('Changed archive: '+$ArchivePath))}
 $ArchiveRows.Add([ordered]@{relative_path=$Property.Name;sha256=$Hash;intact=$Intact})
}
if($ArchiveRows.Count -ne 3089){$Failures.Add('Archive count mismatch')}
$RuntimePrefix='C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\'
$RuntimeCount=@($Rows.ToArray() | Where-Object {$_.path.StartsWith($RuntimePrefix,[StringComparison]::OrdinalIgnoreCase)}).Count
$CanonicalPython=Join-Path $RuntimePrefix 'python.exe'
$Result=[ordered]@{
 schema='ROUND22_FROZEN_BUILD01_UNION_METADATA_OBSERVATION';status='METADATA_ONLY_PENDING_REVISED_SOURCE_AND_REVIEW';observed_utc=[DateTime]::UtcNow.ToString('o');
 actor='ROLE6';controls=$Controls;control_binding_counts=@(6332,12,5);duplicate_occurrences=$Duplicates;unique_union_count=$Map.Count;verified_binding_count=$Rows.Count;
 python_runtime_file_count=$RuntimeCount;canonical_python_sha256=(Get-FileHash -LiteralPath $CanonicalPython -Algorithm SHA256).Hash.ToLowerInvariant();
 protected_registry_path=$RegistryPath;protected_registry_sha256=$RegistryHash;protected_archive_count=$ArchiveRows.Count;
 all_binding_and_archive_bytes_unchanged=($Failures.Count -eq 0);failures=@($Failures.ToArray());
 compiler_invocations=0;candidate_invocations=0;math_source_imports_or_parses=0;build_metadata_ready=$false;
 source_build01_cwd_mismatch_pending_distinct_source02=$true;independent_final_source_review_received=$false;
 bindings=@($Rows.ToArray());archives=@($ArchiveRows.ToArray())
}
[IO.File]::WriteAllText($ResultPath,($Result | ConvertTo-Json -Depth 10),[Text.UTF8Encoding]::new($false))
[ordered]@{path=$ResultPath;sha256=(Get-FileHash -LiteralPath $ResultPath -Algorithm SHA256).Hash.ToLowerInvariant();bytes=(Get-Item -LiteralPath $ResultPath).Length;union_count=$Map.Count;runtime_count=$RuntimeCount;archive_count=$ArchiveRows.Count;failures=@($Failures.ToArray());build_prepared=$false;compiler_invocations=0;candidate_invocations=0} | ConvertTo-Json -Depth 4
