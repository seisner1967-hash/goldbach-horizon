$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$taskRole = Join-Path $taskBase 'round22\role3\h1_psi\revision04'
$taskCache = 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages'
$taskTool = 'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0'
$taskPython = 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$taskModules = @('GammaPsiBetaLimit22','GammaPsiIntegral22','GammaPsiDuplication22')
$taskCounts = @(23,10,2)
$taskPackages = @('aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq')
$taskUtf8 = [Text.UTF8Encoding]::new($false)

function TaskSha([string] $p) { (Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash.ToLower() }
function TaskWriteNew([string] $p, $obj) {
  if(Test-Path -LiteralPath $p){throw "refusing to replace frozen preparation: $p"}
  $s = ($obj | ConvertTo-Json -Depth 25) + "`n"
  [IO.File]::WriteAllText($p,$s,$taskUtf8)
}
function TaskBinding([string] $p, [string] $scope) {
  [ordered]@{path=$p;sha256=(TaskSha $p);bytes=(Get-Item -LiteralPath $p).Length;read_scope=$scope}
}
function TaskHeader([string] $text) {
  $i=0; $names=[Collections.Generic.List[string]]::new(); $prelude=$false
  while($i -lt $text.Length){
    if([char]::IsWhiteSpace($text[$i])){$i++;continue}
    if($i+1 -lt $text.Length -and $text.Substring($i,2) -eq '--'){
      $j=$text.IndexOf("`n",$i);if($j -lt 0){break};$i=$j+1;continue
    }
    if($i+1 -lt $text.Length -and $text.Substring($i,2) -eq '/-'){
      $depth=1;$i+=2
      while($depth -gt 0 -and $i -lt $text.Length){
        if($i+1 -lt $text.Length -and $text.Substring($i,2) -eq '/-'){$depth++;$i+=2}
        elseif($i+1 -lt $text.Length -and $text.Substring($i,2) -eq '-/'){$depth--;$i+=2}
        else{$i++}
      }
      if($depth -ne 0){throw 'unclosed header comment'};continue
    }
    $pre=[regex]::Match($text.Substring($i),'\Aprelude\b')
    if($pre.Success){$prelude=$true;$i+=$pre.Length;continue}
    $hit=[regex]::Match($text.Substring($i),'\Aimport\b[^\r\n]*')
    if(-not $hit.Success){break}
    $line=($hit.Value -replace '--.*$','').Substring(6).Trim()
    foreach($n in ($line -split '\s+')){
      if($n -notmatch '^[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*$'){throw "unrecognized import token $n"}
      $names.Add($n)
    }
    $i+=$hit.Length
  }
  if(-not $prelude){$names.Add('Init')}
  [ordered]@{imports=@($names.ToArray() | Select-Object -Unique);prelude=$prelude}
}

$taskFullRole=[IO.Path]::GetFullPath($taskRole)
if(-not $taskFullRole.StartsWith([IO.Path]::GetFullPath($taskBase)+[IO.Path]::DirectorySeparatorChar)){
  throw 'ownership directory escaped the workspace'
}
$taskFinal=Join-Path $taskRole 'source_final'
if(Test-Path -LiteralPath $taskFinal){throw 'source_final already exists; use a separate revision'}
New-Item -ItemType Directory -Path $taskFinal | Out-Null
$catalog=@();$sourceBindings=@();$seeds=[Collections.Generic.Queue[string]]::new()
for($idx=0;$idx -lt $taskModules.Count;$idx++){
  $name=$taskModules[$idx];$original=Join-Path $taskRole ($name+'.lean');$final=Join-Path $taskFinal ($name+'.lean')
  Copy-Item -LiteralPath $original -Destination $final
  if((TaskSha $original) -ne (TaskSha $final)){throw 'source copy hash mismatch'}
  $s=[IO.File]::ReadAllText($final)
  if($s -match '\b(sorry|admit|axiom|unsafe|native_decide)\b'){throw 'forbidden proof token'}
  $decls=@([regex]::Matches($s,'(?m)^(?:def|theorem)\s+([A-Za-z_0-9]+)') | ForEach-Object {'GoldbachContinuous22.'+$_.Groups[1].Value})
  $prints=@([regex]::Matches($s,'(?m)^#print axioms ([A-Za-z_.0-9]+)\s*$') | ForEach-Object {$_.Groups[1].Value})
  if($decls.Count -ne $taskCounts[$idx] -or $prints.Count -ne $decls.Count -or
      (($decls | Sort-Object) -join '|') -ne (($prints | Sort-Object) -join '|')){throw 'qualified axiom catalog mismatch'}
  $header=TaskHeader $s
  foreach($n in $header.imports){if($n -notin $taskModules -and $n -ne 'GammaPsiCore22'){$seeds.Enqueue($n)}}
  $catalog+=[ordered]@{module=$name;path=$final;sha256=(TaskSha $final);declaration_count=$decls.Count;declarations=$decls;imports=$header.imports}
  $sourceBindings+=(TaskBinding $original 'AUTHOR_FULL_FINAL_SOURCE');$sourceBindings+=(TaskBinding $final 'BYTE_IDENTICAL_FROZEN_COPY')
}

$taskCoreSource=Join-Path $taskBase 'round22\role3\h1_psi\revision03\source_final\GammaPsiCore22.lean'
$taskCoreOlean=Join-Path $taskBase 'round22\role3\h1_psi\revision03\psi_batch03_attempt01\GammaPsiCore22.olean'
if((TaskSha $taskCoreSource) -ne '450962be9526866fa0ffebc39ef29a819d94b57a90000291337550e9f4dc7284' -or
  (TaskSha $taskCoreOlean) -ne '15f66830eab0ee8e192d4fffee9518abd001b3167c28c527881bbdaabefb9a4b'){throw 'readonly Core actual PASS bindings changed'}
foreach($n in (TaskHeader ([IO.File]::ReadAllText($taskCoreSource))).imports){$seeds.Enqueue($n)}
$sourceBindings+=(TaskBinding $taskCoreSource 'READONLY_ACTUAL_CORE_AUX_PASS_SOURCE')
$sourceBindings+=(TaskBinding $taskCoreOlean 'READONLY_ACTUAL_CORE_OLEAN_HASH_ONLY')
$roots=@();$libraries=@()
foreach($p in $taskPackages){
  $src=Join-Path $taskCache $p;$lib=Join-Path $src '.lake\build\lib'
  if(-not (Test-Path -LiteralPath $lib -PathType Container)){throw "cached library missing $lib"}
  $roots+=[ordered]@{source=$src;lib=$lib};$libraries+=$lib
}
$roots+=[ordered]@{source=(Join-Path $taskTool 'src\lean');lib=(Join-Path $taskTool 'lib\lean')}
$roots+=[ordered]@{source=(Join-Path $taskTool 'src\lean\lake');lib=(Join-Path $taskTool 'lib\lean')}
$seen=[Collections.Generic.HashSet[string]]::new();$artifacts=@();$nodes=@();$totBytes=[long]0
while($seeds.Count -gt 0){
  $n=$seeds.Dequeue();if(-not $seen.Add($n)){continue}
  $rel=($n -replace '\.','\');$found=@()
  foreach($r in $roots){$src=Join-Path $r.source ($rel+'.lean');if(Test-Path -LiteralPath $src){$found+=@{source=$src;olean=(Join-Path $r.lib ($rel+'.olean'))}}}
  if($found.Count -ne 1){throw "import source resolution is not unique: $n count=$($found.Count)"}
  $f=$found[0];if(-not (Test-Path -LiteralPath $f.olean)){throw "import olean missing: $n"}
  $header=TaskHeader ([IO.File]::ReadAllText($f.source))
  $nodes+=[ordered]@{module=$n;imports=$header.imports;prelude=$header.prelude;scope='PARSED_IMPORT_HEADER_ONLY_NOT_FULL_MATH_READ'}
  $a=TaskBinding $f.source 'PARSED_IMPORT_HEADER_ONLY_NOT_FULL_MATH_READ';$o=TaskBinding $f.olean 'READONLY_BYTE_HASH_ONLY'
  $artifacts+=$a;$artifacts+=$o;$totBytes+=$a.bytes+$o.bytes
  foreach($next in $header.imports){$seeds.Enqueue($next)}
}
$closurePath=Join-Path $taskRole 'psi_cache_closure22.json'
TaskWriteNew $closurePath ([ordered]@{schema='round22.psi.static_cache_closure.v1';generated_at=[DateTime]::UtcNow.ToString('o');
  scope='STATIC_IMPORT_HEADER_PARSE_AND_FILE_HASH_ONLY_NO_LEAN_PROBE';module_count=$nodes.Count;artifact_count=$artifacts.Count;
  bound_bytes=$totBytes;lean_path_libraries=$libraries;nodes=$nodes;artifacts=$artifacts})

$apiRel=@('NumberTheory\Harmonic\GammaDeriv.lean','Analysis\SpecialFunctions\Gamma\Beta.lean',
  'Analysis\SpecialFunctions\Pow\Real.lean','Analysis\SpecialFunctions\Pow\Deriv.lean','Analysis\SpecialFunctions\Pow\Continuity.lean',
  'Analysis\SpecialFunctions\Pow\Complex.lean','Analysis\Calculus\MeanValue.lean','Analysis\Calculus\Deriv\Basic.lean',
  'Analysis\Calculus\Deriv\Slope.lean','Analysis\Complex\RealDeriv.lean','Analysis\SpecificLimits\Basic.lean',
  'Analysis\SpecialFunctions\Integrals.lean','MeasureTheory\Integral\DominatedConvergence.lean',
  'MeasureTheory\Integral\IntervalIntegral.lean','MeasureTheory\Function\Jacobian.lean','MeasureTheory\Function\L1Space.lean',
  'MeasureTheory\Function\StronglyMeasurable\Basic.lean','Analysis\SpecialFunctions\Complex\Log.lean',
  'Analysis\SpecialFunctions\Log\Basic.lean','Analysis\SpecialFunctions\ExpDeriv.lean','Data\Complex\Exponential.lean',
  'MeasureTheory\Integral\IntegrableOn.lean','MeasureTheory\Integral\SetIntegral.lean','Topology\ContinuousOn.lean')
$apis=@();foreach($rel in $apiRel){$apis+=(TaskBinding (Join-Path (Join-Path $taskCache 'mathlib\Mathlib') $rel) 'TARGETED_API_SEE_read_scope22.md')}
$apiPath=Join-Path $taskRole 'psi_api_inventory22.json';TaskWriteNew $apiPath ([ordered]@{schema='round22.psi.API_BINDINGS.v1';read_scope_doc='read_scope22.md';APIs=$apis})
$inputs=$sourceBindings+$apis
foreach($rel in @('run_psi_batch_once22.py','prepare_psi_metadata22.ps1','preparation22.md','read_scope22.md','C5_next_obligations22.md','psi_api_inventory22.json','psi_cache_closure22.json')){
  $inputs+=(TaskBinding (Join-Path $taskRole $rel) 'PREPARATION_SOURCE_OR_METADATA_ONLY')
}
foreach($rel in @('round22\role4\h1_contour\psi_c5_subcontract22.md','round22\role1_bridge\contour_formula22.md','round22\judge5\h1_source_review01\review.md',
  'round22\judge5\batch02_sources\GammaPrerequisites22.lean','round22\judge5\batch02_attempt01\GammaPrerequisites22.olean','round22\judge5\batch02_attempt01\receipt.json',
  'round22\role6\thermal_h1\actual_component22\actual_receipt.json','round22\role6\thermal_h1\actual_component22\actual.log')){
  $inputs+=(TaskBinding (Join-Path $taskBase $rel) 'READONLY_REQUIRED_OR_ACTUAL_EVIDENCE')
}
foreach($rel in @('round22\role3\h1_psi\psi_source_manifest22.json','round22\role3\h1_psi\psi_prepared_receipt22.json',
  'round22\role3\h1_psi\psi_batch01_attempt01\receipt.json','round22\role3\h1_psi\psi_batch01_attempt01\GammaPsiCore22.log',
  'round22\role3\h1_psi\psi_batch01_attempt01\START.json','round22\role3\h1_psi\psi_batch01_attempt01\GammaPsiCore22_FIN.json',
  'round22\role3\h1_psi\psi_batch01_attempt01\PREEXEC.json','round22\role3\h1_psi\psi_batch01_attempt01\POSTEXEC.json')){
  $inputs+=(TaskBinding (Join-Path $taskBase $rel) 'READONLY_PREVIOUS_ACTUAL_FAILURE_NOT_REPLAYED')
}
$inputs+=(TaskBinding (Join-Path $taskRole 'failure01_diagnosis22.md') 'FULL_ACTUAL_FAILURE_DIAGNOSIS')
foreach($rel in @('round22\role3\h1_psi\revision02\psi_source_manifest22.json','round22\role3\h1_psi\revision02\psi_prepared_receipt22.json',
  'round22\role3\h1_psi\revision02\psi_batch02_attempt01\receipt.json','round22\role3\h1_psi\revision02\psi_batch02_attempt01\GammaPsiCore22.log',
  'round22\role3\h1_psi\revision02\psi_batch02_attempt01\START.json','round22\role3\h1_psi\revision02\psi_batch02_attempt01\GammaPsiCore22_FIN.json',
  'round22\role3\h1_psi\revision02\psi_batch02_attempt01\PREEXEC.json','round22\role3\h1_psi\revision02\psi_batch02_attempt01\POSTEXEC.json')){
  $inputs+=(TaskBinding (Join-Path $taskBase $rel) 'READONLY_SECOND_ACTUAL_FAILURE_NOT_REPLAYED')
}
$inputs+=(TaskBinding (Join-Path $taskRole 'failure02_diagnosis22.md') 'FULL_SECOND_ACTUAL_FAILURE_DIAGNOSIS')
foreach($rel in @('round22\role3\h1_psi\revision03\psi_source_manifest22.json','round22\role3\h1_psi\revision03\psi_prepared_receipt22.json',
  'round22\role3\h1_psi\revision03\psi_batch03_attempt01\receipt.json','round22\role3\h1_psi\revision03\psi_batch03_attempt01\GammaPsiBetaLimit22.log',
  'round22\role3\h1_psi\revision03\psi_batch03_attempt01\START.json','round22\role3\h1_psi\revision03\psi_batch03_attempt01\GammaPsiBetaLimit22_FIN.json',
  'round22\role3\h1_psi\revision03\psi_batch03_attempt01\PREEXEC.json','round22\role3\h1_psi\revision03\psi_batch03_attempt01\POSTEXEC.json')){
  $inputs+=(TaskBinding (Join-Path $taskBase $rel) 'READONLY_THIRD_ACTUAL_BATCH_NOT_REPLAYED')
}
$inputs+=(TaskBinding (Join-Path $taskRole 'failure03_diagnosis22.md') 'FULL_THIRD_ACTUAL_FAILURE_DIAGNOSIS')
$receiptPath=Join-Path $taskBase 'round22\role6\thermal_h1\actual_component22\actual_receipt.json'
$receipt=[IO.File]::ReadAllText($receiptPath)|ConvertFrom-Json
if((TaskSha $receiptPath) -ne '2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48' -or
  $receipt.exit_code -ne 1 -or $null -ne $receipt.result_sha256 -or -not $receipt.post_integrity){throw 'actual numeric technical failure observation changed'}
$gammaPath=Join-Path $taskBase 'round22\judge5\batch02_attempt01\GammaPrerequisites22.olean'
if((TaskSha $gammaPath) -ne 'fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477'){throw 'readonly Gamma olean changed'}
$pythonSHA=TaskSha $taskPython;$leanSHA=TaskSha (Join-Path $taskTool 'bin\lean.exe')
if($pythonSHA -ne '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c' -or
   $leanSHA -ne '8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'){throw 'runtime file binding changed'}
$manifestPath=Join-Path $taskRole 'psi_source_manifest22.json'
TaskWriteNew $manifestPath ([ordered]@{schema='round22.psi.author_prepared.v1';status='PREPARED_SOURCE_ONLY';node_id='15.3';role='ROLE3';
  generated_at=[DateTime]::UtcNow.ToString('o');modules=$taskModules;catalog=$catalog;declarations=35;inputs=$inputs;
  cache_closure_path=$closurePath;cache_closure_module_count=$nodes.Count;cache_closure_artifact_count=$artifacts.Count;
  lean_path_libraries=$libraries;python_path=$taskPython;python_sha256=$pythonSHA;lean_path=(Join-Path $taskTool 'bin\lean.exe');lean_sha256=$leanSHA;
  mathlib_commit_context='9837ca9d65d9de6fad1ef4381750ca688774e608';readonly_gamma_olean_sha256=(TaskSha $gammaPath);readonly_psi_core_olean_sha256=(TaskSha $taskCoreOlean);
  independent_SOURCE_review=[ordered]@{actor='ROLE4';captures=@('a84072','41e749');APIs=@('60792f','c40ad1');compile_invocations=0;scope='Original analytical proofs reviewed; Core real author PASS imported readonly; Beta actual four errors repaired in revision04; Dup numeral APIs corrected by cache source'};
  numeric_evidence=[ordered]@{receipt_path=$receiptPath;receipt_sha256=(TaskSha $receiptPath);numeric_PASS=$false;counterexample_established=$false;
    classification='TECHNICAL_EXPORT_FAILURE_NO_MATH_COUNTEREXAMPLE';exit_code=1;result_sha256=$null;post_integrity=$true;ROOT_clarification='numeric PASS is not a mathematical precondition for this independent auxiliary theorem'};
  compiler_gate_required=$true;compiler_invocations=0;C5_paid=$false;global_H1_paid=$false;D_N_paid=$false;victory=$false})
$preparedPath=Join-Path $taskRole 'psi_prepared_receipt22.json'
TaskWriteNew $preparedPath ([ordered]@{schema='round22.psi.metadata_receipt.v1';time=[DateTime]::UtcNow.ToString('o');status='PREPARED_SOURCE_ONLY';
  manifest_sha256=(TaskSha $manifestPath);launcher_sha256=(TaskSha (Join-Path $taskRole 'run_psi_batch_once22.py'));
  source_copy_hashes_verified=$true;declarations=35;qualified_axiom_prints=35;cached_import_closure_modules=$nodes.Count;
  cached_import_closure_artifacts=$artifacts.Count;numeric_PASS=$false;compiler_invocations=0;Python_math_invocations=0;API_probe_invocations=0;victory=$false})
[ordered]@{status='PREPARED_SOURCE_ONLY';manifest_sha256=(TaskSha $manifestPath);prepared_receipt_sha256=(TaskSha $preparedPath);
  input_count=$inputs.Count;module_count=$nodes.Count;artifact_count=$artifacts.Count;bound_cache_bytes=$totBytes;compiler_invocations=0}|ConvertTo-Json -Compress
