$ErrorActionPreference='Stop'
$taskBase='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$roleDir=Join-Path $taskBase 'round22\role3'
$utf8=[System.Text.UTF8Encoding]::new($false)
$catalogPath=Join-Path $roleDir 'G0_final_catalog.json'
$receiptPath=Join-Path $roleDir 'G0_final_receipt.json'
if((Test-Path -LiteralPath $catalogPath) -or (Test-Path -LiteralPath $receiptPath)){throw 'refusing final metadata replacement'}
function Hash-File($path){(Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()}
$specs=@(
  @{module='EpsteinKernel22';sourceDir='revision02';attempt='stage01_attempt02';manifest='source_manifest.json';logFull='41e1f7'},
  @{module='EpsteinFinite22';sourceDir='stage02\revision03';attempt='stage02_attempt03';manifest='source_manifest.json';logFull='5e8492'},
  @{module='EpsteinUnfold22';sourceDir='stage03\revision04';attempt='stage03_attempt04';manifest='source_manifest.json';logFull='4ee808'},
  @{module='EpsteinTail22';sourceDir='stage04';attempt='stage04_attempt01';manifest='source_manifest.json';logFull='4cc683'}
)
$allowed=@('propext','Classical.choice','Quot.sound')
$rows=@()
foreach($spec in $specs){
  $srcDir=Join-Path $roleDir $spec.sourceDir
  $outDir=Join-Path $srcDir $spec.attempt
  $source=Join-Path $srcDir ($spec.module+'.lean')
  $olean=Join-Path $outDir ($spec.module+'.olean')
  $log=Join-Path $outDir ($spec.module+'.log')
  $actualReceipt=Join-Path $outDir 'receipt.json'
  $manifest=Join-Path $srcDir $spec.manifest
  $actual=Get-Content -Raw -LiteralPath $actualReceipt|ConvertFrom-Json
  if($actual.status -ne 'AUTHOR_STAGE_AUX_PASS' -or $actual.actual_child_invocations -ne 1 -or -not $actual.all_source_inputs_unchanged){throw ('actual author PASS missing: '+$spec.module)}
  $run=$actual.rows[0]
  if($run.module -ne $spec.module -or $run.exit_code -ne 0 -or (Hash-File $source) -ne $run.source_sha256 -or (Hash-File $olean) -ne $run.olean_sha256 -or (Hash-File $log) -ne $run.log_sha256){throw ('actual artifact mismatch: '+$spec.module)}
  $bindings=Get-Content -Raw -LiteralPath $manifest|ConvertFrom-Json
  foreach($entry in $bindings.inputs){if((Hash-File $entry.path) -ne $entry.sha256){throw ('frozen input changed: '+$entry.path)}}
  $body=[IO.File]::ReadAllText($source)
  if([regex]::IsMatch($body,'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b')){throw ('forbidden source: '+$spec.module)}
  $declarations=@([regex]::Matches($body,'(?m)^#print axioms (Epstein22\.\w+)')|ForEach-Object{$_.Groups[1].Value})
  $logText=[IO.File]::ReadAllText($log)
  $audits=@([regex]::Matches($logText,"(?m)^'([^']+)' depends on axioms: \[([^\]]*)\]")|ForEach-Object{[ordered]@{name=$_.Groups[1].Value;axioms=@($_.Groups[2].Value.Split(',')|ForEach-Object{$_.Trim()}|Where-Object{$_ -ne ''})}})
  if($audits.Count -ne $declarations.Count){throw ('missing audit: '+$spec.module)}
  for($idx=0;$idx -lt $declarations.Count;$idx++){
    if($audits[$idx].name -ne $declarations[$idx]){throw ('wrong audit name: '+$spec.module)}
    foreach($ax in $audits[$idx].axioms){if($ax -notin $allowed){throw ('unallowed axiom: '+$ax)}}
  }
  $theorems=([regex]::Matches($body,'(?m)^theorem\s+')).Count
  $definitions=([regex]::Matches($body,'(?m)^def\s+')).Count
  if($theorems+$definitions -ne $declarations.Count){throw ('declaration/audit catalog mismatch: '+$spec.module)}
  $rows += [ordered]@{module=$spec.module;source=$source;source_sha256=(Hash-File $source);olean=$olean;olean_sha256=(Hash-File $olean);log=$log;log_sha256=(Hash-File $log);actual_receipt=$actualReceipt;actual_receipt_sha256=(Hash-File $actualReceipt);source_manifest=$manifest;source_manifest_sha256=(Hash-File $manifest);started_at=$run.started_at;finished_at=$run.finished_at;exit_code=0;theorem_count=$theorems;definition_count=$definitions;audits=$audits;FULL_log_receipt=$spec.logFull;status='AUTHOR_PASS_AUX_JUDGE_REQUIRED'}
}
$now=[DateTimeOffset]::UtcNow.ToString('o')
$raccord=Join-Path $roleDir 'G0_raccord_final.md'
$helper=Join-Path $roleDir 'write_G0_final_metadata.ps1'
$catalog=[ordered]@{schema='round22.role3.G0_final_catalog.v1';time=$now;node_id='16.1';status='AUTHOR_ALL_FOUR_PASS_AUX_JUDGE_REQUIRED';rows=$rows;module_count=$rows.Count;theorem_count=($rows|Measure-Object -Property theorem_count -Sum).Sum;definition_count=($rows|Measure-Object -Property definition_count -Sum).Sum;axiom_print_count=84;allowed_axioms=$allowed;raccord_path=$raccord;raccord_sha256=(Hash-File $raccord);metadata_helper_sha256=(Hash-File $helper);author_recompile_required=$false;new_Lean_invocations=0;Python_math_calls=0;old_PASS_replays=0;new_D_N_bound=$false;victory=$false;official_credit='ROOT_JUDGE_REQUIRED'}
[IO.File]::WriteAllText($catalogPath,($catalog|ConvertTo-Json -Depth 40)+[Environment]::NewLine,$utf8)
$receipt=[ordered]@{schema='round22.role3.G0_final_receipt.v1';time=$now;status='FINAL_FROZEN_AUTHOR_AUX_CATALOG';catalog_sha256=(Hash-File $catalogPath);module_count=$rows.Count;theorem_count=$catalog.theorem_count;definition_count=$catalog.definition_count;axiom_print_count=84;new_Lean_invocations=0;new_Python_math_calls=0;no_win=$true;metadata_actual_exit='tool return required separately'}
[IO.File]::WriteAllText($receiptPath,($receipt|ConvertTo-Json -Depth 12)+[Environment]::NewLine,$utf8)
$receipt|ConvertTo-Json -Depth 12
