$ErrorActionPreference='Stop'
$roleDir='D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\role3'
$priorPath=Join-Path $roleDir 'G0_final_catalog.json'
$newPath=Join-Path $roleDir 'G0_final_catalog_v2.json'
$receiptPath=Join-Path $roleDir 'G0_final_receipt_v2.json'
if((Test-Path -LiteralPath $newPath) -or (Test-Path -LiteralPath $receiptPath)){throw 'refusing metadata v2 replacement'}
function Hash-File($path){(Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()}
$catalog=Get-Content -Raw -LiteralPath $priorPath|ConvertFrom-Json
$totalTheorems=0
$totalDefinitions=0
$totalAudits=0
foreach($row in $catalog.rows){
  foreach($kind in @('source','olean','log','actual_receipt','source_manifest')){if((Hash-File $row.$kind) -ne $row.($kind+'_sha256')){throw ('frozen artifact changed: '+$row.module+'/'+$kind)}}
  $bindings=Get-Content -Raw -LiteralPath $row.source_manifest|ConvertFrom-Json
  foreach($entry in $bindings.inputs){if((Hash-File $entry.path) -ne $entry.sha256){throw ('frozen input changed: '+$entry.path)}}
  $totalTheorems += [int]$row.theorem_count
  $totalDefinitions += [int]$row.definition_count
  $totalAudits += @($row.audits).Count
}
if($totalTheorems -ne 69 -or $totalDefinitions -ne 15 -or $totalAudits -ne 84){throw 'actual declaration totals disagree with final raccord'}
$catalog.schema='round22.role3.G0_final_catalog.v2'
$catalog.time=[DateTimeOffset]::UtcNow.ToString('o')
$catalog.theorem_count=$totalTheorems
$catalog.definition_count=$totalDefinitions
$catalog.axiom_print_count=$totalAudits
$catalog.metadata_helper_sha256=Hash-File (Join-Path $roleDir 'write_G0_final_metadata_v2.ps1')
$catalog|Add-Member -NotePropertyName predecessor_catalog_sha256 -NotePropertyValue (Hash-File $priorPath)
$catalog|Add-Member -NotePropertyName metadata_correction -NotePropertyValue 'v1 Measure-Object returned null totals for OrderedDictionary rows; v2 explicitly sums actual parsed row counts, preserving all v1 artifacts'
$utf8=[System.Text.UTF8Encoding]::new($false)
[IO.File]::WriteAllText($newPath,($catalog|ConvertTo-Json -Depth 40)+[Environment]::NewLine,$utf8)
$receipt=[ordered]@{schema='round22.role3.G0_final_receipt.v2';time=$catalog.time;status='FINAL_FROZEN_AUTHOR_AUX_CATALOG';catalog_sha256=(Hash-File $newPath);module_count=@($catalog.rows).Count;theorem_count=$totalTheorems;definition_count=$totalDefinitions;axiom_print_count=$totalAudits;new_Lean_invocations=0;new_Python_math_calls=0;no_win=$true;metadata_actual_exit='tool return required separately'}
[IO.File]::WriteAllText($receiptPath,($receipt|ConvertTo-Json -Depth 12)+[Environment]::NewLine,$utf8)
$receipt|ConvertTo-Json -Depth 12
