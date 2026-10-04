$ErrorActionPreference = 'Stop'
$basePath = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$ledger = Get-Content -LiteralPath (Join-Path $basePath 'round20/role3/build_receipt.json') -Raw | ConvertFrom-Json
$attempts = @($ledger.attempts | Where-Object { $_.attempt -ge 8 -and $_.attempt -le 14 })
if ($attempts.Count -ne 7 -or $attempts[6].actual_exit_code -ne 0 -or $attempts[6].attempt -ne 14) {
    throw 'Actual ROLE3 attempts08..14 not complete in stored ledger'
}
$bindings = [ordered]@{}
$projection = @()
foreach ($item in $attempts) {
    $projection += [ordered]@{attempt=$item.attempt; module=$item.module;
        actual_exit_code=$item.actual_exit_code; status=$item.status;
        source_sha256=$item.source_sha256; log_path=$item.log_path; log_sha256=$item.log_sha256}
    $paths = @($item.log_path, ('round20/role3/attempt{0:D2}_{1}_receipt.json' -f $item.attempt, $item.module))
    foreach ($rel in $paths) {
        $bindings[$rel] = (Get-FileHash -LiteralPath (Join-Path $basePath $rel) -Algorithm SHA256).Hash.ToLower()
    }
    if ($bindings[$item.log_path] -ne $item.log_sha256) { throw 'Actual log SHA differs from original receipt' }
}
foreach ($id in @(8,10,12,13)) {
    $rel = 'round20/role3/attempt{0:D2}_analysis.json' -f $id
    $bindings[$rel] = (Get-FileHash -LiteralPath (Join-Path $basePath $rel) -Algorithm SHA256).Hash.ToLower()
}
$value = [ordered]@{created_utc=[DateTime]::UtcNow.ToString('o'); round=20;
    role3_final_observed_cutoff=14; observed_author_passes=6; observed_actual_technical_failures=8;
    copied_stored_receipt_projection=$projection; input_bindings_sha256=$bindings;
    mathematical_recomputation=$false; own_Lean_invocations=0; own_numeric_invocations=0; victory=$false}
$encoding = New-Object Text.UTF8Encoding($false)
$bytes = $encoding.GetBytes(($value | ConvertTo-Json -Depth 12) + "`n")
$stream = [IO.File]::Open((Join-Path $PSScriptRoot 'late_role3_observation.json'), [IO.FileMode]::CreateNew, [IO.FileAccess]::Write)
try { $stream.Write($bytes, 0, $bytes.Length) } finally { $stream.Dispose() }
Write-Output 'Stored ROLE3 receipt labels08..14 copied; 18 original bindings; no mathematics or compiler executed.'
