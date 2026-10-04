$ErrorActionPreference = 'Stop'
$role1Base = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$role1Dir = Join-Path $role1Base 'round21\role1'
$role1Report = Join-Path $role1Base 'round21\agent1_signed.md'
function Get-Role1Binding([string]$path, [string]$mode, [string[]]$ranges) {
    $item = Get-Item -LiteralPath $path
    [ordered]@{path=$item.FullName;sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath $item.FullName).Hash.ToLowerInvariant();bytes=$item.Length;read_mode=$mode;ranges=$ranges}
}
$role1Inputs = @(
    (Get-Role1Binding 'C:\Users\Utilisateur\.codex\skills\arbor-agent-ideate\SKILL.md' 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round21\PROBE_BLOCK.md') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base '.arbor\sessions\parity\.coordinator\messages\round20_feedback.md') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round20\agent5_judge.md') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round20\ideation_failure_feedback20_final.md') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round20\agent1_switched_composite.md') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round20\role3\SwitchedIncidenceEstimator.lean') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round20\role3\PhysicalCompositeSubtraction.lean') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round20\role3\CompositeAPConductor.lean') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round20\role3\SwitchedSelbergWeight.lean') 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Base 'round18\role3\SeparatedTypeII.lean') 'FULL' @('entire file')),
    (Get-Role1Binding 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\NumberTheory\AbelSummation.lean' 'FULL' @('entire file')),
    (Get-Role1Binding (Join-Path $role1Dir 'constraints_pre_ideate.txt') 'FULL' @('entire saved helper output, fresh before IDEATE')),
    (Get-Role1Binding 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\Analysis\SpecialFunctions\Log\Deriv.lean' 'TARGETED' @('rg hits: hasDerivAt_log, HasDerivAt.log, differentiableAt_log, lines47,51,63,104,106-107,142,146; full file not claimed')),
    (Get-Role1Binding 'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\Analysis\SpecialFunctions\Log\Basic.lean' 'TARGETED' @('lines333-382 inclusive; log_prod/log_nat_eq_sum_factorization')),
    (Get-Role1Binding (Join-Path $role1Base 'round20\role4_geometry\FriableSourceGeometry.lean') 'TARGETED' @('rg declaration hits sourceU/sourceA/sourceAlpha/sourcegeometry; lines331-395 inclusive'))
)
$role1InputManifest = [ordered]@{
    kind='ROUND21_ROLE1_HONEST_READ_MANIFEST';created_utc=[DateTime]::UtcNow.ToString('o');base=$role1Base;
    full_count=@($role1Inputs | Where-Object {$_.read_mode -eq 'FULL'}).Count;
    targeted_count=@($role1Inputs | Where-Object {$_.read_mode -eq 'TARGETED'}).Count;
    entries=$role1Inputs;
    helper_calls=[ordered]@{tool='arbor_state.py view --cwd B --run-name parity --format constraints';actual_calls=2;exit_codes=@(0,0);metadata_only=$true;findings=37;pruned=5;max_depth=2;saved_view_sha256='8fa53bf40b5848895b11c9f600704ceadeeb97ee7de2b51a4efba64efffa306e';unobserved_chunk_ids_not_evidence=$true};
    web_reads=@([ordered]@{url='https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/AbelSummation.html';scope='TARGETED tool response; lines1-105 displayed; latest API not cache authority'},[ordered]@{url='https://github.com/leanprover-community/mathlib4/blob/9837ca9d65d9de6fad1ef4381750ca688774e608/Mathlib/NumberTheory/AbelSummation.lean';scope='NOT_READ';outcome='cache miss'});
    search_incidents=@('An initial broad rg against round18/lean hit a missing directory and truncated broad output. No FULL read of that output is claimed; SeparatedTypeII.lean was subsequently read FULL by its exact path.','An initial rg against a nonexistent NumberTheory/PrimeCounting directory returned an error; Log.Basic was subsequently read at the precise declared lines.');
    original_PDF_ZIP_current_body_read=$false;inherited_fixed_frame_only=$true;
    no_math_execution=$true;no_Lean=$true;no_old_PASS_or_numeric_replay=$true
}
$role1InputPath = Join-Path $role1Dir 'input_manifest.json'
$role1InputManifest | ConvertTo-Json -Depth 10 | Set-Content -Encoding UTF8 -LiteralPath $role1InputPath
foreach ($entry in $role1Inputs) {
    $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $entry.path).Hash.ToLowerInvariant()
    if ($actual -ne $entry.sha256) { throw ('Input changed: '+$entry.path) }
}
if ((Get-FileHash -Algorithm SHA256 -LiteralPath $role1Report).Hash.ToLowerInvariant() -ne '0e6bac077503477d03f78c3c121b40134a67e1504b733bfb26175efeca884d70') { throw 'Report changed before closure' }
$role1Owned = @(
    $role1Report,
    (Join-Path $role1Dir 'constraints_pre_ideate.txt'),
    (Join-Path $role1Dir 'provenance_correction01.md'),
    (Join-Path $role1Dir 'finalize_metadata.ps1'),
    $role1InputPath
)
$role1Bindings = [ordered]@{}
foreach ($path in $role1Owned) {
    $relative = $path.Substring($role1Base.Length + 1).Replace('\','/')
    $role1Bindings[$relative] = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant()
}
$role1FinalManifestPath = Join-Path $role1Dir 'final_manifest.json'
[ordered]@{kind='ROUND21_ROLE1_FINAL_FROZEN_MANIFEST';created_utc=[DateTime]::UtcNow.ToString('o');base=$role1Base;bindings=$role1Bindings;input_manifest_sha256=$role1Bindings['round21/role1/input_manifest.json'];not_bound_self_or_final_receipt=$true;no_mutation_old_archives=$true} | ConvertTo-Json -Depth 8 | Set-Content -Encoding UTF8 -LiteralPath $role1FinalManifestPath
$role1ReceiptPath = Join-Path $role1Dir 'final_receipt.json'
[ordered]@{
    kind='FINAL1_ROUND21_CONCEPTUAL_AUXILIARY_PRE_SELECTION';created_utc=[DateTime]::UtcNow.ToString('o');status='FINAL1_FROZEN_NO_WIN';
    report_path=$role1Report;report_sha256=$role1Bindings['round21/agent1_signed.md'];
    manifest_sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath $role1FinalManifestPath).Hash.ToLowerInvariant();
    input_manifest_sha256=$role1Bindings['round21/role1/input_manifest.json'];input_count=$role1Inputs.Count;full_count=$role1InputManifest.full_count;targeted_count=$role1InputManifest.targeted_count;input_integrity_unchanged=$true;
    proposed_parent='13';proposed_depth=2;candidate_count=5;chosen='physical-frame, finite AP envelope and Abel variation';
    paper_bound='|actualAP-main| <= (32/7)*E_phys + (16/7)*log N; E_phys constructed finite max, no small-error premise';
    numerical_contract=[ordered]@{N=100000000;lower_j_exclusive=12500000;upper_j_inclusive=25000000;whole_window_before_masks=$true;old19_old20_overlap_explicit=$true;producer_new_required=$true;source_onset_false_at_finite_N=$true;no_execution_authorized_by_role1=$true};
    actual_Lean_invocations=0;actual_math_Python_invocations=0;actual_Judge_invocations=0;old_replay_count=0;tree_node_mutations=0;score=0;victory=$false;
    scope_limits=@('E_phys distribution/SD/BV aggregation unproved','principal/M0/kappa global bridge unproved','tails/slack/rawPP and all source capacities retained','D_N full ledger unproved');
    source_outputs_frozen=$true
} | ConvertTo-Json -Depth 10 | Set-Content -Encoding UTF8 -LiteralPath $role1ReceiptPath
[ordered]@{report_sha256=$role1Bindings['round21/agent1_signed.md'];input_manifest_sha256=$role1Bindings['round21/role1/input_manifest.json'];final_manifest_sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath $role1FinalManifestPath).Hash.ToLowerInvariant();final_receipt_sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath $role1ReceiptPath).Hash.ToLowerInvariant();inputs=$role1Inputs.Count;full=$role1InputManifest.full_count;targeted=$role1InputManifest.targeted_count;math_execution_count=0;Lean_execution_count=0;old_archive_mutation_count=0} | ConvertTo-Json -Depth 5
