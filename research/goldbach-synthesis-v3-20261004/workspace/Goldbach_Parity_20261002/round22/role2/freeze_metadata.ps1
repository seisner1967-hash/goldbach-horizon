$ErrorActionPreference = 'Stop'
$taskBase = 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'
$taskOwned = Join-Path $taskBase 'round22\role2'
$taskUtf8 = New-Object System.Text.UTF8Encoding($false)
function TaskDigest([string]$taskPath) {
  $taskFile = Get-Item -LiteralPath $taskPath
  [ordered]@{ path=$taskFile.FullName; bytes=$taskFile.Length; sha256=(Get-FileHash -LiteralPath $taskPath -Algorithm SHA256).Hash.ToLowerInvariant() }
}
function TaskJson([string]$taskPath, $taskObject) {
  [System.IO.File]::WriteAllText($taskPath, ($taskObject | ConvertTo-Json -Depth 14), $taskUtf8)
}
$taskReadSpecs = @(
 @{ path=(Join-Path $taskBase 'round22\USER_DIRECTIVE.md'); scope='FULL'; capture='835ce9; reread8fad34'; detail='Current authoritative pivot; instructions distinguished from historical attached materials.' },
 @{ path=(Join-Path $taskBase 'round22\PROBE_BLOCK.md'); scope='FULL'; capture='529d21; reread8fad34'; detail='Two concrete evidence items, all four probe questions, gates.' },
 @{ path='C:\Users\Utilisateur\.codex\skills\arbor-agent-ideate\SKILL.md'; scope='FULL'; capture='66f6bf after freshviewf4cd25; reread849967'; detail='Valid sequence restarted after earlier premature skill read2b721e.' },
 @{ path=(Join-Path $taskBase 'round20\agent5_judge.md'); scope='FULL'; capture='fcbb47'; detail='Read-only historical adjudication, not recompiled or numerically replayed.' },
 @{ path=(Join-Path $taskOwned 'fresh_constraints.txt'); scope='FULL'; capture='f4cd25'; detail='Actual fresh helper output, no TreeAdd invoked by ROLE2.' },
 @{ path='D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\Analysis\MellinInversion.lean'; scope='FULL'; capture='53747d'; detail='Read-only source; actual API hypotheses, no Lean probe.' },
 @{ path='D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\Analysis\Fourier\PoissonSummation.lean'; scope='FULL'; capture='1c82bb'; detail='Read-only source; Schwartz and convergence APIs, no Lean probe.' },
 @{ path='D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\NumberTheory\LSeries\RiemannZeta.lean'; scope='TARGETED'; capture='75ffaa'; detail='rg hits for definitions, differentiability and Dirichlet-series statement; not entire module.' },
 @{ path='D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib\NumberTheory\LSeries\Dirichlet.lean'; scope='TARGETED'; capture='e94d22'; detail='Lines325-421 read in full; existing Lambda convolution provenance disclosed; no method application or compilation.' },
 @{ path=(Join-Path $taskBase 'round22\agent2_operator.md'); scope='FULL'; capture='84a979'; detail='Final paper report4817tokens before manifest creation.' },
 @{ path=(Join-Path $taskOwned 'uniform_formula.md'); scope='FULL'; capture='6bab79'; detail='Complete uniform derivation3185tokens, paper-only.' },
 @{ path=(Join-Path $taskOwned 'lean_contract.md'); scope='FULL'; capture='259db0'; detail='Final contract2467tokens, no Lean sources executed.' },
 @{ path=(Join-Path $taskOwned 'numeric_contract.md'); scope='FULL'; capture='82cd13'; detail='Complete contract2283tokens; only two Markdown bullet spaces corrected afterwards, no mathematical change.' }
)
$taskLocalReads = foreach ($taskSpec in $taskReadSpecs) {
  $taskEntry = TaskDigest $taskSpec.path
  $taskEntry.scope=$taskSpec.scope; $taskEntry.capture=$taskSpec.capture; $taskEntry.detail=$taskSpec.detail
  $taskEntry
}
$taskWebSources = @(
 @{ title='Borthwick modular spectral geometry slides'; url='https://math.dartmouth.edu/~specgeom/Borthwick_slides.pdf'; scope='TARGETED'; portions='Pages24,30,35-38,63; Friedrichs, continuum, Eisenstein, channel formula.' },
 @{ title='Cakoni-Chanillo Transmission Eigenvalues and the Riemann Zeta Function'; url='https://sites.math.rutgers.edu/~chanillo/te.pdf'; scope='TARGETED'; portions='Section2; current primary read153view0 lines513-577 identifies excluded Mobius/totient proof.' },
 @{ title='Lagarias-Suzuki integrals of Eisenstein series'; url='https://arxiv.org/pdf/math/0412039'; scope='TARGETED'; portions='Pages1-2, equations1,2,10,11; full nonprimitive Epstein and constant term, no RH inference.' },
 @{ title='NIST DLMF'; url='https://dlmf.nist.gov/'; scope='TARGETED'; portions='2.5.E1/E2,5.4.E3,5.5.E1,5.7.E6,25.2,27.4.E12; exact formulas and domains, not whole site.' },
 @{ title='Trefethen-Weideman exponentially convergent trapezoidal rule'; url='https://people.maths.ox.ac.uk/trefethen/publication/PDF/2014_149.pdf'; scope='TARGETED'; portions='Section5 pages14-16, equations5.8/5.9; outline proof not assumed.' },
 @{ title='Mayer Selberg zeta via continued fraction dynamics'; url='https://archive.mpim-bonn.mpg.de/346/1/preprint_1990_86.pdf'; scope='TARGETED'; portions='SectionsII-III, pages2-9; current153view1 OCR ambiguous radius acknowledged, no closed tail claimed.' },
 @{ title='Connes trace formula and zeros'; url='https://alainconnes.org/wp-content/uploads/selecta.ps-2.pdf'; scope='TARGETED'; portions='Introduction pages1-2 and Theorem3 pages20-23; global open qualification and local regularization.' },
 @{ title='Marcolli qBostConnes'; url='https://www.its.caltech.edu/~matilde/qBostConnes.pdf'; scope='TARGETED'; portions='Hamiltonian logk and partition page1 only; full article/title not inspected, no KMS facts used.' },
 @{ title='Behrndt-Malamud-Neidhardt Scattering matrices and Weyl functions'; url='https://arxiv.org/pdf/math-ph/0604013'; scope='TARGETED'; portions='Actual155view0 pages0-7 lines0-390, boundary pairs/Weyl/resolvent formula; not full39pages.' }
)
foreach ($taskWeb in $taskWebSources) { $taskWeb.raw_pdf_sha256=$null; $taskWeb.hash_note='No raw PDF downloaded; text tool captures separately hashed. TARGETED denotes content actually inspected.' }
$taskCaptures = Get-ChildItem -LiteralPath $taskOwned -File | Where-Object { $_.Name -like 'web_sources*.json' } | ForEach-Object { TaskDigest $_.FullName }
TaskJson (Join-Path $taskOwned 'read_manifest.json') ([ordered]@{
 schema='ROLE2_READ_MANIFEST22_V1'; created_utc=[DateTime]::UtcNow.ToString('o'); local_reads=@($taskLocalReads); web_sources=$taskWebSources; text_tool_captures=@($taskCaptures);
 incomplete_or_failed_reads=@('Zagier scanned PDF: text0 and screenshot metadata only, NOT READ; attempted download failed, no local file.','Original Bost-Connes scan inaccessible, no full-source claim.','Simon bibliography timed out154view0/1, not used.','Broad local rg418002 truncated, only observed hits, not FULL module.');
 historical_constraints='No old mathematical PASS replay, no round21 writes, no source method from forbidden family applied.'
})
$taskReadManifestDigest = TaskDigest (Join-Path $taskOwned 'read_manifest.json')
TaskJson (Join-Path $taskOwned 'read_receipt.json') ([ordered]@{
 schema='ROLE2_READ_RECEIPT22_V1'; read_manifest=$taskReadManifestDigest; local_scope_statement='FULL and TARGETED scopes listed truthfully; hashes certify bytes, not a claim to have read inaccessible content.';
 report_captures=@('84a979 FULL agent2_operator','6bab79 FULL uniform_formula','259db0 FULL lean_contract','82cd13 FULL numeric_contract, two Markdown spaces subsequently corrected');
 numeric_invocations22=0; lean_compiler_invocations22=0; lean_api_probe_invocations22=0; previous_role4_math_invocations21=0;
 paper_audit='ROLE6 messages only: signs, factors, endpoint indices and closed tails checked on paper; no numerical PASS.'
})
$taskFreezePaths = @((Join-Path $taskBase 'round22\agent2_operator.md')) + @(Get-ChildItem -LiteralPath $taskOwned -File | Where-Object { $_.Name -notin @('final_manifest.json','final_receipt.json') } | ForEach-Object { $_.FullName })
$taskFreezeEntries = @($taskFreezePaths | Sort-Object -Unique | ForEach-Object { TaskDigest $_ })
TaskJson (Join-Path $taskOwned 'final_manifest.json') ([ordered]@{
 schema='ROLE2_FINAL22_V1'; created_utc=[DateTime]::UtcNow.ToString('o'); status='FINAL_PAPER_ONLY_FROZEN'; artifacts=$taskFreezeEntries;
 ownership='round22/role2/** and round22/agent2_operator.md only'; methods='Epstein nonprimitive unfolding; actual modular operator obligation; analytic scattering telescope; Mellin-Poisson continuous envelopes';
  win=$false; d_n_gain=$false; numeric_pass=$false; formal_pass=$false;
 scopes=@('G0 UNFOLD_AUX24cases including sqrtN scale','H0 HEAT_AUX fullN reference, certified producer OPEN','C0 COEFFICIENT_N fullcontour, astronomical cost and certified producer OPEN','O1 operator-scattering identification OPEN','D_N fullledger bridge OPEN');
 protected_registry_root_message=[ordered]@{count=3089; sha256='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'; note='Root-provided registry identity; ROLE2 does not claim independent conservation run.'};
 gates='Source proposal final; root selection/conservation/review and fresh execution authorization required for any new math or Lean invocation.'
})
$taskFinalDigest = TaskDigest (Join-Path $taskOwned 'final_manifest.json')
TaskJson (Join-Path $taskOwned 'final_receipt.json') ([ordered]@{
 schema='ROLE2_FINAL_RECEIPT22_V1'; created_utc=[DateTime]::UtcNow.ToString('o'); final_manifest=$taskFinalDigest;
 report=(TaskDigest (Join-Path $taskBase 'round22\agent2_operator.md')); formula=(TaskDigest (Join-Path $taskOwned 'uniform_formula.md')); lean_contract=(TaskDigest (Join-Path $taskOwned 'lean_contract.md')); numeric_contract=(TaskDigest (Join-Path $taskOwned 'numeric_contract.md'));
 freeze_command='powershell -NoProfile -ExecutionPolicy Bypass -File round22/role2/freeze_metadata.ps1'; operation='Metadata-only SHA256/JSON creation; no mathematical evaluator/compiler called.';
 execution_counts=[ordered]@{lean22=0; lean_api_probe22=0; math_python22=0; numeric22=0; old_pass_replay=0; role4_lean21=0; role4_math21=0; round21_writes_since_pivot=0};
 qualification='Exact identities and bounds proposed on paper, not Lean-certified. AUX tests not executed. No parity or Goldbach victory.'
})
[ordered]@{ status='FINAL_PAPER_ONLY_FROZEN'; manifest=$taskFinalDigest; final_receipt=(TaskDigest (Join-Path $taskOwned 'final_receipt.json')); report=(TaskDigest (Join-Path $taskBase 'round22\agent2_operator.md')); formula=(TaskDigest (Join-Path $taskOwned 'uniform_formula.md')); lean=(TaskDigest (Join-Path $taskOwned 'lean_contract.md')); numeric=(TaskDigest (Join-Path $taskOwned 'numeric_contract.md')); artifacts=$taskFreezeEntries.Count } | ConvertTo-Json -Depth 6
