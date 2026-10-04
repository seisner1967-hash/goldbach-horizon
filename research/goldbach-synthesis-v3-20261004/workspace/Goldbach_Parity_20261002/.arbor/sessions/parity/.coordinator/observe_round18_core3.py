"""Record already executed Lean18 core attempts, without invoking Lean."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import re,json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator';R=B/'round18/role3'
def digest(p):return sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_bytes())
rows=[]
for n in (1,2,3):
 r=read(R/f'attempt{n:02d}_receipt.json');p=read(R/f'attempt{n:02d}_started.json')
 assert r['attempt']==n and r['exit_code']==(0 if n==3 else 1)
 assert r['source_sha256']==r['snapshot_sha256']==digest(Path(r['source_snapshot']))
 assert r['builder_sha256']==digest(Path(r['builder_snapshot']))
 assert r['log_sha256']==digest(Path(r['log']))
 assert r['started_at_utc']==p['started_at_utc'] and r['source_sha256']==p['source_sha256']
 assert r['old_Lean_rebuilds']==r['old_producers_replayed']==r['old_oleans_copied']==0
 code=Path(r['source_snapshot']).read_text(encoding='utf-8').split('-- AXIOM_AUDIT_BEGIN')[0]
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|trustMe)\b',code)
 log=Path(r['log']).read_text(encoding='utf-8')
 rows.append(dict(attempt=n,exit_code=r['exit_code'],receipt_sha256=digest(R/f'attempt{n:02d}_receipt.json'),
  source_snapshot_sha256=r['snapshot_sha256'],log_sha256=r['log_sha256'],
  error_diagnostics=log.count(': error:'),warning_diagnostics=log.count(': warning:'),
  Lean_generated_sorryAx_in_failed_log='sorryAx' in log))
r=read(R/'attempt03_receipt.json');source=R/'SeparatedTypeII.lean';log=(R/'attempt03.log').read_text(encoding='utf-8')
assert r['source_sha256']==digest(source)=='4513f3323bbf475b329daf423de805eb207d3fe88793f91016369bcb0d5228d7'
assert r['log_sha256']=='aab20695b18c648e5f1c560d8f68fdd0ff58f15ca1358ca97e07ace277ede6b3'
assert r['olean_sha256']==r['preserved_olean_sha256']==digest(Path(r['olean']))==digest(Path(r['preserved_olean']))=='896daceeb6a093f808313556ee63a93761ecd5831bc6279b8b88ffe9212d1dd5'
assert r['numeric_receipt_sha256']==digest(B/'round18/role6/typeii_canonical_receipt.json')
assert r['numeric_output_sha256']==digest(B/'round18/typeii.json')
assert r['root_observation_sha256']==digest(C/'messages/round18_typeii_root_observation.json')
assert ': error:' not in log and ': warning:' not in log and 'sorryAx' not in log
body=source.read_text(encoding='utf-8').split('-- AXIOM_AUDIT_BEGIN')[0]
decls=re.findall(r'^(theorem|def|structure)\s+(\w+)',body,re.M)
assert [name for _,name in decls]==r['new_declarations']
counts={kind:sum(k==kind for k,_ in decls) for kind in ['theorem','def','structure']}
printed=[]
for name,kind,axioms in re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log):
 assert all(a.strip() in {'propext','Classical.choice','Quot.sound'} for a in axioms.split(',') if a.strip())
 printed.append(name.rsplit('.',1)[-1])
assert printed==r['new_declarations'] and len(printed)==58
result=dict(status='ROOT_READ_AUTHOR_CORE18_PASS03_INDEPENDENT_JUDGE_PENDING',actual_attempts=rows,
 declaration_counts=counts,standard_axiom_prints=len(printed),source_sha256=r['source_sha256'],
 log_sha256=r['log_sha256'],olean_sha256=r['olean_sha256'],
 role3_attempt02_classification='technical missing Decidable instances and cascading elaboration after local-attribute repair',
 mathematical_content='actual beta support, periodic separated coefficients, inverse product/divisor reindexing and actual calibration identities',
 CRT_source_lower_bound_or_R6_or_global_Gamma_estimate_proved=False,
 independent_judge18_completed=False,cumulative_verified_modules=22,cumulative_verified_auxiliary_theorems=337,
 producer_Lean_audit_rerun_by_root=False,victory=False)
with (C/'messages/round18_core3_root_observation.json').open('x',encoding='utf-8') as h:json.dump(result,h,indent=2);h.write('\n')
cp=read(C/'checkpoint.json');cp['last_progress']+=' CoreSeparatedTypeII authorPASS03 actualexit0 after failed01/02; root fully reads source/log/receipt and checks all58standardaxiomprints,30theorems26definitions2structures, frozen olean/source bindings. Failed02 Decidable cascade retained; source noexplicit sorry, generatedfailedsorryAx is not validation. IndependentJudgepending, official22modules337aux unchanged; actualCRT source/Gamma/globalD_N stillopen.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/role3/attempt02_receipt.json','round18/role3/attempt03_receipt.json','round18/role3/SeparatedTypeII.lean','.arbor/sessions/parity/.coordinator/messages/round18_core3_root_observation.json']))
(C/'checkpoint.json').write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=B/'REPORT.md';txt=p.read_text(encoding='utf-8')
txt+='\n### Core TypeII18 : PASS auteur, Juge encore attendu\n\nTrois invocations réelles du core : exit1,exit1,exit0. La seconde conserve des erreurs Decidable/elaboration ; la troisième compile sans avertissement ni sorryAx, avec58impressions d’axiomesstandards (30théorèmes,26définitions,2structures). Root lit et lie source/captures/logs/reçus/olean sans compiler. Le core prouve la bijection des vrais couples produit/diviseur, les coefficients périodiques séparés, le coût exact et les prix de calibration. La minoration CRT source et Γ/globalD_N restent ouverts. Aucun nouvel ajout au cumul officiel22modules337aux avant le contrôle indépendant du Juge18.\n'
p.write_text(txt,encoding='utf-8')
print(json.dumps(result))
