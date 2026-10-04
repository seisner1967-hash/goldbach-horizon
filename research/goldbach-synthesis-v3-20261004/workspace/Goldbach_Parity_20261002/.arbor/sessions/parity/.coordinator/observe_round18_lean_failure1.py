"""Record actual first failed new Lean attempt18 from stored evidence only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json,re
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator';R=B/'round18/role3'
def digest(p):return sha256(p.read_bytes()).hexdigest()
receipt=json.loads((R/'attempt01_receipt.json').read_bytes())
assert receipt['attempt']==1 and receipt['exit_code']==1
assert receipt['source_sha256']==receipt['snapshot_sha256']==digest(R/'attempt01_SeparatedTypeII_source.lean.txt')=='4c146142daa3e265bf1013bb4d4e5ab1099b4b538de698f122f913f100ed6d48'
assert receipt['log_sha256']==digest(R/'attempt01.log')=='c8b1353eee5cc92cd269f798f8bede0a625af7a5b74e992751b7ebe2d990793b'
assert receipt['builder_sha256']==digest(R/'attempt01_builder.py.txt')=='fd8b0326456a742b77482432e559888d0ab64b9e14a598b6a46642455d36e433'
code=(R/'attempt01_SeparatedTypeII_source.lean.txt').read_text(encoding='utf-8').split('-- AXIOM_AUDIT_BEGIN')[0]
assert not re.search(r'\b(sorry|admit|axiom|native_decide|trustMe)\b',code)
log=(R/'attempt01.log').read_text(encoding='utf-8');assert 'sorryAx' in log
groups=['local attribute syntax','Nat.Coprime.mul_left missing API','Nat.ModEq cancellation/normalization','Finset product memberships','conditional expression simplification']
result=dict(status='ROOT_READ_ACTUAL_FAILED_LEAN18_ROLE3_ATTEMPT01',attempt=1,exit_code=1,
 source_snapshot_sha256=receipt['snapshot_sha256'],log_sha256=receipt['log_sha256'],builder_snapshot_sha256=receipt['builder_sha256'],
 error_diagnostics=log.count(': error:'),warning_diagnostics=log.count(': warning:'),classification='technical elaboration/API errors',groups=groups,
 explicit_source_sorry_or_admit=False,failed_log_contains_Lean_generated_sorryAx=True,
 mathematical_parity_deduction_falsified=False,old_Lean_rebuilds=receipt['old_Lean_rebuilds'],
 producer_or_Lean_or_audit_rerun_by_root=False,victory=False)
(C/'messages/round18_lean_failure01_root.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=json.loads(p.read_bytes())
cp['last_progress']+=' First newLean18role3 actualexit1 snapshot/source/log fullyread byroot; eight diagnostics plus stylewarning, API/elaboration only, generatedsorryAx in failedlog despite no explicitsource sorry. Failedattempt retained, no globalparityfalsification or validatednewmodule. Correctionpassed toformal4, role3repairs currentcandidate.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/role3/attempt01_receipt.json','round18/role3/attempt01.log','.arbor/sessions/parity/.coordinator/messages/round18_lean_failure01_root.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=B/'REPORT.md';txt=p.read_text(encoding='utf-8')
txt+='''
### Premier échecLean18 réellement archivé

Le rôle3 a compilé SeparatedTypeII après autorisation root/numericPASS : attempt01exit1, du21:41:18au21:41:42UTC. Root a lu intégralement sourcecapturée/log/reçu/builder et vérifié leursempreintes. Huit diagnostics d'erreur et un avertissement concernent syntaxe localattribute, API Coprime.mul_left absente, normalisationModEq, membershipsFinset et simplificationconditionnelle. La source ne contient aucun sorry/admit/axiomead hoc, mais le logéchoué imprime des sorryAx injectés par Lean après erreurs : aucun nouveau module n'est validé par cette tentative. Échec technique conservé, aucun blocage de parité logique inventé ; auteurcorrige, avis API transmis au secondformaliseur. Le Juge indépendant18 reste ultérieur.
'''
p.write_text(txt,encoding='utf-8')
print(json.dumps(result,ensure_ascii=False))
