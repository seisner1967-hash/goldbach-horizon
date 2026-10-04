"""ROOT documentary binding only: no mathematical evaluation or compiler."""
import hashlib, json
from datetime import datetime, timezone
from pathlib import Path
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
targets=[('round22/role3/continuous_contract_delivery22_revision03.txt','af466104a72bb89b5e0a5e7ecf117c06c610d23d14a82139cfda7cb96c6fcb82'),('round22/role3/continuous_contract_delivery22_revision03_read_receipts.json','4a160309fde4a80bc3e7d8171bc6e6c8439299043dcea4be91cd5913b42366cc')]
entries=[]
for name,digest in targets:
 p=B/name;assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
 entries.append(dict(path=name,sha256=digest,bytes=p.stat().st_size))
reads=json.loads((B/targets[1][0]).read_text(encoding='utf-8-sig'))
for x in reads['FULL_entries']+reads['preserved_previous_inputs']:
 p=Path(x['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'],str(p)
cp_path=C/'checkpoint.json';cp=json.loads(cp_path.read_text(encoding='utf-8-sig'))
assert cp['official_auxiliary_validation']['modules']==78 and cp['official_auxiliary_validation']['declarations']==1304
o=dict(schema='ROUND22_ROOT_DOCUMENTARY_DELIVERY03_OBSERVATION',time_utc=datetime.now(timezone.utc).isoformat(),status='CONTRACT_DELIVERED_WITH_COMPILED_ERROR_ENVELOPE_GLOBAL_COEFFICIENT_OPEN',entries=entries,ROOT_FULL_reads=['7695a7','c5accc'],independent_math_owner='ROLE3_AND_ROLE5',new_Lean_invocations=0,new_numeric_evaluations=0,new_credit=0,official_modules=78,official_declarations=1304,previous_delivery_bytes_preserved=True,full_global_numeric_coefficient_computed=False,D_N_paid=False,WIN=False)
out=C/'messages/round22_delivery03_observation.json'
with out.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
cp['continuous_contract_delivery03']=o
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nContrat continu revision03 livre, SHA af466104a72bb89b5e0a5e7ecf117c06c610d23d14a82139cfda7cb96c6fcb82, ROOT FULL7695a7/c5accc. Identite13, discret15 et quantification/enveloppe17 compiles, officiel78/1304 auxiliaires. Catalogue natif/coefficient complet N1e8 et D_N/WIN ouverts; aucune nouvelle evaluation ni credit de ce rapport.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
