"""Write the concrete candidate gate after root stored-evidence review."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
observation_path=C/'messages/round19_nonss_finish_root_observation.json'
observation=json.loads(observation_path.read_text(encoding='utf-8'))
assert observation['status']=='ROOT_VERIFIED_ACTUAL_UNIQUE_NEW_NONSS19_FINISH_PASS_AUXILIARY_ONLY'
gate={
 'authorization':'ROOT19_FORMAL4_COMPILE','root_authorized':True,
 'canonical_new_numeric_pass_inspected':True,'round':19,'node':'14.4',
 'authorized_at_utc':datetime.now(timezone.utc).isoformat(),
 'numeric_bindings':observation['numeric_bindings'],
 'numeric_receipt_relative_path':'round19/role6_nonss/canonical_attempt01/receipt.json',
 'root_review_evidence':str(observation_path),
 'root_review_sha256':hashlib.sha256(observation_path.read_bytes()).hexdigest(),
 'full_read_candidate_source_hashes':observation['formal4_full_root_read_current_source_hashes'],
 'scope':'Five new role4 modules only. Preserve PREEXEC source and every actual log/receipt; necessary technical repairs after failure allowed. Do not rebuild historical imports or rerun PASS modules. No independent Judge or numeric producer authorized.',
 'auxiliary_only':True,'victory':False,'official_Judge_counts_modified':False
}
p=B/'round19/role4/root_compile_authorization.json'
with p.open('x',encoding='utf-8') as f: f.write(json.dumps(gate,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':'CONCRETE_ROOT19_FORMAL4_COMPILE_GATE_WRITTEN',
 'gate':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'bound_new_numeric_files':len(gate['numeric_bindings']),'victory':False}))
