"""Correct unconsumed ROOT gate provenance; preserve its original bytes."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
C=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\.arbor\sessions\parity\.coordinator')
p=C/'messages/round22_role4_analytic_batch01_authorization1.json'
raw=p.read_bytes(); old=hashlib.sha256(raw).hexdigest()
assert old=='15302a4d8f850c9c5f4e5135181dae05101612fa784c28a497f6269ce6051c78'
B=C.parents[3]; actual=B/'round22/role4/h1_contour/analytic_batch01/actual_attempt01'
assert not actual.exists()
archive=C/'messages/round22_role4_analytic_batch01_authorization1_unconsumed_initial.json'
with archive.open('xb') as f:f.write(raw)
gate=json.loads(raw)
gate['component_failure_closure_sha256']=gate['component_technical_failure_receipt_sha256']
gate['component_technical_failure_receipt_sha256']='2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48'
gate['corrected_utc']=datetime.now(timezone.utc).isoformat()
gate['unconsumed_initial_gate_sha256']=old
gate['correction']='Raw actual receipt field corrected; distinct closure field retained. No launcher or Lean invocation before correction.'
p.write_text(json.dumps(gate,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(p),'corrected_gate_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'original_gate_preserved':str(archive),'launcher_invocations':0,'Lean_invocations':0},indent=2))
