"""Project and verify source-preparation bindings; metadata only."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role4'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()
manifest=P/'gamma_prepared_manifest2.json'; imports=P/'gamma_import_bindings2.json'
assert sha(manifest)=='2bceda49bb82eaffa0b48cbbcb00dcbdb0f7ea95ba2e7a8994a096bf808c7976'
assert sha(imports)=='96d70cb2e2e58d3757162b1d9c0cb18b368d778a6f5130b49d1679c1fedb0402'
m=read(manifest); deps=read(imports)
assert m['status']=='PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED'
assert m['node']=='15.2' and not m['unresolved_modules'] and m['qualified_prints_exact']
assert m['compiler_invocations']==m['mathematical_numeric_invocations']==0 and not m['win']
assert m['import_module_count']==deps['module_count']==3184 and not deps['unresolved']
assert len(m['immutable_inputs'])==6387
for row in m['immutable_inputs']: assert sha(Path(row['path']))==row['sha256'],row['path']
binding_map={row['path']:row['sha256'] for row in m['immutable_inputs']}
assert len(binding_map)==6387
for row in deps['entries']:
    assert binding_map[row['source']]==row['source_sha256']
    assert binding_map[row['olean']]==row['olean_sha256']
projection={k:v for k,v in m.items() if k!='immutable_inputs'}
projection.update({'scope':'SHA_BYTE_VERIFICATION_AND_HEADER_PROJECTION_ONLY_NO_COMPILATION','observed_utc':datetime.now(timezone.utc).isoformat(),'manifest_sha256':sha(manifest),'imports_sha256':sha(imports),'byte_bindings_verified':6387,'manifest_FULL_text_read':False,'cache_sources_FULL_text_read':False,'source_FULL_read':'701280','preparation_FULL_read':'d27bbe','launcher_FULL_read':'597c12','metadata_helper_FULL_read':'f9b2b4','read_receipts_FULL_read':'2a9932','actual_Gamma_bank':False,'gate_opened':False,'launcher_trace_repair_pending':'Separate v3 START+ownedPREcopies+oleanSHA requested; v2 never executed.'})
target=C/'messages/round22_gamma_prepared2_observation.json'
with target.open('x',encoding='utf-8') as f: json.dump(projection,f,ensure_ascii=False,indent=2); f.write('\n')
print(json.dumps(projection,ensure_ascii=False,indent=2))
