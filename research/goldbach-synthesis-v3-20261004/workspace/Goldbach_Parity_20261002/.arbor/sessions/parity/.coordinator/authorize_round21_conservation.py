"""Authorize actor6's reviewed new metadata-only preflight; never execute it here."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round21'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()
expected={
 R/'conservation.py':'ab4495d95052c8e64253a1c4e93726799c36f7c0418217dd9c599d24d72d54c2',
 R/'role6/run_conservation_once.py':'5cba3b716cf510490243722f60de50e87899d1014cef70d5af1eade4849c45a4',
 R/'role6/preparation.json':'f7419bbfbe7c902ac87ddaa8065d2f4f351fd89fdd94196c99acb6c8f1175a73',
 R/'previous_artifacts_sha256.json':'5c1c372a2a723a1a06224c6531c2e0775978bbe902f02cf910450a583772896c',
 R/'PROBE_BLOCK.md':'015cccf57d59c53abd34f4b6623b891199fdb61a9f8acafcd4f352df0b8fd7de',
 B/'round20/controller_manifest.json':'815d2ce77851a01d9addfa4202a17edb787a42f7f080d4e41cab18aa7b002b04',
 B/'INPUT_HASHES.json':'5f3f8498fc1343b69ade24634d0253ec662c090641a852465e6b70059b005460',
 Path(r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'):'4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c',
 Path(r'D:\Users\Utilisateur\Downloads\goldbach_synthesis.pdf'):'bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24',
 Path(r'D:\Users\Utilisateur\Downloads\Goldbach_Continuation_Cofacteur_Court_2026-10-01.zip'):'32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd'}
for p,d in expected.items(): assert sha(p)==d,str(p)
prep=json.loads((R/'role6/preparation.json').read_text(encoding='utf-8'))
assert prep['status']=='PREPARED_UNSTARTED_AWAITING_DISTINCT_ROOT_AUTHORIZATION'
assert prep['preflight_subprocess_invocations']==prep['mathematical_executions']==prep['Lean_executions']==0
registry=json.loads((R/'previous_artifacts_sha256.json').read_text(encoding='utf-8'))
assert len(registry['sha256'])==registry['file_count']==3028
assert not (R/'conservation.json').exists()
assert not list((R/'role6').glob('conservation_attempt01*'))
gate=dict(prep['required_authorization_fields'])
gate.update(preparation_sha256=expected[R/'role6/preparation.json'],authorized_at_utc=datetime.now(timezone.utc).isoformat(),
 root_FULL_read_evidence={'source':'b744be','launcher':'4e31f2','preparation':'653e27'},
 exact_protected_file_count=3028,root_runtime_originals_sources_hash_verified=True,
 actor='/root/round21_numeric_conservation',only_one_new_metadata_preflight_authorized=True,
 no_Lean_or_mathematical_bank_authorized=True,root_compiler_math_preflight_or_audit_execution=False,victory=False)
dest=C/'messages/round21_conservation_authorization.json'
with dest.open('x',encoding='utf-8') as f: f.write(json.dumps(gate,ensure_ascii=False,indent=2)+'\n')
obs={'status':'ROOT21_AUTHORIZED_NEW_UNIQUE_METADATA_CONSERVATION_ONLY',
 'gate_sha256':sha(dest),'verified_prepared_path_count':len(expected),'bindings_sha256':{str(p):d for p,d in expected.items()},
 'all_preflight_sources_fully_read':True,'actual_preflight_not_started':True,'root_preflight_Lean_math_or_audit_execution':False,'victory':False}
(C/'messages/round21_conservation_authorization_root_observation.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json'; cp=json.loads(p.read_text(encoding='utf-8')); cp['phase']='ROUND21_CONSERVATION_GATE_GRANTED_IDEATION_ACTIVE'
cp['last_progress']+=' ROOTFULLpreflightsourceb744be/launcher4e31f2/prep653e27 and10hashverified; uniqueactor6 metadata gate granted, no math/Lean21 authorized/noWin.'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round21_conservation_authorization.json']
p.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':obs['status'],'gate_sha256':sha(dest),'source_sha256':gate['source_sha256'],'launcher_sha256':gate['launcher_sha256'],'preparation_sha256':gate['preparation_sha256']},indent=2))
