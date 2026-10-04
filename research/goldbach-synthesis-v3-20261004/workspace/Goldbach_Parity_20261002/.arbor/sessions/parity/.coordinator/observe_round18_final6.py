"""Bind frozen FINAL6 metadata and actual closure evidence; no mathematics execution."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');R=B/'round18';C=B/'.arbor/sessions/parity/.coordinator'
def read(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
expected={'agent6.md':'95f54c20ebde7682b3ac1e4a78695ccf5ab79148322479379de8b27b44d80075',
 'numeric_manifest.json':'3b97b7a1e18175ed6ced2750ad86284be14fc0969b272618ccd9846372a35aa1',
 'role6_final_receipt.json':'29f5bb311bbeec25ced7b01e5d1c59f73696e603d45488802bb1e77a8f7bc5fa',
 'role6/closure_receipt.json':'bbbf84046cc71b379013a3789c9b4f4b9866d2160be40c04634420a1c945691f',
 'role6/finalize_attempt01.log':'b3f96a979af612d23e15cfa27c48ccf8223bc3a634b8d6148d7fe5d7536ee002',
 'role6/finalize_attempt01_receipt.json':'5abdf69cc2688e0c317e82e1ca2b355a6bc313e88279f2a420cab75f31434803'}
for name,h in expected.items():assert digest(R/name)==h,name
m=read(R/'numeric_manifest.json');f=read(R/'role6_final_receipt.json');x=read(R/'role6/closure_receipt.json');r=read(R/'role6/finalize_attempt01_receipt.json')
assert m['files']==len(m['sha256'])==67 and f['bound_files']==len(f['sha256'])==68
assert f['sha256']==dict(m['sha256'],**{'numeric_manifest.json':expected['numeric_manifest.json']})
for name,h in f['sha256'].items():assert digest(R/name)==h,name
assert r['exit_code']==x['finalizer_exit_code']==0
assert r['source_sha256']==r['snapshot_sha256']==digest(R/'finalize_numeric.py')==digest(R/'role6/finalize_attempt01_source.py.txt')=='623996e75f6757c85182c2ac9501152fc4a0340984737464829b6de8cce2daca'
assert r['launcher_sha256']==digest(R/'role6/finalize_once.py')
assert x['role6_final_receipt_sha256']==expected['role6_final_receipt.json'] and x['numeric_manifest_sha256']==expected['numeric_manifest.json']
assert x['report_sha256']==expected['agent6.md'] and x['finalizer_actual_receipt_sha256']==expected['role6/finalize_attempt01_receipt.json']
assert x['finalizer_log_sha256']==expected['role6/finalize_attempt01.log'] and x['finalizer_started_sha256']==digest(R/'role6/finalize_attempt01_started.json')
assert m['strict_sign_positions']==f['strict_sign_positions']==320 and m['sign_counts']==f['sign_counts']==dict(POSITIVE=191,NEGATIVE=83,ZERO=46)
assert m['canonical_new_bank_invocations']==3 and m['actual_numeric_failures']==1 and m['unique_isolated_replays']==2
assert not m['Lean_called'] and not m['global_D_N'] and not m['victory'] and not f['victory']
result=dict(status='ROOT_INSPECTED_FROZEN_FINAL6_18',checked_final_artifacts_sha256=expected,numeric_manifest_bindings=67,final_receipt_bindings=68,
 actual_metadata_finalizer_exit_code=0,canonical_bank_invocations=3,actual_technical_numeric_failures=1,unique_isolated_replays=2,
 stored_strict_sign_positions=320,stored_sign_distribution=m['sign_counts'],independent_judge18='actual startup; preparation only; no audit/Lean authorization yet',
 root_reran_producer_kernel_Lean_sign_expression_or_audit=False,victory=False)
with (C/'messages/round18_final6_root_observation.json').open('x',encoding='utf-8') as h:json.dump(result,h,indent=2);h.write('\n')
p=C/'checkpoint.json';cp=read(p);cp['phase']='ROUND18_NUMERIC_FINAL6_FROZEN_FORMAL_EXTENSIONS_ACTIVE_JUDGE_PREPARATION_ONLY'
cp['in_flight_executors']=[x for x in cp['in_flight_executors'] if x['role']!=6]+[dict(role=5,agent='/root/round18_independent_judge',status='actual_startup_independent_preparation_only_no_audit_or_Lean_authorized')]
cp['last_progress']+=' FrozenFINAL6 report/manifests/closure/log/source/launcher fullyrootread and exact67+1bindings verified. Metadatafinalizer actualexit0;320storedpositions191POS83NEG46ZERO,3canonicalruns(oneencodingfailure)+2uniqueisolatedreplays. Numericagentreleased; freshindependentJudge18 actualstartup preparationonly whileFINAL3/4pending. No independent18validation or Win.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/agent6.md','round18/numeric_manifest.json','round18/role6_final_receipt.json','round18/role6/closure_receipt.json','.arbor/sessions/parity/.coordinator/messages/round18_final6_root_observation.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=B/'REPORT.md';txt=p.read_text(encoding='utf-8');txt+='\n### FINAL6/18 gelé et Juge indépendant en préparation\n\nRapport final numérique et67liaisons+manifeste68 ont été intégralement lus et vérifiés par root, ainsi que la clôture après finaliseurmetadataexit0. Trois runs canoniques(0,1,0), deux uniques rejeux isolés(0,0) byteidentiques ;320positionsstockées191POS83NEG46ZERO. Aucun run mathématique/audit/Lean par root. Rôle6 terminé ; Juge18 indépendant nouvellement démarré en préparation seulement. Les FINAL3/4 et l’autorisation d’audit indépendant restent attendus. Cumul officiel22modules337aux inchangé ; déficit globalD_N et victoire ouverts.\n';p.write_text(txt,encoding='utf-8')
print(json.dumps(result))
