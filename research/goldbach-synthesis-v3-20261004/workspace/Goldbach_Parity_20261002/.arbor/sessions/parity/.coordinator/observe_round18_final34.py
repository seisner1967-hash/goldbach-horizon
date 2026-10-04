"""Coordinator inspection of frozen author metadata; no mathematical producer/compiler."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import json, re
B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
R = B / 'round18'
def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def verify(bindings):
    for name, expected in bindings.items():
        assert digest(B / name) == expected, name
f3 = load(R / 'role3/final_receipt.json')
m3 = load(R / 'role3/manifest.json')
f4 = load(R / 'role4/final_receipt.json')
assert digest(R/'agent3_formalisation.md') == f3['report_sha256'] == 'b0d82b52621c6f57a1a34f24d3a422437847a685678e1b905aea2058062bcb62'
assert digest(R/'role3/manifest.json') == f3['manifest_sha256'] == '957acece4f93ac74438e41130d9e65429cd237e983d5cad4d882ed74ad9de93b'
assert digest(R/'role3/final_receipt.json') == 'ef9132dd3a78c741556271850bd499b8dce57da19c0a4773a5a242af31edfc49'
assert digest(R/'agent4_formalisation.md') == '9f30e03fbfab99eeb88ef421e6f1dc35f1897383cc910b41ea9cdc661592b81d'
assert digest(R/'role4/final_receipt.json') == '6b28aecc8e0a90c69beaeeb3b7b93a12ad45c345252ccc2c7da4cbc2bbf95660'
assert len(m3['bindings']) == m3['binding_count'] == 89
verify(m3['bindings']); verify(m3['immutable_inputs'])
verify(f4['bindings']); verify(f4['historical_readonly_bindings'])
records = []
for role, ledger in [(3,'build_receipt.json'), (3,'crt_build_receipt.json'), (3,'lower_build_receipt.json'), (4,'build_receipt.json')]:
    for a in load(R/f'role{role}'/ledger)['attempts']:
        snapshot = a.get('source_snapshot', a.get('snapshot'))
        assert digest(snapshot) == a['snapshot_sha256'] == a['source_sha256']
        assert digest(a['builder_snapshot']) == a.get('builder_sha256', a.get('builder_snapshot_sha256'))
        assert digest(a['log']) == a['log_sha256']
        code = Path(snapshot).read_text(encoding='utf-8')
        code = re.sub(r'/\-.*?\-/', '', code, flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustMe)\b', code)
        log = Path(a['log']).read_text(encoding='utf-8')
        if a['exit_code'] != 0: assert 'error:' in log
        else:
            assert 'error:' not in log and 'sorryAx' not in log
            original = Path(a['source'])
            assert digest(original) == a['source_sha256']
            assert digest(a['olean']) == a['olean_sha256']
            for _, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
                assert {x.strip() for x in axioms.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}
        records.append(dict(role=role, ledger=ledger, attempt=a['attempt'], exit_code=a['exit_code'],
          source_snapshot_sha256=a['snapshot_sha256'], log_sha256=a['log_sha256'],
          errors=log.count('error:'), warnings=log.count('warning:'),
          generated_sorryAx_in_failed_log=a['exit_code']!=0 and 'sorryAx' in log))
assert len(records) == 23 and sum(x['exit_code']!=0 for x in records) == 15
assert f3['counts']['theorems'] == 60 and f4['counts_new_only']['theorems'] == 110
assert f3['counts']['axiom_prints'] == 96 and f4['counts_new_only']['print_axioms'] == 146
finalizer_failure=load(R/'role3/finalize_failed01.json')
assert finalizer_failure['actual_exit_code']==1 and finalizer_failure['source_snapshot_timing'].startswith('POSTEXEC')
observation=dict(status='ROOT_INSPECTED_FROZEN_FINAL3_FINAL4_JUDGE_PENDING', utc=datetime.now(timezone.utc).isoformat(),
  role3_bindings=89, role4_bindings=len(f4['bindings']), historical_readonly_bindings=len(f4['historical_readonly_bindings']),
  actual_Lean_invocations=records, new_author_counts=dict(modules=8,theorems=170,definitions=68,structures=4,axiom_prints=242),
  Count_PASS_style_warning_expected=True, author_finalizer_reader_failure=finalizer_failure,
  frozen_sources_fully_read_by_root=True, actual_failed_logs_fully_read_by_root=True,
  root_reexecuted_Lean_numeric_audit_or_finalizers=False, independent_judge_authorized=False,
  source_R6_D5_D10_D11_or_global_D_N_proved=False, score=0,victory=False,
  FINAL3_sha256=digest(R/'agent3_formalisation.md'), FINAL4_sha256=digest(R/'agent4_formalisation.md'))
dest=C/'messages/round18_final34_root_observation.json'
with dest.open('x',encoding='utf-8') as f: json.dump(observation,f,indent=2,ensure_ascii=False); f.write('\n')
p=C/'checkpoint.json'; cp=load(p)
cp['phase']='ROUND18_FINAL3_FINAL4_FINAL6_FROZEN_CRT_ANNEX_PREPARATION_JUDGE_PREPARATION_ONLY'
cp['in_flight_executors']=[dict(role=5,agent='/root/round18_independent_judge',status='preparation_only_no_audit_or_Lean_authorized'),dict(role=6,agent='/root/round18_numeric_crt_annex',node='13.10',status='new_CRT_annex_preparation_only_no_producer_authorized')]
cp['current_protected_artifacts']=997; cp['current_protected_registry']='round18/previous_artifacts_sha256.json'; cp['current_protected_registry_sha256']=digest(R/'previous_artifacts_sha256.json')
cp['last_progress']+=' FINAL3/4 gelled and fullyrootread; all89/role4bindings and 23actualLeaninvocations15technicalfails snapshot/logs verified metadataonly. New8authorPASS170thm68defs4structures242prints, Count one benign push_cast warning retained; official22/337 unchanged pending independentJudge. One actualRole3finalizer readerFAIL omitting5noaxiomprints preserved POSTEXEC-honest; correctedclosing no recompilation. FreshCRTannex preparing separate rationals/guards; no new producer yet. Judge preparation repaired exhaustive primality/reversecore support/warning reader, audit not authorized.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/agent3_formalisation.md','round18/role3/manifest.json','round18/role3/final_receipt.json','round18/agent4_formalisation.md','round18/role4/final_receipt.json',str(dest.relative_to(B)).replace('\\','/')]))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=observation['status'], role3_bindings=89, role4_bindings=len(f4['bindings']), actual_attempts=23,failures=15,author_new_theorems=170, observation_sha256=digest(dest))))
