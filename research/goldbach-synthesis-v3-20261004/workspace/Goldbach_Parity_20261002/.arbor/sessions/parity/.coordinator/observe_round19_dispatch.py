"""Record actually accepted startups; no preflight or mathematics execution."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json
C = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\.arbor\sessions\parity\.coordinator')
p = C/'checkpoint.json'; cp = json.loads(p.read_bytes())
dispatch = json.loads((C/'messages/round19_dispatch.json').read_bytes())
assert cp['rounds_completed'] == 18 and cp['phase'] == 'ROUND19_FRESH_CONSTRAINTS_AND_PROBE_READY'
cp.update(phase='ROUND19_TWO_IDEATIONS_ACTIVE_CONSERVATION_PREPARATION_ONLY',in_flight_executors=[
    dict(role=x['role'],agent=x['agent'],status='actual_startup_preflight_preparation_no_execution_authorized' if x['role']==6 else 'actual_quantitative_ideation_startup')
    for x in dispatch['actual_startup_confirmed']])
cp['last_progress'] += ' Two fresh ideation19 startups actual; new numeric dispatch and priorCRT followup refused by thread capacity, resolved by reusing completed content-review handle for metadata-only role6preflight19, actualstartup confirmed. All1361archives immutable, no19node/bank/Lean/preflight selected or executed, no externalblocker and noWin.'
cp['previous_goal_turn_evidence'] = list(dict.fromkeys(cp['previous_goal_turn_evidence']+['.arbor/sessions/parity/.coordinator/messages/round19_dispatch.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('ROUND19_ACTUAL_STARTUPS_RECORDED; metadata only')
