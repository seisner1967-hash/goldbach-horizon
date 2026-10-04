"""Select frozen canonical double-semiprime layer18; bookkeeping only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json,subprocess
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p):return json.loads(p.read_bytes())
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
r=read(C/'messages/round18_root_conservation.json')
assert r['actual_preflight_attempts']==1 and r['actual_preflight_exit_code']==0 and r['exact_inventory997']
report='round18/agent2_capacity_incidence.md'
h='48dbcc5875c140d6d4991fa7d6cd58749048e3cf151e35f476893c27f81ae595'
assert sha256((B/report).read_bytes()).hexdigest()==h
tree=read(C/'idea_tree.json');assert '14.3' not in tree['nodes'],'Already selected; do not rerun'
labels=['Mechanism:','Hypothesis:','Observable:','Conflicts:']
lines=[s for s in (B/report).read_text(encoding='utf-8').splitlines() if any(s.startswith(t) for t in labels)]
assert len(lines)==4 and all(s.startswith(t) for s,t in zip(lines,labels))
hyp='\n'.join(lines)
invoke('add','--parent-id','14','--hypothesis',hyp)
assert read(C/'idea_tree.json')['nodes']['14.3']['hypothesis']==hyp
invoke('update','--node-id','14.3','--status','running','--insight',
 'FINAL2 fully read and SHA frozen; fresh constraints after13.10 read before selection. Genuine nonrough double-semiprime layer via canonical factors and integer CRT divided forms. Written all-parameter bound includes outer/inner CRT+1, budget onlyu>=10^36 vs fixedsourceu>=10^24. Composite quotient residual and T_A/global capacity remain open. Reciprocal m0 has complementp0q distinctsemiprime hence rawzero; m1 consumed physically once, no capacity credited by demand bound. New full5001q contract selected, no result presumed.')
invoke('prompt-executor','--node-id','14.3','--workdir',str(B),'--additional-context',
 'Read PROBE18, frozen FINAL2 SHA '+h+', formalization_guard18 and feedback17. Protect997. Only new whole q1400100..1405100/allSFunitcores>p0 through70 authorized. Full canonical resource factorizations, A/R/S andSS/complement, actual integerdivided forms/CRT determinants/rho/guards, targettheta/raw and properpowers retained. FiniteT3/Y1 noD5/10/11sourceusage. ActualD/W only selected nonzeroaxesplusm1; zeroaxes literal/unevaluatedothercells unpaid. Physicallymergevertices beforecharge, m0rawzero/m1onlyqaxis/ell1p0alreadyanchor. Source initialu>=10^24 and budgetonset10^36 explicit. Formalwrite permitted now, compile candidate after canonical newbankPASS inspected/rootauthorization; only actualobjects and derivedlocalfacts, nofreeG/density/availability/targetpremise. Judge afterallFINALfrozen, nooldbank/kernel/sign/PASS/Leanrerun.')
receipt=dict(node='14.3',report=report,report_sha256=h,contract='FINAL2 numerical contract complete closed5001q window',
 numerical_contract_authorized=True,numerical_result_presumed=False,protected_artifacts=997,finite_N=100000000,
 q_interval=[1400100,1405100],all_core_cap=70,finite_sieve_level=3,finite_Y=1,
 source_u_minimum='10^24',written_budget_u_minimum='10^36',source_intermediate_segment_unpaid=True,
 remaining=['S minus selected double-semiprime layer','T_A and single-consumption capacity','global D_N'],
 formal_sources_authorized=True,compiler_waits_for_canonical_numeric_PASS=True,victory=False)
(C/'messages/round18_semiprime_selection.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p)
cp.update(phase='ROUND18_TWO_NEW_CONTRACTS_SELECTED_FORMAL_WRITING_NUMERIC_PREPARATION',current_nodes=['13.10','14.3'],objective_complete=False,victory=False)
cp['last_progress']+=' FrozenFINAL2 fully read/hashconfirmed; node14.3 selected after freshconstraints. Canonical double-semiprime SS/allparameterCRT costs written; budgetonset10^36 and remainingS/T_A explicit. New entire5001q bank authorized, formal writing permitted but compilation waits numericPASS. No result presumed.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+[report,'.arbor/sessions/parity/.coordinator/messages/round18_semiprime_selection.json','.arbor/sessions/parity/experiments/14.3/executor_prompt.md']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('NODE14.3_SELECTED; new whole5001q/cores70 bank authorized; formal writing only before numericPASS; no math producer/compiler/audit invoked')
