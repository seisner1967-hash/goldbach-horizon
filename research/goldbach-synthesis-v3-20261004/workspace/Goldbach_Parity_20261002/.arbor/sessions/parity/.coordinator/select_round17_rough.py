"""Select the frozen four-form demand candidate; bookkeeping only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json,subprocess
BASE=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
COORD=BASE/'.arbor/sessions/parity/.coordinator'
HELPER=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p):return json.loads(p.read_bytes())
def invoke(c,*a,quiet=False):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(HELPER),c,'--cwd',str(BASE),'--run-name','parity',*a],capture_output=True,text=True,encoding='utf-8')
    if not quiet or p.returncode:print(p.stdout,end='')
    if p.stderr:print(p.stderr,end='',file=sys.stderr)
    if p.returncode:raise SystemExit(p.returncode)
report=BASE/'round17/agent2_capacity_incidence.md'
h='2c3b2dfadb507925b0fdc92a69b5174353f8f93ba2fc188175dadf05b38ad8d7'
assert sha256(report.read_bytes()).hexdigest()==h
assert '14.2' not in read(COORD/'idea_tree.json')['nodes'],'Already selected; do not rerun'
hyp=(
 'Mechanism: Partition canonique de la demande sans les incidences e1/p0, puis crible des quatre formes réelles après union physique de tous les cœurs admissibles.\n'
 'Hypothesis: La sous-famille des deux complémentaires z-rugueux possède une majoration indépendante T_R<=N/(8192u logu), avec collisions, troncature et reste CRT payés ; T_S et T_A restent ouverts.\n'
 'Observable: Nouvelle fenêtre complète de 201 entiers q=1200100..1200300, tous cœurs SF/unit<=82, partitions A/R/S, λ/G rationnels, carré Selberg et vrais kernels actifs sans signe présupposé.\n'
 'Conflicts: A7 acquis, aucune capacité consommée par cette borne ; absence ne signifie pas rugosité, raw/Λ(e)/faces/ledger conservés, source u>=10^24 distinct du test, aucun Win local.')
invoke('add','--parent-id','14','--hypothesis',hyp,quiet=True)
assert read(COORD/'idea_tree.json')['nodes']['14.2']['hypothesis']==hyp
invoke('update','--node-id','14.2','--status','running','--insight','Frozen FINAL2 read and primary statements checked. New exact numerical contract selected; mathematical results not presumed. Formalization targets actual four-form weights and quantitative bound, with T_S/T_A still open.',quiet=True)
invoke('prompt-executor','--node-id','14.2','--workdir',str(BASE),'--additional-context',
 'Use round17/PROBE_BLOCK.md, FINAL2 SHA '+h+' and feedback16. Protect799 archives. This receipt records the selected six-role workflow, not a separate user chat. Only new q-window1200100..1200300 and all SF/unit cores are authorized. Keep actual four affine forms, local saturation, exact λ/G, CRT+1, physical D/W, rawpowers and partition A/R/S. Source bound C6 is written partial, not a Win or finite input. Formalizers must derive obligations, no target-shaped bound or availability assumed. Judge independently audits only new files after all FINAL.',quiet=True)
receipt=dict(node='14.2',report='round17/agent2_capacity_incidence.md',report_sha256=h,contract='FINAL2 section7 complete four-form q window',
    numerical_contract_authorized=True,numerical_result_presumed=False,old_artifacts=799,finite_N=100000000,source_u_minimum='10^24',
    source_C6_written_only=True,remaining=['small-factor demand T_S','present-incidence demand T_A and once-only capacity','other ledger branches'],victory=False)
(COORD/'messages/round17_rough_selection.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=COORD/'checkpoint.json';j=read(p);j.update(phase='ROUND17_ROUGH_CONTRACT_SELECTED_TYPEII_MASK_REVIEW',current_nodes=['14.2'])
j['last_progress']+=' Fresh constraints and FINAL2 fully read; primary Selberg/RS statements verified. Node14.2 selected; new complete four-form bank authorized, no numerical result presumed. TypeII FINAL1 addendum for unit mask77 pending before its numerical authorization.'
j['previous_goal_turn_evidence']+=['round17/agent2_capacity_incidence.md','.arbor/sessions/parity/.coordinator/messages/round17_primary_source_context.md','.arbor/sessions/parity/.coordinator/messages/round17_rough_selection.json','.arbor/sessions/parity/experiments/14.2/executor_prompt.md']
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('NODE14.2_SELECTED; NEW_ROUGH_NUMERIC_CONTRACT_AUTHORIZED; no arithmetic or compiler called')
