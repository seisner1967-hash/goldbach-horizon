"""Select frozen TypeII mode and unit-mask addendum, bookkeeping only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import subprocess,json
BASE=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
COORD=BASE/'.arbor/sessions/parity/.coordinator'
HELPER=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p):return json.loads(p.read_bytes())
def invoke(c,*a,quiet=False):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(HELPER),c,'--cwd',str(BASE),'--run-name','parity',*a],capture_output=True,text=True,encoding='utf-8')
    if not quiet or p.returncode:print(p.stdout,end='')
    if p.stderr:print(p.stderr,end='',file=sys.stderr)
    if p.returncode:raise SystemExit(p.returncode)
inputs={'round17/agent1_calibrated_typeii.md':'446c2d8fe21c86b05fbaf0e2864e7129da1b964287f31ff4287c0a19251103a9',
        'round17/role1/unit_mask_addendum.md':'51735b4ecd379b8b58066d24b952ff779347af5ae8a32ecd4b4ac303b7636cac'}
for n,h in inputs.items():assert sha256((BASE/n).read_bytes()).hexdigest()==h,n
assert '13.9' not in read(COORD/'idea_tree.json')['nodes'],'Already selected; do not rerun'
hyp=(
 'Mechanism: Calibration payante modulo39 du vrai mode TypeII χ13(v)χ13(w), avec AP sur q et comparaison des lois 1/(v−1) et 1/v du produit candidat j=vw.\n'
 'Hypothesis: Pour cette paire de coefficients, le principal résiduel gagne 1/V après calibration ; fronts, BV supplémentaire et prix L13/E77 sont conservés, sans contrôle des autres modes.\n'
 'Observable: Nouvelle progression complète b974026..1136363, vrais produits v17/19, β et caps physiques, deux masques unitaires0/77, Γ/T et prix distincts avec rawproperpowers et intervalles rationnels stricts.\n'
 'Conflicts: Brut x/u³ distinct du normalisé x/u ; masque16 réel gcd(b,N) conservé, aucun Γ agrégé petit ni partenaire ajouté, modèle S(bN)/ledger/sourceonset intacts, aucun Win auxiliaire.')
invoke('add','--parent-id','13','--hypothesis',hyp,quiet=True)
assert read(COORD/'idea_tree.json')['nodes']['13.9']['hypothesis']==hyp
invoke('update','--node-id','13.9','--status','running','--insight','Both FINAL1 and addendum fully read; actual mask16 checked in immutable code. New complete matrix contract selected; no finite sign or asymptotic estimate presumed. Partial one-mode estimate only, whole TypeII/Gamma/globalD_N open.',quiet=True)
invoke('prompt-executor','--node-id','13.9','--workdir',str(BASE),'--additional-context',
 'Read PROBE17, feedback16, FINAL1 and unit_mask_addendum. Protect799 archives. This receipt records current six-role workflow, no new user chat. Numerical new matrix b974026..1136363, v17/19, physical q endpoints and both masks0/77 authorized. Keep prime and TypeII prices distinct, rawpowers, multiplicities, fronts. No BV/source bound at finiteN1e8. A7 remains acquired. Formalizers derive actual weights, no margin/density/Gamma/availability input. Independent Judge only after FINAL/frozen evidence.',quiet=True)
receipt=dict(node='13.9',inputs_sha256=inputs,contract='FINAL1 section6 plus unit_mask_addendum section4',
    numerical_contract_authorized=True,numerical_result_presumed=False,old_artifacts=799,finite_N=100000000,
    source_u_minimum='10^24',additional_BV_onset_unknown=True,one_mode_only=True,
    corrected_root_provenance='round16/typei_checks.py line33 unit=gcd(b,N), not gcd(b,77N)',victory=False)
(COORD/'messages/round17_typeii_selection.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=COORD/'checkpoint.json';j=read(p);j.update(phase='ROUND17_TWO_NUMERIC_CONTRACTS_SELECTED_FORMALIZATION',current_nodes=['14.2','13.9'])
j['last_progress']+=' FINAL1 and mask addendum fully read/hashbound. Root mistaken oldmask77 corrected by actual line33 gcd(b,N), no old source changed. Node13.9 selected; second complete new numerical contract authorized, source BV/finite separate. Formal3 started after two failed threadlimit dispatches launched no work. Formal4 dispatch pending slot; no external blocker.'
j['previous_goal_turn_evidence']+=list(inputs)+['.arbor/sessions/parity/.coordinator/messages/round17_typeii_selection.json','.arbor/sessions/parity/experiments/13.9/executor_prompt.md']
j['coordination_incident']='Two formal3 dispatch calls returned threadlimit and launched no audit/compiler; fresh formal3 succeeded after FINAL1 addendum released slot. Formal4 scheduling uses remaining slots.'
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('NODE13.9_SELECTED; NEW_TYPEII_NUMERIC_CONTRACT_AUTHORIZED; no math producer/compiler called')
