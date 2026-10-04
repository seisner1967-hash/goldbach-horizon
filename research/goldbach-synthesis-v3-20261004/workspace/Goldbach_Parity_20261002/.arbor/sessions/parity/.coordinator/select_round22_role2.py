"""Select frozen modular concept22. Metadata-only; never an evaluator."""
import json, hashlib, re, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round22'; C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode: raise RuntimeError((p.returncode,p.stdout,p.stderr))
    return p.stdout
expected={'agent2_operator.md':'be2a121cd14fe3513c9ee8ae28458a8a03f38957599d4a9bbba4e2174dbdcafe','role2/uniform_formula.md':'720b8b2363c222321e7f50752591a8a5d0e992c119bfc3b4f445b9c80b7b7825','role2/lean_contract.md':'9648829a0eb94f57f2a2e0e056836fac03e611d5a1d2fb21e4f453a04e953dbc','role2/numeric_contract.md':'943470e906efd8a77b2fbdbe50f001978e9bbaa9c20101f6ad379bcca9e03ebf','role2/final_manifest.json':'0e225a6f5cf711a9588670e868a94ee5103be4b9124275888f2e79f7ffa3f13f','role2/read_manifest.json':'ddce30863d28ce429b180ca0e2efdcfdb30391cf8c47422eacbb25b8e0a2b24e'}
for rel,s in expected.items(): assert sha(R/rel)==s,rel
m=read(R/'role2/final_manifest.json'); rd=read(R/'role2/read_manifest.json')
assert len(m['artifacts'])==21 and len(rd['local_reads'])==13
for row in m['artifacts']+rd['local_reads']+rd['text_tool_captures']:
    p=Path(row['path']); assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],str(p)
assert not m['win'] and not m['d_n_gain'] and not m['numeric_pass'] and not m['formal_pass']
# Root adopts the frozen actor's four-question probe, four moves, five-field
# diversity/self-check, already FULL-read; root makes no mathematical proposal.
report=R/'agent2_operator.md'
lines=re.findall(r'^(?:Mechanism|Hypothesis|Observable|Conflicts):[^\n]+',report.read_text(encoding='utf-8'),re.M)
assert len(lines)==4 and [x.split(':',1)[0] for x in lines]==['Mechanism','Hypothesis','Observable','Conflicts']
before=read(C/'idea_tree.json'); assert '16' not in before['nodes']
broad='\n'.join(['Mechanism: Géométrie modulaire globale et canaux de diffusion issus de véritables objets continus indépendants de la réponse arithmétique.','Hypothesis: Un producteur géométrique construit et normalisé offre une représentation globale, avec domaines opérateurs, modes et erreurs explicitement payés.','Observable: Identité analytique exacte et troncature continue falsifiable, puis pont au bilan complet seulement après certification indépendante.','Conflicts: Le pivot22 interdit les méthodes locales bilinéaires, cribles, inversion Mobius, Vaughan et restes AP ; aucune positivité ou trace contenant la réponse ne sera postulée.'])
invoke('add','--parent-id','ROOT','--hypothesis',broad)
assert set(read(C/'idea_tree.json')['nodes'])-set(before['nodes'])=={'16'}
invoke('add','--parent-id','16','--hypothesis','\n'.join(lines))
invoke('update','--node-id','16.1','--status','running','--insight','Frozen FINAL2 actual whole-lattice Epstein unfolding selected. First G0 real s3/2 finite/infinite row and closed tail, source-writing preparation only. Gamma/zeta certified producer, operator identification, HEAT, coefficientN and D_N remain OPEN. No numerical PASS or Lean invocation22 yet; 24case AUX is not fullN arithmetic validation.')
context='ROUND22 definitive continuous pivot. Frozen FINAL2 '+str(report)+' SHA'+expected['agent2_operator.md']+'; formula '+str(R/'role2/uniform_formula.md')+' SHA'+expected['role2/uniform_formula.md']+'; Lean/numeric contracts frozen with finalmanifestSHA'+expected['role2/final_manifest.json']+'. ROLE3 ownership round22/role3/** and agent3_formalisation.md. Read final sources before writing. Source writing authorized for true Epstein22 concrete s3/2 primitive, signed affine cells, finite telescope/isometry, infinite unfolding and continuous closed tail. No sorry/admit/addedaxiom/unsafe/native_decide or target as premise. No compiler/APIprobe until distinct root gate after own informative new24casebank PASS and FULL source/builder/prep+SHA. Need genuine integrability/summability/reindexing/positive guards; a generic telescope is not the selected result. No banned methods/oldPASS replay. 3089 archives preserved, sourceu>=1e24, AUX versus heat/coefficientN/D_N separate. Gamma, diffusion and fullledger independent OPEN obligations; noWin. Standard analytic LSeries provenance deferred outside G0, no excluded decomposition may be imported as candidate method.'
invoke('prompt-executor','--node-id','16.1','--workdir',str(B),'--additional-context',context)
prompt=C.parent/'experiments/16.1/executor_prompt.md'
obs={'status':'ROUND22_FINAL2_FROZEN_SELECTED16.1_SOURCE_WRITING_ONLY','created_utc':datetime.now(timezone.utc).isoformat(),'category':'16','selected_node':'16.1','actor_probe_fivefields_fourmoves_adopted':str(report),'root_FULL_report':'7bb22f','root_FULL_formula':'9356a6','root_FULL_lean':'d4bf59','root_FULL_numeric':'2927c8','root_FULL_manifest':'dcc844','root_FULL_receipts':'dbfb6d','root_FULL_readmanifest':'677ce3','fresh_constraints_FULL':'02d43b','ideate_skill_FULL':'d4a13e','artifact_bindings_verified':21,'local_read_bindings_verified':13,'web_capture_bindings_verified':10,'executor_prompt_sha256':sha(prompt),'math_authorized':False,'Lean_authorized':False,'win':False,'standard_analytic_LSeries_provenance':'Deferred beyond G0; no excluded local decomposition introduced.'}
(C/'messages/round22_role2_selection.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
cp=read(C/'checkpoint.json'); cp['current_nodes']=['15.2','16.1']; cp['phase']='ROUND22_TWO_CONTINUOUS_CONCEPTS_SELECTED_SOURCE_WRITING_GATES_CLOSED'
cp['in_flight_executors']=[{'role':3,'agent':'/root/round22_formal3_prepare','status':'G0_SOURCE_WRITING_AUTHORIZED_NO_LEAN'},{'role':4,'agent':'/root/round22_formal4_trace','status':'REAL_TRACE_SOURCE_PREPARATION_NO_LEAN'},{'role':6,'agent':'/root/round21_numeric_conservation','status':'EPSTEIN24_FINAL_SOURCE_PREPARATION_NO_MATH'}]
cp['previous_goal_turn_evidence']+=['round22/agent2_operator.md','round22/role2/final_manifest.json','.arbor/sessions/parity/.coordinator/messages/round22_role2_selection.json','.arbor/sessions/parity/experiments/16.1/executor_prompt.md']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
