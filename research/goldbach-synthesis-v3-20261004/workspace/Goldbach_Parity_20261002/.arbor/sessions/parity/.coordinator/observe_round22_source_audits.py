"""Bind two delegated SOURCE/PAPER audits; no mathematical adjudication here."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
expected={
 'round22/judge5/C5_source_review22.md':'b2458e4edfd3a8b21de91a09d2d3ea4a0134ae764dc64d7c1d617cdd3b0a66e8',
 'round22/judge5/error_contract_source_review22.md':'6ac1af9df6b555aa34dcb9714c6c43f8dd6345d804577409688ca7ef3557cccc',
 'round22/role3/h1_psi/C5_checkpoint_after_psi05.md':'9119650574a298e229f620623d50c14d7e749d915305ffe0fa459a9dc6c889f7',
 'round22/role3/h1_psi/GammaPsiReflection22.lean':'8e070c18a483ac71703f66b80dbcf4129f0f16ada8f2a933497655b3a7cdaa30',
 'round22/role3/h1_psi/ContourChiPsi22.lean':'a90d536187fe342d01cf913a56c80a34e6846eb273a533bcdd843289f7d83248',
 'round22/role3/h1_psi/ContourChiScaled22.lean':'d0aa03290fe806f9c84c0311a7e07a2fe0737148c9c1de7c80876118fb7a64d7',
 'round22/role3/h1_psi/PsiKernelEnvelope22.lean':'949c6fc0d895003b522518e18ae89bdf6b5062448d5273f146685645afb72ef8',
 'round22/role3/h1_psi/PsiKernelDomination22.lean':'80b85c14c7db79121f7c9cb003edf97a7d5e947f785ce8402f910ea93aad48bc',
 'round22/role3/h1_psi/PsiMixedFubini22.lean':'d143b0fbdf795a1b400f737274a5eae5c8c5bba0c2e4ecaf145d86932df0b250',
 'round22/role1_bridge/contour_formula22.md':'42faea33cdcd56c08f6fb593dbd42c5c293b8e72beb9c823db68e9576ac1edb7',
 'round22/role1_bridge/numeric_precontract22.md':'02cba2d0b3478b5fe3bddb46c1df0862a7c6287452f19892b7cec8ba100db05b',
 'round22/role4/h1_global_numeric/source_contract22.md':'cea359055df1966ece11887305856bed46c24bb6de62f1a052d2e54c0e7d6cec',
 'round22/role4/h1_global_numeric/envelopes_source22.py':'f988d3edbcd28ce40698515f2e608d67a2615ab6bf777e4daf42f0820e8d5e67'}
for path,digest in expected.items():assert sha(B/path)==digest,path
cpp=C/'checkpoint.json';cp=read(cpp)
assert cp['official_auxiliary_validation']['modules']==66 and cp['official_auxiliary_validation']['declarations']==1109
o={'schema':'ROUND22_DELEGATED_SOURCE_AUDITS_ROOT_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'status':'DELEGATED_SOURCE_PAPER_AUDITS_CLOSED_NO_NEW_PASS','bindings':expected,
 'root_FULL_reads':{'C5_review':'317174','error_review':'fab0f9'},
 'C5_delegate_scope':'74 SOURCE declarations coherent on inspection; dependencies and Mellin/Arch/full quantitative contract still open',
 'error_delegate_scope':'Fixed-parameter constants coherent on paper; domain restrictions and actual interval-output requirements recorded',
 'domains_not_promoted':'Continuity Y>0 does not imply uniform W bound; W/C8 use Y>=1, primal tail monotonicity guard, Q integer>=2, R>=2',
 'micro_contour_source':'Separate correction891454 under ROLE3; new Judge batch05 preparation only, no gate or compile yet',
 'numeric_global_run':False,'numeric_global_PASS':False,'official_modules':66,'official_declarations':1109,
 'root_mathematical_judge_invocations':0,'root_compiler_invocations':0,'root_numeric_invocations':0,
 'H1_paid':False,'C3_paid':False,'C5_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_source_audits_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Delegated C5 SOURCE74 and error PAPER audits closed, no new PASS. Fixed thermal constants coherent under explicit domain restrictions; primitive and output certification pending. New Judge Box12->Contour11 source preparation separate, numeric ROLE3 review/ROLE4 launcher writing active. Official66/1109 incldefs unchanged; H1/C3/C5/coefficientN/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
child=subprocess.run([sys.executable,'-B','-X','utf8',helper,'update','--cwd',str(B),'--run-name','parity','--node-id','15.3','--status','running','--insight',insight],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cp['last_progress']=insight;cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==5:actor['status']='SOURCE_PAPER_AUDITS_CLOSED_NEW_BATCH05_BOX_CONTOUR_SOURCE_PREPARATION'
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nDeux revues indépendantes SOURCE/PAPER closes : C5SOURCE74 cohérent à lecture, dépendances et Mellin/Arch encore ouverts ; enveloppes du contrat thermique cohérentes à spécialisationfixée sous restrictions exactes de domaine. W/C8 exigent Y>=1, Eprim décroissance, Q>=2,R>=2 ; continuité ne remplace pas validité des majorants. Tous les budgets exigent des outputs effectifs ; checker structurel ne certifie pas primitives. Nouveau Jugebatch05 Box12→Contour11 en préparation distincte, aucune gate/compilation. Officiel66/1109 inchangé, H1/C3/C5/additif/D_N/WIN ouverts.\n')
print(json.dumps({k:v for k,v in o.items() if k!='bindings'},ensure_ascii=False,indent=2))
