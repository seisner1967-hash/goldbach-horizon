"""Coordinator checkpoint only: report/tree/byte preservation metadata."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round22'
def load(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
registry=load(R/'previous_artifacts_sha256.json')
assert registry['file_count']==len(registry['sha256'])==3089
for rel,expected in registry['sha256'].items(): assert sha(B/rel)==expected,rel
tree=load(C/'idea_tree.json'); old=tree['nodes']['ROOT']['insight']
oldtail='Les rôles1/2 explorent,6 critique le contrat numérique ;3/4 et5 indépendant viendront en vagues. Aucune nouvelle identité sélectionnée/exécutée/certifiée ; objectif actif sans blocage externe.'
newtail='FINAL1/2 papier gelés ;15.2 trace réelle premiers-zéros et16.1 déroulement modulaire Epstein sélectionnés réellement. ROLE3/4 écrivent les preuves en sources seulement, ROLE6 prépare un banc géométrique24cas et ses racines dyadiques96bits. Aucun math22/Lean22/PASS22 exécuté ou autorisé. Import analytique standardLSeries différé horsG0. Domaines opérateurs, formule Weil/comptagezéros, évaluateursΓ/ζ, coefficientN et raccordD_N restent des obligations distinctes ; objectif actif sans blocage externe.'
assert oldtail in old
p=subprocess.run([sys.executable,'-B','-X','utf8',r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py','update','--cwd',str(B),'--run-name','parity','--node-id','ROOT','--insight',old.replace(oldtail,newtail)],capture_output=True,text=True,encoding='utf-8')
assert p.returncode==0,(p.stdout,p.stderr)
report=B/'REPORT.md'; text=report.read_text(encoding='utf-8')
needle='Aucune nouvelle identité n\'est encore sélectionnée, exécutée ou validée.'
replacement='Deux propositions papier sont maintenant gelées et sélectionnées : trace réelle premiers–zéros (15.2) et déroulement Epstein du réseau complet (16.1). ROLE3/4 préparent leurs preuves sans compiler ; ROLE6 prépare24cas géométriques, dont6 à y=10000, avec racines à encadrement dyadique96bits et queue fermée positive. Aucun banc ou module22 n\'a encore été exécuté ou validé. L\'identification opérateur, les producteurs Gamma/zêta certifiés, le coefficient global à N et le raccord D_N restent ouverts.'
assert text.count(needle)==1
report.write_text(text.replace(needle,replacement),encoding='utf-8')
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'protected_files_checked':3089,'protected_registry_sha256':sha(R/'previous_artifacts_sha256.json'),'scope':'BYTE_METADATA_ONLY_NOT_MATH_CONSERVATION_REPLAY','FULL_role3_api':'abb629','FULL_role3_preparation_and_artifacts':'e28ef4','FULL_role3_inputmanifest':'32ee53','FULL_role3_readreceipts':'ef6ff3','role3_old_draft_bank_binding':'Historical read hash only, changed source requires new FINAL reading before PREEXEC','ROLE4_actual_agent':'/root/round22_formal4_trace','math22_invocations':0,'Lean22_invocations':0,'official_verified_modules':57,'official_verified_auxiliary_theorems':942,'win':False}
(C/'messages/round22_sources_checkpoint.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
