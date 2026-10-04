"""Archive interrupted round21 and install user-directed continuous contract22; metadata only."""
import hashlib,json,sys,subprocess
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round22'; OLD=B/'round21'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def write(p,x): p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode: raise RuntimeError((p.returncode,p.stdout,p.stderr))
    return p.stdout
assert not R.exists(), 'Round22 is a new namespace; no existing experiment overwritten'
R.mkdir()
for d in ('role1','role2','role3','role4','role6','judge'): (R/d).mkdir()
old_registry=read(OLD/'previous_artifacts_sha256.json')
assert isinstance(old_registry,dict)
print('old registry schema',list(old_registry)[:8])
# Shape inspection is metadata only. Existing registry is kept byte-for-byte.
own={str(p.relative_to(B)).replace('\\','/'):sha(p) for p in sorted(OLD.rglob('*')) if p.is_file()}
write(OLD/'controller_interrupted_manifest.json',{'status':'INTERRUPTED_BY_EXPLICIT_USER_PIVOT_NOT_MATHEMATICAL_FAILURE','bindings':own,'files':len(own),'victory':False,'retained_verified_modules':57,'retained_auxiliary_theorems':942,'actual_new_round21_Lean_invocations':0,'actual_new_round21_math_bank_invocations':0,'conservation21_metadata_unique_pass':True})
controller=OLD/'controller_interrupted_manifest.json'
directive='''# Directive utilisateur — boucle22

Le changement de paradigme est définitif pour la recherche à venir. Abandonner les formes bilinéaires, le crible combinatoire, l'inversion de Möbius, les décompositions Vaughan et les estimations scalaires des restes de progressions arithmétiques. Les sources et acquis historiques sont conservés comme archives ; ne pas les réexécuter ni les prolonger.

Explorer un couplage continu topologique, spectral ou géométrique : (1) dualité premiers/zéros des fonctions L, formules explicites Riemann/Weil et corrélations de traces ; (2) transformation globale de formes modulaires ou demi-poids, invariances géométriques exactes sur le demi-plan de Poincaré ; (3) opérateurs globaux et résonances, déterminant de Fredholm, traces de Birman-Krein ou Connes.

Livrable demandé : une identité analytique EXACTE, isolant la contribution arithmétique globale sans heuristique probabiliste ; un contrat numérique falsifiable à N=100000000 avec troncature contrôlée et enveloppe d'erreur fermée, continue, mathématiquement certifiable sous Lean4.

Les hypothèses, modes retirés, termes archimédiens, zéros triviaux, contributions de puissances premières et erreurs de troncature doivent être explicites. Une réécriture en Fourier, une définition d'opérateur dont la trace recopie la réponse, une positivité postulée, RH ou un opérateur de Hilbert-Pólya supposé ne constituent pas un contournement établi. Les identités auxiliaires restent distinctes de la cible D_N. Les notations et acquis des sources demeurent fixés ; seuil source u=logN>=10^24, distinct du test fini.

Ce contrat remplace les méthodes et l'ancienne forme de victoire bilinéaire. Il ne remplace pas le besoin de compilation Lean sans sorry pour une revendication formelle ni les charges du bilan D_N. Aucun résultat nouveau n'est encore exécuté ou certifié.
'''
(R/'USER_DIRECTIVE.md').write_text(directive,encoding='utf-8')
probe='''# PROBE22 — pivot continu demandé par l'utilisateur

Q1 First principles : classe de blocage = représentation et information quantitative manquante. Evidence1 : adjudication20 fcc74721566fe8b373c67b6ac113c3ddf5d9aba0168ceee60fc40e7e2190cd87 constate16modules auxiliaires et absence de paiement global D_N. Evidence2 : propositions21 agent1_signed/agent2_nonfriable gardent respectivement SD/prix globaux et complément/capacité ouverts, avant toute compilation. Le pivot est une instruction opérateur, pas un nouveau résultat mathématique.
Q2 Hidden assumption : la même représentation locale en facteurs et progressions procurerait l'information globale encore manquante. Cette famille est maintenant interdite ; explorer une identité continue avec toutes les contributions de trace et une erreur finie certifiable.
Q3 Elephant : une trace spectrale ou une invariance ne donnent pas gratuitement une information sur les deux premiers couplés. Il faut construire le domaine/opérateur/fonction test, dériver la formule et ses queues, préserver la contribution originale et déclarer les liens au D_N encore absents.
Q4 Hamming : oui, l'axe continu vise une nouvelle source d'information globale. Une simple représentation, un opérateur contenant la réponse ou une hypothèse équivalente à la cible ne satisfont pas le contrat.

IDEATION: deux rapports complémentaires, les trois axes examinés, quatre mouvements et cinq champs par candidat. Lire des sources primaires pour toute formule exacte ou queue proposée ; conserver titre/lien/énoncé/domaine. Ne pas importer RH, simplicité des zéros, auto-adjonction de l'opérateur des premiers, modularité d'une série de premiers ou annulation des arcs sans preuve. Les acquis ne sont pas remis en cause. Le cadre continu demandé n'autorise aucune reprise des méthodes interdites.

EXECUTION: root reste coordinateur seulement. Les agents écrivent les propositions et sources. ROLE6 prépare un protocole neuf strict N=1e8 et critique troncature/erreurs avant toute exécution. Toutes les portes mathématiques/Lean sont initialement fermées. Chaque invocation réelle dispose d'une source figée, captures PREEXEC, commande/log/exit/reçu. Les six rôles se répartissent en vagues dans quatre places, avec Juge indépendant des auteurs. Pas de victoire sur une identité tautologique ou sur une borne globale admise.
'''
(R/'PROBE_BLOCK.md').write_text(probe,encoding='utf-8')
for node in ('13.13','14.6'):
    invoke('update','--node-id',node,'--status','pruned','--insight','Interrupted before any new mathematical or Lean invocation by explicit definitive user continuous pivot22. Sources preserved uncompiled, not a numerical/Lean/mathematical FAIL. Local sieve/bilinear/AP methods prohibited going forward; no victory.')
invoke('meta','--set','eval_cmd="'+sys.executable+'" -B -X utf8 "'+str(R/'judge/run_once.py')+'"','--set','dataset_info=ROUND22 definitive continuous spectral/modular/operator user pivot; banned bilinear/combinatorial sieve/Mobius inversion/Vaughan/scalarAP remainders; exact analytic identity and N1e8 controlled truncation/closed continuous error contract; sourceu>=1e24;57modules942aux/noWin; all gates closed')
obs={'status':'ROUND22_USER_PIVOT_INSTALLED_ALL_EXECUTION_GATES_CLOSED','created_utc':datetime.now(timezone.utc).isoformat(),'directive_sha256':sha(R/'USER_DIRECTIVE.md'),'probe_sha256':sha(R/'PROBE_BLOCK.md'),'interrupted21_controller_sha256':sha(controller),'round21_own_files_frozen':len(own),'old3028_registry_sha256':sha(OLD/'previous_artifacts_sha256.json'),'root_fresh_constraints_full_chunk':'1489d7','root_ideation_skill_full_chunk':'37af85','root_metadata_cli_failures':['0c368d unsupported --run-dir, exit1','4679e0 missing UTF8 output, exit1'],'root_metadata_cli_correction':'1489d7 correct --cwd/--run-name and -X utf8 exit0','actual_actor_interrupts':{'round21_formal3_prepare':'running interrupted','round21_ideation1_signed':'running interrupted','round21_numeric_conservation':'running interrupted'},'proof_or_numeric_execution_authorized':False,'victory':False}
write(C/'messages/round22_pivot.json',obs)
cp=read(C/'checkpoint.json'); cp.update(phase='ROUND22_USER_PIVOT_CONTINUOUS_IDEATION_AND_TRUNCATION_PREPARATION_ONLY',current_nodes=[],in_flight_executors=[],required_user_input=None,external_blocker=None,objective_complete=False,victory=False)
cp['last_progress']='Explicit user definitive continuous pivot22:21 interrupted before new Lean or mathbank; all21 drafts frozen, old57/942 unchanged. Prohibit bilinear/combinatorial sieve/Mobius inversion/Vaughan/scalarAPremainder goingforward. New exact spectral/modular/operator analytic identity with closed continuous truncation error atN1e8 required. Freshconstraints1489d7/strictideation37af85, rootmetadataonly, all executiongatesclosed.'
cp['next_focus']='Continuous exact spectral/modular/operator identity and independently falsifiable controlled truncation; no implicit RH/modularity/operator positivity or target-equivalent premise.'
cp['previous_goal_turn_evidence']+=['round21/controller_interrupted_manifest.json','round22/USER_DIRECTIVE.md','round22/PROBE_BLOCK.md','.arbor/sessions/parity/.coordinator/messages/round22_pivot.json']
write(C/'checkpoint.json',cp)
report=B/'REPORT.md'; txt=report.read_text(encoding='utf-8')
start=txt.index('**Boucle21 en cours :**'); stop=txt.index('**Boucle20 close :**',start)
txt=txt[:start]+'''**Boucle22 — pivot continu actif :** sur directive explicite de l'utilisateur, les méthodes bilinéaires, de crible combinatoire, d'inversion de Möbius, de Vaughan et d'estimation scalaire des restes AP sont abandonnées pour la suite. Les travaux21 ont été interrompus avant toute compilation ou exécution mathématique nouvelle ; leurs sources restent archivées sans validation. Les57modules/942conclusions historiques restent les seuls comptes certifiés. La recherche vise maintenant une identité analytique exacte spectrale, modulaire ou opératorielle avec troncature contrôlée à N=10^8 et enveloppe d'erreur fermée, continue, certifiable sous Lean4. Aucune nouvelle identité n'est encore sélectionnée, exécutée ou validée. [Directive](round22/USER_DIRECTIVE.md), [contrat de phase](round22/PROBE_BLOCK.md).

'''+txt[stop:]
report.write_text(txt,encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
