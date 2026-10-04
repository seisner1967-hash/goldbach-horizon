"""Record the actually closed independent round18 and next intake; metadata only."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from hashlib import sha256
import json, subprocess
B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B/'.arbor/sessions/parity/.coordinator'
H = Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p): return json.loads(p.read_bytes())
def invoke(cmd,*args):
    r = subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if r.returncode: print(r.stdout,r.stderr); raise SystemExit(r.returncode)
m = read(B/'round18/controller_manifest.json')
mh = sha256((B/'round18/controller_manifest.json').read_bytes()).hexdigest()
assert mh == 'ce00517b1df6f4fc89f27667be44dd7f2c4d3331c8022fd14e4c505392175c5c'
assert m['next_protected_artifacts_expected'] == 1361 and not m['victory']
tree = read(C/'idea_tree.json')
assert tree['nodes']['13.10']['status'] == tree['nodes']['14.3']['status'] == 'running'
notes = {
 '13.10': ('agent1_calibrated_typeii.md','role3/SeparatedTypeIILower.lean',
  'Independent FINAL18 validates four TypeII modules: actual product-incidence bijection, weighted calibration retaining the entire old sum in its price, exact Mobius/CRT floor fronts, and R5 under independent arithmetic guards. No candidate-primality filter or availability assumption. Complete finite d91 progression 109890 integers /196 structural beta /8441 theta /9 raw proper powers, 57189 actual products with analytic multiplicities. Distinct CRT annex independently checks all1944 CRT equations, J23185/JR234, R4a false R4b true R4c false so R5 is not applied. Calibrated H*ell has JR0 and fails coprimality. Source R4/R6, structural nonvacuity, whole weighted Gamma, true theta prices and D_N remain unestimated; valid auxiliary statements, no global NoGo or Win.'),
 '14.3': ('agent2_capacity_incidence.md','role4/DividedSelbergBridge.lean',
  'Independent FINAL18 validates four double-extraction modules: actual prime quotients/CRT representation, divided affine forms and actual Delta, derived root counts with rho1 at witnesses/rho4 only off Delta, actual Mobius Selberg weights and finite upper bound retaining all remainders. Lower G remains conditional on independent prime-log input and explicit scale/unsaturation guards. Complete finite5001q/333prime/22SFunitcores/7326axes has A258 R32 S674=SS40+634; 286 actual divided switches/68 physicalvertices54active14zero and2 old anchors are preserved without extra capacity. SS-to-rough source fronts, Mertens/totient, uniform CRT+1, allparameter D5/D10/D11 and written onset1e36 vs source1e24 are not Lean-certified. T_A, S minus SS, unique assignment/fullGamma/globalledger remain unpaid. Eight fresh modules together add170 auxiliary thm; no parityWin.')}
for node,(report,code,insight) in notes.items():
    invoke('record','--node-id',node,'--report-file',str(B/'round18'/report),'--score','0','--insight',insight,
           '--result','Actual independent FINAL18 verifies auxiliary conditional arithmetic; whole parity bypass and D_N target remain open.',
           '--code-ref',str(B/'round18'/code))
head = ('FINAL18 closed: one actual independent audit exit0, eight fresh Lean PASS, 170 theorems /68 defs /4 structures /242 standard-axiom prints. Cumulative30 modules507 auxiliary theorems, no victory. Exact997 archives and267 frozen inputs/22 historical dependencies preserved,91 Judge-owned bindings/10 closure bindings checked. Controller18 binds363+self364 for next1361, SHA'+mh+'. Numeric320 stored positions191POS83NEG46ZERO; original3canonical invocations with one encoding failure and2 unique replays, distinct CRT1canonical0replay/1944 checks. Authors23 Lean invocations15 technical failures, no Judge failure or continuation, sole benign Count warning. Actual R5/CRT and actual divided G are proved with their independent premises. R6 source application, D5/D10/D11 analytic conversion/rough bridge/uniform errors/allparameter aggregation, onset1e24..1e36 and whole Gamma/unique capacity/T_A/S remainder/full D_N remain open. Root only read receipts/sources/logs and metadata; one root metadata KeyError corrected with honest POSTEXEC capture, not mathematical failure. A7 and fixed acquis unchanged.\n')
tail = ('\nNext19: seek an actual new quantitative estimate for the entire weighted signed cofactor aggregate with all literal calibration prices, or a quantitative mechanism covering the remaining non-SS family and physical capacity assignment. A stronger SS estimate alone cannot pay the entire residue. Do not spend another iteration rederiving acquired product bijections, Mobius/CRT fronts, generic Gram identities, divided roots, finite Selberg weights or the same local adversarial counterexample. Source R4/R6 formalization is a possible bounded subtask, but its conditional local result is not a parity Win. Keep all1361 archives immutable, source u>=10^24 and the full fixed ledger. New concept selection and new mathematical bank require fresh constraints. No target-equivalent, availability or aggregate-bound premise may be promoted to victory.')
invoke('update','--node-id','ROOT','--insight',head+tree['nodes']['ROOT']['insight']+tail)
invoke('meta','--set','eval_cmd="'+sys.executable+'" -B -X utf8 "'+str(B/'round18/judge/run_once.py')+'"',
       '--set','dataset_info=FINAL18 actualaudit0/fresh8LeanPASS;267inputs/22deps/320storedsigns;8modules170thm68defs4structures;cumul30/507;R5 independentguards and actualG conditional;R6/D5/D10/D11/wholeGamma/fullledger open;sourceu>=10^24;next1361;noWin;19intake')
p = C/'checkpoint.json'; cp = read(p)
cp.update(phase='ROUND18_COMPLETE_ROUND19_INTAKE',rounds_completed=18,current_nodes=[],in_flight_executors=[],objective_complete=False,victory=False,
    last_judge_receipt='round18/judge/final_receipt.json',last_controller_manifest='round18/controller_manifest.json',
    last_controller_manifest_sha256=mh,next_protected_artifacts_expected=1361,next_protected_registry_pending=None,
    next_focus='Estimate entire weighted Gamma with actual prices, or cover non-SS cofactor remainder with physical unique capacity.',
    previous_goal_turn_classification='progress',external_blocker=None,last_progress=head.strip())
cp['retained_verified_modules'] += ['round18/'+n for n in ['SeparatedTypeII','SeparatedTypeIIPrice','SeparatedTypeIICount','SeparatedTypeIILower','DoubleExtractionArithmetic','DividedFourForms','DividedRootCounts','DividedSelbergBridge']]
cp['previous_goal_turn_evidence'] = list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/agent5.md','round18/judge/manifest.json',
    'round18/judge/final_receipt.json','round18/judge/closure_receipt.json','round18/judge/audit_receipt.json','round18/judge/launch_receipt.json',
    'round18/controller_manifest.json','.arbor/sessions/parity/.coordinator/messages/round18_feedback.md',
    '.arbor/sessions/parity/.coordinator/messages/round18_judge_start_root_failed01.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
feedback = '''# Feedback18 figé pour la prochaine idéation

Le Juge a exécuté un audit indépendant unique, exit0, et huit compilations neuves chacune une fois. 170 théorèmes,68 définitions,4 structures,242 prints d'axiomes standards ; cumul30 modules507 théorèmes auxiliaires. Count garde un seul warning push_cast inactif. Les15 invocations Lean échouées sur23 chez les auteurs sont techniques, pas15 découvertes d'obstruction de parité. Le finalizer ROLE3 a omis cinq prints sans axiomes, puis a été corrigé sans compilation. La racine a corrigé un KeyError de son lecteur de gate ; capture POSTEXEC honnête. Aucun échec ou continuation du Juge, aucun stage PASS rejoué. Aucun Win ni NoGo global.

TypeII : conserver la bijection des produits effectifs, les caps physiques, les coefficients construits avant theta, E complet et la convention d'unité exacte. R5 est acquis sous gardes R4 indépendantes ; A>0 est structurel, sans hypothèse de partenaire premier. L'application source R4/R6, sa non-vacuité avec d croissant et le passage à Gamma première ne sont pas acquis. N=10^8 est seulement une boussole :109890 entiers,196beta,8441theta,9rawproperpowers,57189 couples. Les multiplicités analytiques ne créent pas de nouvelles capacités physiques. Garder les prix theta/II/II_raw/raw distincts et entiers.

Annexe CRT distincte :972 diviseurs H et1944 diviseurs K, toutes mu=0 retenues ;1944 congruences/floors vérifiées. J23185/JR234, R4a/R4b/R4c=faux/vrai/faux, donc R5 non appliqué malgré deux comparaisons finies vraies. H*ell donne J21077/JR0 et détruit l'ancienne coprimalité. La calibration annule le témoin et déplace toute l'ancienne somme dans son prix. Une première pondération produit égale zéro n'implique pas Gamma(theta)=0. Le nouvel objectif doit estimer l'agrégat complet avec tous les prix, pas une seule fibre ni un mode chi.

Double extraction SS : quotients premiers et minFac réels, ell0 distinct de p0, ell1 peut être p0 ; vraies divisions/CRT, Delta et ses facteurs. Rho1 aux témoins et rho4 seulement hors Delta sous gardes de primitivité dérivées. Saturation vide. Vrais poids Mobius/Selberg et restes entiers ; G>=P(y)^4 collisionLoss/2 garde l'input indépendant de somme première et les gardes de troncature. Rien d'équivalent à D_N n'a été ajouté comme prémisse.

Les raccords SS vers roughCell aux fronts physiques, prime-log analytique/Mertens/totient, Delta uniformément majoré, erreur CRT+1 à tous paramètres et D5/D10/D11 restent non certifiés sous Lean. Budget SS écrit seulement u>=10^36, source fixé u>=10^24 ; segment intermédiaire non payé. L'amélioration du crible SS peut combler ce gap local, mais seule ne paie pas S hors SS, T_A ou le ledger. Le nouveau mécanisme doit couvrir la famille restante ou donner une estimation entière de Gamma. Une nouvelle identité générique de norme, racines ou calibration déjà acquise ne suffit pas.

Banque SS complète :5001 entiers q,333 premiers,22 cœurs SF unitaires,7326axes ; A258/R32/S674=SS40+634.286 triplets divisés,68 sommets physiques54 kernels actifs14axes m0 zéro. m0=p0q a rawLambda=0 ; les2 ancres m1 existantes ne créent pas de capacité supplémentaire. W/D et wholeU_a stricts restent figés.320positions stockées191POS83NEG46ZERO sont des positions de certificats, pas320 expériences indépendantes. Une seule annexe CRT sans nouveau signe ni replay.

Préservation :997 archives avant18 ; controller18 lie363pièces et lui-même, prochain1361. Interdit de modifier les acquis, de rejouer les banques/anciens Lean/PASS/PDF/W/D/logs ou signes sans une nouvelle raison précise. Garder rawLambda_N sans mu², cofacteurs longs/k1/c1/b1/e1/axes physiques et fronts, vrais S(bN), principal -S(N)N, sourceu>=10^24, A7 canonique sous C2 acquis. Ledger fixé : D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0). P5K2/J2 sur le bloc entier avant retrait ; ne pas double payer avec U4. Score0 de cette itération ne signifie pas que les mécanismes valides partiels sont faux.
'''
(C/'messages/round18_feedback.md').write_text(feedback,encoding='utf-8')
p = B/'REPORT.md'; txt = p.read_text(encoding='utf-8')
txt = txt.replace('point de recherche du 2 octobre 2026','point de recherche du 3 octobre 2026',1)
txt = txt.replace('au cours de dix-sept boucles','au cours de dix-huit boucles',1)
txt = txt.replace('Vingt-deux fichiers Lean ont été compilés puis reconstruits indépendamment, avec337 conclusions auxiliaires distinctes',
    'Trente fichiers Lean ont été compilés puis reconstruits indépendamment, avec507 conclusions auxiliaires distinctes',1)
txt = txt.replace('La boucle17 ajoute cinq modules et93 théorèmes',
    'La boucle18 ajoute huit modules et170 théorèmes sur les incidences TypeII, leurs prix, les fronts CRT et les formes divisées du switch SS, avec les hypothèses quantitatives restantes explicites. La boucle17 ajoute cinq modules et93 théorèmes',1)
txt += '''
### Clôture indépendante18 : huit modules valides, contournement global non établi

Le Juge a recompilé les huit nouveaux fichiers Lean, chacun une fois, sans sorry ni erreur. Les170 théorèmes,68 définitions et4 structures ont242 prints d'axiomes vérifiés ; seul Count comporte le warning prévu d'une tactique push_cast inactive. Le cumul atteint30 modules et507 théorèmes auxiliaires. L'audit unique s'est achevé à23:02:52UTC avec exit0, puis sa clôture metadata avec exit0. Aucun stage PASS, ancienne compilation ou producteur numérique n'a été relancé.

Les identités TypeII portent sur les produits et incidences réels ; leur calibration conserve le prix entier. L'inclusion Möbius et les fronts CRT dérivent le minorant R5 sous des gardes arithmétiques indépendantes. L'annexe vérifie1944 cas : J23185/JR234, deux gardes suffisantes fausses, donc aucune application R5 au N fini. Le passage source R4/R6, la non-vacuité structurelle, l'estimation de Gamma entière et ses prix restent ouverts.

La double extraction SS construit les quotients, les quatre formes divisées, leur discriminant arithmétique, les racines effectives et les poids Selberg. Son minorant de G reste conditionnel à un input analytique indépendant. Les fronts source, la conversion Mertens/totient, CRT+1 uniforme et la sommation de tous les paramètres D5/D10/D11 ne sont pas certifiés. Le seuil SS écrit10^36 laisse un segment au-delà du seuil source10^24 ; S hors SS, T_A et l'assignation unique des capacités restent impayés. Le ledger global de D_N n'est pas fermé ; aucune victoire.

Les banques complètes à N=10^8 sont figées : TypeII109890entiers et57189produits ; SS5001entiers/333premiers/22cœurs/7326axes, A258/R32/S674=SS40+634,286switches divisés et68sommets54actifs14zéro. Les320 positions de certificat (191 positives,83 négatives,46 nulles) sont conservées. L'annexe CRT a une invocation canonique et zéro rejeu. Les15 échecs Lean auteurs sont des diagnostics techniques conservés, sans obstruction logique de parité inventée.

La racine a lu les rapports/sources/journaux/reçus et vérifié267 inputs,22 dépendances,91 pièces du Juge,10 bindings de clôture,242 axiomes et997 archives ; son contrôle reste limité aux métadonnées et certificats stockés. Le controller18 lie363 pièces et lui-même ;1361 archives sont protégées pour la suite. SHAcontroller18 : '''+mh+'''. Nodes13.10/14.3 done0 ; les résultats auxiliaires restent acquis. La prochaine idéation doit viser une estimation quantitative entière ou une famille encore non couverte.

Pièces : [TypeII et gardes R5](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/role3/SeparatedTypeIILower.lean), [switch divisé Selberg](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/role4/DividedSelbergBridge.lean), [rapport du Juge18](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/agent5.md), [controller18](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/controller_manifest.json).
'''
p.write_text(txt,encoding='utf-8')
print('ROUND18_RECORDED; next1361; no compiler, audit or numeric producer executed')
