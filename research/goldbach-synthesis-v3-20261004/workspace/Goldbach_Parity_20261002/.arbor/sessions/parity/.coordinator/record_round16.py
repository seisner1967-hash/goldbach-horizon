"""Record completed FINAL16 evidence and feedback, without numerical or Lean execution."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from hashlib import sha256
import json, subprocess
BASE = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
COORD = BASE / '.arbor/sessions/parity/.coordinator'
HELPER = Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p): return json.loads(p.read_bytes())
def invoke(command,*args,quiet=False):
    p = subprocess.run([sys.executable,'-B','-X','utf8',str(HELPER),command,'--cwd',str(BASE),'--run-name','parity',*args],
                       capture_output=True,text=True,encoding='utf-8')
    if not quiet or p.returncode: print(p.stdout,end='')
    if p.stderr: print(p.stderr,end='',file=sys.stderr)
    if p.returncode: raise SystemExit(p.returncode)
c = read(BASE/'round16/controller_manifest.json')
assert c['round']==16 and c['victory'] is False and c['no_test_reexecution_by_controller']
h = sha256((BASE/'round16/controller_manifest.json').read_bytes()).hexdigest()
assert h=='10d9f68fc649d965aa5eecac96fecf5fd20f705527d42f52b855662acec02332'
count=len(c['bindings_sha256'])+1; total=701+count
assert count==98 and total==799
tree=read(COORD/'idea_tree.json')
assert tree['nodes']['13.8']['status']==tree['nodes']['14.1']['status']=='running'
notes={
 '13.8':('agent1_bilinear_covariance.md','typei_checks.py',
  'FINAL16 Judge confirms real fixed d77 TypeI3 bias: uniform drift38, corrected2, difference36; beta216/classes0,106,110 over full129870integers51948units. Written BMOR AP3 correction E3 and positive drift bound valid only at both endpoints>=8e9, never applied to N1e8. Exact Gamma=Gamma_star+L3 and literal principal L3=-1/4 uniform retained; parents also3rough. Nine rawproperpowers preserved. Local correction is a valid partial reduction; Gamma_star, other TypeI/TypeII and true parent comparison unestimated. Complete bank1+unique existing replay identical. Narrow exactuniformcentering false, no global impossibility or parityWin.'),
 '14.1':('agent2_or_incidence.md','role3/EulerAnchor.lean',
  'FINAL16 independent fresh Lean compiles validate actual canonical p0 odd prime absent N, all smaller odd primes divide N, real tprod convergence/tail and Euler/harmonic prefix, yielding actual S(N)-logp0>=1/144 for nonzero even N under acquired lower C2 enclosure only. New36theorems8defs in two modules, cumul17/244, standard axioms no sorry. Written A9 C<=-1/288 at U4 not Lean-certified; source first-prime availability and global capacity unestimated. Complete18q34cores612vertices128profiles/484exactzeros,95primeincidences e1zero/e3three. Entire principal deficitPOS both endpoints/actualsumPOS; no free resource reuse or erasedLambda(e). Finite A9 no counterexample only, source onset preserved. A7 genuine partial arithmetic gain retained; no globalD_N or Win.')}
for node,(report,code,insight) in notes.items():
    invoke('record','--node-id',node,'--report-file',str(BASE/'round16'/report),'--score','0',
           '--insight',insight,'--result','Validated partial arithmetic result; independent FINAL16 audit passed; quantitative incidence remains open; no victory.',
           '--code-ref',str(BASE/'round16'/code),quiet=True)
head=(
 'Goal active, no victory. FINAL16 independent unique audit exit0;78 frozen inputs/five FINALroles,30numericbindings/two full existing identical copies,1879strict rational signpositions654POS95NEG1130ZERO; four localfalsifiers and one finiteNOCEX. Two fresh new Lean modules36theorems8defs, cumul17/244 standardaxioms/no sorry/error/warning. Actual canonical leastmissingoddprime p0 and actual singularSeries margin S(N)-logp0>=1/144 certified under acquired2541/4096<=C2 only; real tprod convergence/tail/Euler-harmonic relation proved, no free S or margin assumption. A9 signed bracket sourceU4 written only, prime incidence availability remains unestimated. Complete capacity bank18q34cores612vertices128profiles,95incidences/e1zero/e3three, wholeprincipaldeficitPOS/endpoints actualsumPOS, no erasedLambdae or duplicatedcapacity. TypeI3 d77 bank129870integers51948units216beta0/106/110, uniformdrift38 corrected2 literaldifference36; Gamma/Gamma_star/L3 NEGfinite, nine rawproperpowers retained. Written AP3 valid at endpoints8e9/sourceU4 only; finite1e8 test notsourceonset. Gamma_star/TypeII/parentscomparison/F6/unioncapacity/wholeD_N unestimated. Nine real technical exit1 Leanproducerattempts documented (oneAPIprobe/eightcandidatefailures), no parityfailure invented; twofreshJudgecompilesexit0.701oldpreserved, controller16 binds97+self98 SHA'+h+'; nextprotected799. Coordination threadlimit/pendinginit resolved by successfulfreshJudge and finalization, no external blocker.\n')
old=tree['nodes']['ROOT']['insight'].split('\nNext16 must seek')[0]
tail='\nNext17 must seek genuinely quantitative control of calibrated weighted Gamma_star/TypeII or many real favorable incidences after global physical union. Keep A7 as acquired; do not rederive its harmonic/tail proof. No postulated prime availability, density, orphan bound or target D_N bound; no generic local-fee/projection lemma as bypass. Candidate firstaxis TypeII product and complementfactor ranges remain distinct. All799 artifacts immutable; new bank only after new exact candidate selection.'
invoke('update','--node-id','ROOT','--insight',head+old+tail,quiet=True)
invoke('meta','--set','eval_cmd="'+sys.executable+'" -B -X utf8 "'+str(BASE/'round16/judge/launch-audit-once.py')+'"',
       '--set','dataset_info=FINAL16 observed unique audit exit0;78inputs30numericbindings2identicalcopies1879signs;2newmodules36thm8defs;cumul17/244;canonical actual A7 acquired;global incidence open;sourceu>=10^24;nextprotected799;noWin;17intake',quiet=True)
checkpoint=read(COORD/'checkpoint.json')
checkpoint.update(phase='ROUND16_COMPLETE_ROUND17_INTAKE',rounds_completed=16,current_nodes=[],in_flight_executors=[],
    objective_complete=False,victory=False,last_judge_receipt='round16/judge/judge_receipt.json',
    last_controller_manifest='round16/controller_manifest.json',last_controller_manifest_sha256=h,
    next_protected_artifacts_expected=799,next_protected_registry_pending=None,
    coordination_incident='Resolved: fresh Judge completed one audit after roles finalized; old failed dispatches launched no audit.',
    next_focus='Quantitative calibrated covariance or actual incidence capacity after global union, using canonical A7 as acquired.',
    previous_goal_turn_classification='progress',external_blocker=None,last_progress=head.strip())
checkpoint['retained_verified_modules']+=['round16/LeastMissingPrimeMargin','round16/EulerAnchor']
checkpoint['previous_goal_turn_evidence']=list(dict.fromkeys(checkpoint['previous_goal_turn_evidence']+[
    'round16/agent3_formalisation.md','round16/role3/EulerAnchor.lean','round16/role3/final_receipt.json',
    'round16/agent6.md','round16/numeric_manifest.json','round16/role6_final_receipt.json','round16/agent5.md',
    'round16/judge/judge_receipt.json','round16/judge/audit_launch_receipt.json','round16/controller_manifest.json',
    '.arbor/sessions/parity/.coordinator/messages/round16_feedback.md']))
(COORD/'checkpoint.json').write_text(json.dumps(checkpoint,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
feedback='''# Feedback16 gelé — acquis et obligations pour17

A7 est désormais acquis sous Lean sur les définitions réelles : N pair non nul, p0 premier impair minimal absent, enclosure acquise2541/4096<=C2, S(N)-logp0>=1/144. Convergence tprod, queue et Euler/harmonique sont prouvés ; ne pas les redériver. A9 C<=-1/288 sous le raccord source U4 reste écrit seulement. L'existence et la masse des incidences q,N-p0q premières ne sont pas prouvées. Une famille vide apporte0 ; aucun coût global n'est payé par le seul signe local.

TypeI3 : centrage uniforme exact réfuté ; correction locale3/481 contre2/481 dans le banc d77, défaut38 devient2 et la différence36 reste réelle. Écriture Gamma=Gamma_star+L3, prix principal L3=-1/4 du terme uniforme, parents eux aussi3rough. Les hypothèses TypeII concernent le produit du candidat j, pas automatiquement les facteurs d*s*q du complément. Gamma_star/TypeII/comparaison parent restent ouverts. BMOR pi_AP3 exige les deux endpoints>=8e9 ; aucun usage asymptotique sur le banc1e8.

Capacité : banc entier18q34cores612vertices, branches e1 et primeLambda(e) gardées, trois incidences e3 favorables mais déficit entier principal/actuelPOS. Consommer la capacité de chaque vertex physique une seule fois. Les labels ne sont pas de nouvelles ressources. Trois falsifiers locaux additionnels réfutent la gratuité, la suppression de Lambda(e) et le recyclage multiple. NOCEX sur trois points e3 n'est pas une preuve de disponibilité source.

Neuf échecs Lean réels archivés :1API indisponible,2réduction/coercions/commutation/induction,3dénominateur,5sup/lambda/cast,6numéral,7if/API,8indices,10petitsFinsets,12if dépendant. Ils sont techniques ; n'inventer aucun message de parité. Producteur3:13invocations dont1probe+12candidats, PASS4/9/11/13; producteur4:1PASS; Juge:2compiles frais PASS. Aucun numericfailure16. Cumul17modules244théorèmes auxiliaires, huit définitions nouvelles séparées. Aucune victoire.

Ledger, I global/sourceu>=10^24, rawproperpowers, wholeU_a, originalalpha/Q, S(bN), c1/e1/b1, cofacteurs longs, référence-S(N)N, restes J0/J1/J2, faces/nonbulk, P5K2 entier avant retrait et onset BV supplémentaire restent conservés.799 artefacts protégés pour17. Audit16 unique terminé, aucun rerun producteur/Lean ancien/PASS/PDF par root ; aucune hypothèse d'indépendance ou disponibilité ajoutée.
'''
(COORD/'messages/round16_feedback.md').write_text(feedback,encoding='utf-8')
report_path=BASE/'REPORT.md'; report=report_path.read_text(encoding='utf-8')
report=report.replace('au cours de quinze boucles','au cours de seize boucles',1)
report=report.replace('Quinze fichiers Lean ont été compilés puis reconstruits indépendamment, avec208 conclusions auxiliaires distinctes',
                      'Dix-sept fichiers Lean ont été compilés puis reconstruits indépendamment, avec244 conclusions auxiliaires distinctes',1)
report=report.replace('La boucle13 ajoute deux modules et39 théorèmes',
                      'La boucle16 ajoute deux modules et36 théorèmes : une marge canonique1/144 sur la vraie série singulière est certifiée sous l’enclosure C2 acquise ; l’incidence quantitative reste ouverte. La boucle13 ajoute deux modules et39 théorèmes',1)
report+='''
### Clôture indépendante16 : marge canonique acquise, incidence globale ouverte

**Deux nouveaux modules Lean recompilés par le Juge, sans sorry, erreur ni avertissement. Aucune victoire.** Pour N pair non nul et p0 le vrai premier impair minimal qui ne divise pas N, le théorème `GoldbachRound16.Anchor.canonical_least_missing_prime_margin` établit S(N)-log p0>=1/144 sous la seule enclosure C2 acquise. Le produit infini réel, sa queue et sa relation au produit eulérien/harmonique sont prouvés ; la conclusion n'est pas substituée par une hypothèse. Les petits cas utilisent l'enclosure ; p>=13 n'en dépend pas. A9 et ses gardes source demeurent écrits et non compilés.

La minoration ne donne pas la masse des incidences q,N-p0q premières. Le nouveau banc complet de capacité à N=10^8 conserve tous les34 cœurs sur18q,612 vertices,128 profils et484 zéros exacts :95 incidences, zéro e1 et trois e3. Le déficit principal entier aux deux endpoints et la somme réelle entière sont positifs. Le centrage TypeI3 uniforme est réfuté ; la correction conserve son prix exact et ne paie pas Gamma_star/TypeII. Quatre falsifications locales, une promotion sans contre-exemple fini,1879 positions de signes stricts654POS/95NEG/1130ZERO, aucun flottant ni signe irrésolu. Les deux copies isolées existantes sont identiques sans relance.

Neuf vrais exit1 Lean techniques sont archivés avec leur source et leur journal ; aucun diagnostic analytique de parité n'est inventé. Les36 théorèmes nouveaux et huit définitions sont comptés séparément, pour17 modules et244 conclusions auxiliaires. Les cinq FINAL et78 inputs sont gelés,30 bindings numériques vérifiés. Audit unique exit0 et deux nouvelles compilations indépendantes exit0. Les anciens701 fichiers et PDF/ZIP originaux sont conservés ; controller16 lie97 pièces et lui-même, portant le prochain inventaire à799. SHA controller16: '''+h+'''. Les nodes13.8/14.1 sont enregistrés done0 ; les deux mécanismes valides sont conservés avec leurs obligations ouvertes.

Les mentions antérieures « en attente » de cette boucle décrivent les observations avant le gel ; tous les rôles16 sont maintenant FINAL. Le problème de dispatch a été résolu avant l'audit. La suite cherche une estimation quantitative de Gamma_star/TypeII ou de la capacité d'incidences après union globale. La cible D_N<=N/(256 logN loglogN) reste non démontrée.

Pièces : [EulerAnchor.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round16/role3/EulerAnchor.lean), [LeastMissingPrimeMargin.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round16/role4/LeastMissingPrimeMargin.lean), [Juge16](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round16/agent5.md), [manifeste root](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round16/controller_manifest.json).
'''
report_path.write_text(report,encoding='utf-8')
print('ROUND16_RECORDED; next protected799; no mathematical tests, compiler or Judge invoked')
