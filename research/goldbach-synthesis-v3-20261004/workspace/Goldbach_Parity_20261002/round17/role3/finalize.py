from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, re, sys
sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
R = W.parents[1]
SRC = W / 'SelbergFourForms.lean'
REPORT = W.parent / 'agent3_formalisation.md'
OUT = W / 'final_receipt.json'
assert not OUT.exists(), 'FINAL receipt already frozen'
def sha(p):
    p = Path(p)
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''): h.update(block)
    return h.hexdigest()
src = SRC.read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', src)
receipt = json.loads((W/'build_receipt.json').read_text(encoding='utf-8'))
rows = receipt['attempts']
last = rows[-1]
assert last['exit_code'] == 0
assert last['source_sha256'] == sha(SRC) == last['snapshot_sha256']
for row in rows:
    assert sha(row['snapshot']) == row['snapshot_sha256']
    assert sha(row['log']) == row['log_sha256']
log = Path(last['log']).read_text(encoding='utf-8')
assert ': error:' not in log and ': warning:' not in log and 'sorryAx' not in log
theorems = re.findall(r'^(?:lemma|theorem)\s+(\w+)', src, re.M)
defs = re.findall(r'^def\s+(\w+)', src, re.M)
names = theorems + defs
assert all('GoldbachRound17.Selberg.'+n in log for n in names)
failures = [r for r in rows if r['exit_code'] != 0]
passes = [r['attempt'] for r in rows if r['exit_code'] == 0]
root_src = R/'round17'/'role4'/'FourFormRoots.lean'
root_obj = root_src.with_suffix('.olean')
assert sha(root_src) == '49cbf93fd8eb9aa75236419d5d7b95e1841d67571865171115ffbbdfcb71e9fa'
assert sha(root_obj) == '4a13fc20feabfd5ff552f5dbd18c99c6b66bcfe1a65a3f44fff555417d7b4021'
report = f'''# Boucle 17 — Selberg fini sur les quatre formes réelles

FINAL rôle 3, source et objet figés. `{len(theorems)}` lemmes/théorèmes et `{len(defs)}` définitions dans un module nouveau. Dernier essai `{last['attempt']}` : exit0, zéro erreur, zéro avertissement ; les `{len(names)}` déclarations imprimées ont uniquement les axiomes standards `propext`, `Classical.choice`, `Quot.sound`. Aucun `sorry`, `admit`, nouvel axiome ou `native_decide` dans le source final. Score 0 ; aucune victoire.

## Contenu effectivement dérivé

Le module importe `FourFormRoots` figé du rôle 4, puis construit le vrai support `P=primeSupport z`, tous les premiers ≤z. Un sous-ensemble d représente le diviseur naturel `primeProduct d`. `support P z` impose exactement ce produit ≤z. `gprod`, `hprod` et `G` sont des produits/sommes finis, avec h(p)=g(p)/(1−g(p)). G n'est jamais une variable libre ou une borne postulée.

`transform` est l'inversion explicite du treillis des sous-ensembles. La cible diagonale y(d)=μ(d)h(d)/G est restreinte au support réel. `inverse_transform` et `diagonalization` sont démontrés par les sommes alternées sur les intervalles et le produit fini 1+1/h(p)=1/g(p). `principal_optimum` dérive ainsi

    Σ_(d,t⊆P) λ(d)λ(t)g(d∪t) = 1/G.

Les poids `weight` sont définis à partir de cette inversion. `canonical_weight_formula` donne la formule fermée et `canonical_moebius_weight` remplace le signe de l'ensemble par la vraie fonction `ArithmeticFunction.moebius` du produit :

    λ(d)=μ(product d) · product_(p∈d)(1−g(p))⁻¹ · cofactorG(d)/G.

`cofactorSupport` impose s⊆P\\d et product(d∪s)≤z : la coprimalité des facteurs est conservée par le support disjoint, et la coupure n'est jamais remplacée par le primorial complet. `weight_empty` prouve λ(1)=1. `support_downward`, `weight_zero_outside` et `product_exceeds_weight_zero` prouvent λ(d)=0 lorsque product d>z.

La norme n'est pas supposée. `one_prime_contraction` injecte les ensembles contenant p dans leurs effacements, avec conservation du support inférieur. `upperMass_le` itère cette contraction et prouve la masse supérieure ≤g(d)G ; `weight_abs_le_one` en déduit |λ(d)|≤1.

Pour un vrai polynôme entier F, `remainder` est exactement

    r(d)=card{{q∈J : ∀p∈d, p∣F(q)}}−card(J)g(d).

`square_decomposition` prouve la somme du carré Selberg =card(J)·principale+Σλ(d)λ(t)r(d∪t). Le masque rugueux est majoré point par point par ce carré. `finite_support_upper_bound` dérive ensuite le majorant concret

    card{{q∈J : ∀p∈P,p∤F(q)}} ≤ card(J)/G+Σ_(d,t∈support)|r(d∪t)|.

Aucune distribution désirée, signe de reste ou borne 1/G n'apparaît en hypothèse.

## Raccord effectif aux quatre formes

`actualDensity N e p0 p` est exactement `FourFormRoots.localDensity p N e p0`, soit le cardinal des racines réelles de q(N−e q)(N−q)(N−p0 q) modulo p, divisé par p. `actualG`, `actualWeight` et `actualRemainder` utilisent ce g et le polynôme entier du rôle 4 ; aucune substitution par quatre racines libres ou un S libre n'est faite.

`actual_four_form_sieve_dichotomy` est inconditionnel sur les coefficients N,e,p0 et tout ensemble entier fini J, avec z≥1. Si un premier local est saturé, le rôle 4 fournit une preuve de cellule rugueuse vide. Sinon les racines réelles satisfont 0<g(p)<1 ; le théorème en déduit G>0, principale1/G, λ(1)=1, toutes les normes |λ|≤1 et le majorant fini ci-dessus. Les ressources premières ne sont jamais supposées disponibles. A7, W/U4 et le ledger ne sont ni redéfinis ni réprouvés.

## Limite quantitative et condition de victoire

Ce module certifie les poids, le carré et sa principale sur les quatre formes. Il ne prouve pas encore |r(d)|≤ρ(d) par CRT/+1, la multiplicité lcm et τ12, la minoration analytique C4 ou les constantes C5/C6 au source u≥10^24. Le rôle 4 poursuit la vraie troncature dans un autre module qui pourra importer ce source figé. Les inputs θ/RS ne sont pas importés comme G≥cible. Les majorants écrits C4/C6 du FINAL2 restent distincts de ce fichier.

Les cellules A et S, le déficit après consommation unique des capacités, les autres couches du ledger, Gamma_star/TypeII et D_N restent ouverts. Un crible supérieur fini ne contourne pas à lui seul le mur de la parité. Le banc neuf à N=10^8 appartient au rôle 6 ; aucun producteur, replay numérique ou test source-onset n'a été lancé par ce rôle.

## Chaque échec réel du compilateur

{len(rows)} invocations nouvelles sur ce module, aucun probe API séparé ; {len(failures)} exit1 techniques, PASS aux essais {passes}. Chaque essai possède son snapshot intégral, log, SHA et commande dans `build_receipt.json`. Les objets PASS11 et final sont aussi préservés. Les anciennes sources, objets, banques et PDF n'ont jamais été compilés/réexécutés ici.

| Essai | Diagnostic observé | Correction logique/technique |
|---|---|---|
| 1 | λ token réservé ; unfold sign sous somme ; sdiff et égalité inversée ; nom ite_sum inconnu | Identifiant w, unfold explicite, orientation des ensembles, distribution finie du if |
| 2 | API prod_const_zero absente ; card_ne_zero attend Nonempty ; somme if non distribuée | Témoin du produit nul, vrai Nonempty, lemma spread |
| 3 | sens sum_subset et summandes distinctes ; mul_sum incomplet ; pow_two réécrit dans une hypothèse déjà développée ; filtre du support | Deux sommes intermédiaires, expansion des deux facteurs, support exact par extensionalité |
| 4 | nlinarith ne reconnaît pas le facteur sign² après dénominateurs ; G·G versus G² | Identité polynomiale par linear_combination, puis ring |
| 5 | Instances Decidable absentes dans masques divisibilité/rugosité | Instances locales explicites ; aucun changement de masque |
| 6 | Rewrite dépendant du Decidable lors de divides_union | simp sur l'équivalence puis cas sur les deux masques |
| 7 | Conjonction du support non réduite dans la formule fermée | Guard réel hr∧hdr réduit explicitement |
| 8 | Association mul/div ; lambda de erase non réduite ; upperMass non dépliée sous abs | Réassociation exacte, congrArg, change du terme défini |
| 9 | Subset n'est pas automatiquement la fonction attendue dans Or.elim ; commutation locale résiduelle | Eta-expansion et ring |
| 10 | gcongr tente un signe du produit sous abs ; z/g insuffisamment déterminés | Sommes et majoration de valeurs absolues explicites, paramètres fixés |
| 12 | Namespace map_prod_of_prime ; timeout d'élaboration du raccord ; dépendance bloquée | Méthode IsMultiplicative, paramètres explicites et masque réel identifié |
| 13 | Deux Decidable différents pour une même Finset.filter | Égalité des cellules par extensionalité, sans hypothèse nouvelle |

Les diagnostics n'affirment aucun blocage de parité : ils concernent les API, coercions, sommes, instances et réécritures. Le mur restant est une obligation analytique et bilantielle non estimée, explicitement séparée du succès Lean auxiliaire.

## Pièces et empreintes figées

Source Selberg : `{sha(SRC)}` ; objet : `{sha(SRC.with_suffix('.olean'))}`.
FourFormRoots importé : source `{sha(root_src)}`, objet `{sha(root_obj)}`.
Rapport FINAL2 conceptuel, PROBE17 et feedback16 sont liés dans le reçu. Inventaire antérieur799 conservé par le préflight du rôle6 ; ce rôle n'a écrit que role3 et ce rapport. Aucun ancien rebuild, aucune victoire et aucun score global positif.
'''
REPORT.write_text(report, encoding='utf-8')
input_paths = [
    R/'round17'/'agent2_capacity_incidence.md', R/'round17'/'PROBE_BLOCK.md',
    R/'.arbor'/'sessions'/'parity'/'.coordinator'/'messages'/'round16_feedback.md',
    root_src, root_obj,
    Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe'),
]
assets = sorted(p for p in W.rglob('*') if p.is_file() and p != OUT and '__pycache__' not in p.parts)
assets.append(REPORT)
d = {
    'round':17, 'role':3, 'status':'FINAL_REAL_FOUR_FORM_SELBERG_WEIGHTS_PRINCIPAL_AND_FINITE_UPPER_BOUND',
    'completed_utc':datetime.now(timezone.utc).isoformat(),
    'source':str(SRC),'source_sha256':sha(SRC),'olean':str(SRC.with_suffix('.olean')),
    'olean_sha256':sha(SRC.with_suffix('.olean')),'report':str(REPORT),'report_sha256':sha(REPORT),
    'theorem_count':len(theorems),'definition_count':len(defs),'theorems':theorems,'definitions':defs,
    'axiom_prints':len(names),'axioms_standard_only':True,'banned_tokens':0,'error_count':0,'warning_count':0,
    'compilatory_invocations':len(rows),'api_probe_count':0,'candidate_compilations':len(rows),
    'actual_exit1_count':len(failures),'successful_candidate_attempts':passes,
    'last_attempt':last['attempt'],'last_exit_code':0,'last_log':last['log'],'last_log_sha256':sha(last['log']),
    'real_root_density':True,'G_defined_not_assumed':True,'weights_defined_not_assumed':True,
    'principal_one_over_G_derived':True,'lambda_one_derived':True,'lambda_norm_le_one_derived':True,
    'product_cut_support_zero_derived':True,'actual_moebius_connected':True,
    'actual_saturated_cell_empty_connected':True,'finite_actual_remainder_upper_bound_derived':True,
    'CRT_plus_one_Lean_certified':False,'source_C4_Lean_certified':False,'source_C6_Lean_certified':False,
    'A7_reproved':False,'availability_assumed':False,'global_D_N_estimated':False,
    'old_Lean_rebuilds':0,'old_numeric_producers_or_replays':0,'old_PDF_rerenders':0,
    'numeric_producer_executed_by_role3':False,'parity_bypass_certified':False,'victory':False,'score':0,
    'input_bindings':{str(p):sha(p) for p in input_paths},
    'files':[{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size} for p in assets],
    'receipt_self_excluded':True,
}
OUT.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'status':d['status'],'source_sha256':d['source_sha256'],'olean_sha256':d['olean_sha256'],
    'report_sha256':d['report_sha256'],'receipt_sha256':sha(OUT),'theorems':len(theorems),
    'definitions':len(defs),'invocations':len(rows),'failed':len(failures),'PASS':passes},ensure_ascii=False))
