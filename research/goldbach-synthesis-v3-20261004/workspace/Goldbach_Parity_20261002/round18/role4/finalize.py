"""Read-only proof/log binding audit; no Lean, bank, sign or kernel invocation."""
import sys, json, re, hashlib
from pathlib import Path
from datetime import datetime, timezone
sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
R = W.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def exclusive_json(p, obj):
    with p.open('x', encoding='utf-8') as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
        f.write('\n')
started = {'phase': 'PREEXEC_READ_ONLY_AUDIT', 'timestamp_utc': datetime.now(timezone.utc).isoformat(),
           'auditor_sha256': sha(Path(__file__)), 'Lean_invoked': False, 'bank_invoked': False}
exclusive_json(W/'finalize_started.json', started)
b = json.loads((W/'build_receipt.json').read_text(encoding='utf-8'))
names = ['DoubleExtractionArithmetic', 'DividedFourForms', 'DividedRootCounts', 'DividedSelbergBridge']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
modules, totals = [], {'theorems': 0, 'defs': 0, 'structures': 0, 'instances': 0, 'print_axioms': 0}
for name in names:
    src, obj = W/(name+'.lean'), W/(name+'.olean')
    text = src.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|trustMe)\b', re.sub(r'#print axioms[^\n]*','',text))
    success = b['successful_modules'][src.name]
    assert sha(src) == success['source_sha256'] and sha(obj) == success['olean_sha256']
    attempt = next(x for x in b['attempts'] if x['attempt'] == success['attempt'])
    assert attempt['exit_code'] == 0
    log = Path(attempt['log']).read_text(encoding='utf-8')
    assert 'error:' not in log and 'warning:' not in log and 'sorryAx' not in log
    decls = [(m.group(1),m.group(2)) for m in re.finditer(r'^(def|theorem|structure|instance)\s+(\w+)',text,re.M)]
    prints = re.findall(r'^#print axioms (\w+)$',text,re.M)
    assert len(prints) == len(decls) and set(prints) == {n for _,n in decls}
    audits = {n.split('.')[-1]: set(a.strip() for a in ax.split(',') if a.strip())
              for n,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",log): audits[n.split('.')[-1]] = set()
    assert set(audits) == set(prints)
    assert all(a <= allowed for a in audits.values())
    counts = {'theorems':sum(k=='theorem' for k,_ in decls),
              'defs':sum(k=='def' for k,_ in decls),
              'structures':sum(k=='structure' for k,_ in decls),
              'instances':sum(k=='instance' for k,_ in decls), 'print_axioms':len(prints)}
    for k,v in counts.items(): totals[k] += v
    modules.append({'module':name, 'namespace':'GoldbachRound18.DoubleExtraction',
                    **success, 'counts_new_only':counts,
                    'pass_log_sha256':sha(Path(attempt['log'])),
                    'axioms':sorted(set().union(*audits.values())), 'warning_count':0})
for a in b['attempts']:
    assert sha(Path(a['snapshot'])) == a['snapshot_sha256'] == a['source_sha256']
    assert sha(Path(a['builder_snapshot'])) == a['builder_snapshot_sha256']
    assert sha(Path(a['started_receipt'])) == a['started_receipt_sha256']
    assert sha(Path(a['log'])) == a['log_sha256']
    if a['olean'] is not None: assert sha(Path(a['olean'])) == a['olean_sha256']
deps = json.loads((W/'dependencies_readonly.json').read_text(encoding='utf-8'))['bindings']
for rel,s in deps.items(): assert sha(R/rel) == s
assert sha(R/'round18'/'agent2_capacity_incidence.md') == '48dbcc5875c140d6d4991fa7d6cd58749048e3cf151e35f476893c27f81ae595'
gate = json.loads((W/'compile_gate.json').read_text(encoding='utf-8'))
for rel,s in gate['numeric_bindings'].items(): assert sha(R/rel) == s
assert totals == {'theorems':110,'defs':34,'structures':2,'instances':0,'print_axioms':146}
report = R/'round18'/'agent4_formalisation.md'
report_text = '''# FINAL — rôle 4, formalisation de la boucle 18

TERMINÉ. Quatre modules nouveaux compilent en Lean 4.15.0, avec 110 théorèmes, 34 définitions, 2 structures et 146 audits explicites `#print axioms`. Chaque journal PASS est sans erreur, sans avertissement et sans `sorryAx`. Les seuls axiomes observés sont `propext`, `Classical.choice` et `Quot.sound`. Score 0 ; aucune victoire ni paiement global de D_N.

La sélection réelle est le node 14.3. Le concept FINAL2 reste inchangé, SHA 48dbcc5875c140d6d4991fa7d6cd58749048e3cf151e35f476893c27f81ae595. Le root a autorisé l’écriture, puis la compilation uniquement après lecture du PASS numérique SS canonique attempt 02 et de ses certificats stockés. `role4/compile_gate.json` lie cette autorisation au reçu numérique et à `semiprime.json`. Le rôle 4 n’a lancé aucune banque, aucun calcul W, aucun signe, aucun ancien PASS, aucun rendu et aucune compilation de source historique.

Les procédures Arbor executor et merge-eval ont été appliquées à la capture des essais et au gel des artefacts. L’ownership imposé et l’interdiction de Git ont fixé le répertoire de travail `round18/role4`, sans création de worktree. Les neuf modules historiques importés sont en lecture seule : les cinq ingrédients 17, EulerAnchor et LeastMissingPrimeMargin 16, ThreeAdicPrimePairing et ShortDivisorComplement historiques. Leurs 18 empreintes source/olean sont capturées et validées dans `dependencies_readonly.json`. Les théorèmes de ces dépendances ne sont pas recomptés dans les 110 nouveaux théorèmes.

| Nouveau module | Théorèmes | Définitions | Structures | Essai PASS |
|---|---:|---:|---:|---:|
| DoubleExtractionArithmetic | 40 | 10 | 1 | 02 |
| DividedFourForms | 20 | 11 | 0 | 04 |
| DividedRootCounts | 36 | 7 | 1 | 08 |
| DividedSelbergBridge | 14 | 6 | 0 | 10 |

**Objets et gardes réels.** `anchor N` est le premier impair manquant canonique importé d’EulerAnchor, et non un p0 libre. `resource1 = N−q`, `resource0 = N−p0*q`, `witness1/0 = minFac(resource1/0)` et `quotient1/0 = resource1/0 / witness1/0` sont des définitions effectives. La structure `Cell N q` garde N positif pair, q premier unitaire, p0 < q, p0*q < N, les deux ressources ≥ 2, les deux quotients effectivement premiers et chaque quotient strictement plus grand que son témoin. Leur primalité est une garde de sélection de SS, pas une disponibilité supposée ni une masse d’incidences.

Cette cellule arithmétique est plus générale que les coupures source. Pour l’appliquer à la famille physique du concept, les coupures q ≥ M, n_e > Q, e carré libre unitaire, e > p0, e ≤ E, ell_j ≤ Z et les autres fronts restent celles du FINAL2. Leur conversion complète depuis alpha/a/M/Q et l’intervalle source n’est pas un nouveau théorème de ces modules. Q original, a = ceil(N^(7/16)), alpha = ceil(N^(1/4)), M = ceil(N^(3/4)) ne sont jamais abaissés.

Le premier noyau dérive les unités des ressources et des témoins, ell_j ≥ p0, ell0 ≠ p0, ell1 ≠ ell0 et même la coprimalité des deux ressources. Il admet ell1 = p0. Il construit A = q mod L, L = ell1*ell0, prouve A < L, q = A + L*(q/L), A ≡ N mod ell1 et p0*A ≡ N mod ell0. `representative_is_actual_CRT` l’identifie au représentant chinois canonique ; `representative_unique_linear_CRT` prouve son unicité pour ces deux congruences effectives. Les unités nécessaires à l’inversion de p0 modulo ell0 sont dérivées.

**Formes divisées et déterminants.** Les constantes entières c1 = (N−A)/ell1 et c0 = (N−p0*A)/ell0 utilisent les quotients naturels exacts. Les deux identités ell1*c1 = N−A et ell0*c0 = N−p0*A sont prouvées avant tout calcul dans ZMod. Les quatre couples (pente, constante) sont (L,A), (−eL,N−eA), (−ell0,c1), (−p0*ell1,c0). Au véritable index q/L, les quatre valeurs sont q, N−eq, quotient1 et quotient0.

Pour Delta_ij = pente_i*constante_j − pente_j*constante_i, dans cet ordre, Lean dérive NL, N*ell0, N*ell1, N*ell0*(1−e), N*ell1*(p0−e), N*(p0−1). Le produit des pentes est −e*p0*L^3. `actualDelta` est la valeur absolue du produit des pentes et des six déterminants ; il est égal à N^6*e*p0*L^6*(e−1)*(e−p0)*(p0−1) et strictement positif sous e > p0. `prime_divisors_actualDelta` prouve, pour toute prime, l’équivalence exacte avec les diviseurs premiers de Delta17*L. C’est le raccord du radical ; aucune prétendue indépendance du représentant n’est assumée.

**Racines effectives.** `dividedRoots`, `dividedRho` et `dividedDensity` filtrent le vrai produit des quatre formes divisées dans ZMod. `TargetGuards` impose seulement l’unité de e, e > p0 et les exclusions arithmétiques e ≠ 1 mod ell1 / e ≠ p0 mod ell0. `actual_primitivity` prouve, sur chaque prime et chaque forme, qu’une pente et sa constante ne s’annulent pas simultanément. Aucune propriété de rho n’est ajoutée comme prémisse. Les primes divisant L, p0 et N sont traitées effectivement par les unités et la coprimalité des ressources.

Les théorèmes compilés donnent 1 ≤ rho ≤ min(4,p), rho = 1 sur chacun des deux témoins admissibles et rho = 4 hors `actualDelta`. Les deux classes exclues de la cible donnent une saturation exacte au témoin correspondant. Toute saturation rend `dividedRoughCell J P` vide sur n’importe quel ensemble fini J contenant ce premier dans P, sans hypothèse de primalité des valeurs de la cible.

Le raccord supplémentaire `modularForm_actual_relation` prouve F17(affine0(x)) = L*F_divisé(x). Si p ne divise pas L, l’application affine est bijective et `rho_transport_off_modulus` identifie les deux nombres de racines effectifs. Le cas N ≡ 1 mod 3, p0 = 3, e ≡ 2 mod 3 et 3 ∤ L a donc rho = 3 par transport du théorème 17 figé. Aux témoins, le transport par division n’est pas utilisé : leurs facteurs locaux sont établis séparément, y compris ell1 = p0.

**Raccord quantitatif réellement compilé.** `switchG`, `switchWeight` et `switchRemainder` instancient les constructions génériques Selberg 17 avec `dividedDensity` réel. Ils ne sont pas un `actualG17` arbitrairement transféré. La dichotomie compilée donne une cellule vide en présence d’une saturation ; sinon G > 0, principal = 1/G, poids vide = 1, norme des poids ≤ 1 et la borne finie du cardinal par |J|/G plus la somme de tous les restes réels `|switchRemainder J (d ∪ t)|`. Les restes sont définis par les comptes de divisibilité effectifs. Aucun coût CRT uniforme n’est placé comme prémisse ni supprimé.

La troncature réutilise le moment et Markov génériques 17. Sous y ≤ z, z > 0, log z ≥ 32, 32 log y ≤ log z, les gardes de cible, la non-saturation réelle et l’input analytique indépendant sum_(p≤y) log(p)/p ≤ 2 + 2 log y, `switchG_collision_loss_half` prouve

    switchG(N,e,q,z) ≥ P(y)^4 * switchCollisionLoss(N,e,q,y) / 2,

où P(y) est le vrai produit d’Euler fini 17 et `switchCollisionLoss` est le produit des (1−1/p)^3 précisément sur les primes divisant `actualDelta`. Les bornes rho ≥ 1 et rho = 4 hors Delta, déjà dérivées sur le nouveau polynôme, fournissent la comparaison locale. La queue du powerset et le support tronqué sont conservés dans le théorème Markov importé. Aucune hypothèse G ≥ cible, disponibilité première, densité favorable, capacité ou C6 n’intervient.

Cette minoration conditionnelle effective ne certifie pas D5 numérique. Mertens fini, le prix global en totient, la preuve analytique de l’input prime-log et les arrondis des niveaux T = floor(N^(1/16)), Y = floor(T^(1/32)) restent indépendants et non formalisés ici. La borne uniforme CRT avec tous ses +1 et la sommation sur tous e/ell1/ell0 restent écrites. D10 = 12 K N ell^6/u^2 + 2 N^(7/8)u^13 et D11 au seuil u ≥ 10^36 ne sont pas déclarés Lean. Le seuil original u ≥ 10^24 et le segment 10^24 ≤ u < 10^36 restent visibles ; N = 10^8 ne teste aucun de ces deux onsets.

**Réciprocité et prix ouverts.** Lean prouve que le complément du vertex m1 = N−q est réellement q premier. Pour m0 = N−p0*q, son premier axe est le produit de deux premiers distincts p0*q : vonMangoldt et theta sont exactement nuls. Aucune capacité m0 n’est créée. `resource1_injective` et le cardinal de l’image d’un ensemble de labels justifient la représentation par vertices physiques ; ils n’établissent ni une assignation globale de partenaires ni le prix signé du ledger. Tous les e d’un même q partagent un seul m1, et un m1 déjà dans l’union d’ancres ou parmi les demandes ne constitue pas une nouvelle ressource. Le vrai coefficient de sourceBracket, les W réels et leur signe après cette union ne sont pas remplacés par des coefficients libres.

Le banc neuf stocké couvre les 5 001 entiers q de [1 400 100,1 405 100], soit 333 q premiers unitaires, 22 cœurs, 7 326 axes cibles et 286 triplets de formes divisées. Il conserve 674 demandes theta dans S, dont 40 dans SS et 634 dans S\\SS. Les 14 fibres SS et 68 vertices physiques gardent 54 kernels actifs, les 14 vertices m0 de poids nul et les 2 ancres existantes ; aucun vieux kernel n’a été recalculé par le rôle 4. Le déficit SS positif moins capacité m1 mesurée une seule fois reste strictement POSITIF. Ces faits finis sont lus dans le PASS canonique et ses certificats autorisés, sans recomputation. Ils ne réfutent aucun théorème asymptotique et ne paient pas le résidu.

Les ressources à quotient composite, notamment à au moins trois facteurs, T_A après consommation unique, Gamma et D_N global restent non estimés. Les branches e = 1 / c1 / b1, les cœurs premiers avec Lambda(e), les rangs 2, raw properpowers sans filtre mu(n)^2, S(bN), référence −S(N)N, original Q/k1/whole U_a, les faces, les cofacteurs longs et toutes erreurs conservent leur place. P5 porte toujours sur le bloc entier avant tout retrait. Le ledger est inchangé : D_N = Bprime^a + Bpp^a + Pband>=2 + Zface>=2 + Ialpha + 2 max(e,0). Le résultat est un acquis auxiliaire conditionnel, pas un contournement global de parité.

**Exécution et gel.** Dix invocations Lean nouvelles ont des snapshots source et builder créés avant exécution, un reçu started, la commande exacte, les chemins de cache, les empreintes gate/numerical/imports, le journal et l’exit réels. Les six échecs 01/03/05/06/07/09 sont conservés : fermeture de section, projections vectorielles/casts, association du produit Fin 4, parenthèses de notation et instance de décidabilité. Ils sont des erreurs techniques d’élaboration. Certains journaux d’échec portent les sorryAx de récupération du compilateur ; aucune source finale ou provisoire ne contient de placeholder de preuve. Les PASS 02/04/08/10 sont sans sorryAx ni avertissement. Aucun module PASS n’a été modifié ni recompilé ; `build.py` refuse une telle invocation. Les imports nouveaux figés sont également validés PREEXEC à partir de l’essai 05 ; leur ordre et leurs empreintes antérieures sont conservés dans le ledger des succès 02/04. Le reçu FINAL lie tous ces artefacts et les limites, sans recompter les dépendances anciennes.
'''
with report.open('x',encoding='utf-8') as f: f.write(report_text)
bindings = {}
for p in W.iterdir():
    if p.is_file() and p.name != 'final_receipt.json':
        bindings[str(p.relative_to(R)).replace('\\','/')] = sha(p)
bindings[str(report.relative_to(R)).replace('\\','/')] = sha(report)
receipt = {'status':'FINAL_PASS_AUXILIARY_PARTIAL_NO_WIN', 'timestamp_utc':datetime.now(timezone.utc).isoformat(),
           'score':0, 'victory':False, 'modules':modules, 'counts_new_only':totals,
           'attempts_total':10, 'failed_attempts_retained':[1,3,5,6,7,9], 'pass_attempts':[2,4,8,10],
           'historical_modules_compiled':0, 'historical_dependencies_recounted':False,
           'allowed_axioms':sorted(allowed), 'final_warning_count':0,
           'old_protected_registry_count_root_preflight':997,
           'source_onset':'log N >= 10^24', 'written_budget_onset':'log N >= 10^36',
           'intermediate_segment_paid':False, 'finite_N_is_onset_test':False,
           'canonical_numeric_gate_output_SHA':gate['numeric_bindings']['round18/semiprime.json'],
           'derived_quantitative_statement':'switchG >= finite Mertens Euler^4 * actual collision loss / 2',
           'independent_analytic_input':'sum_{prime p<=y} log(p)/p <= 2+2log(y)',
           'not_Lean_certified':['analytic prime-log estimate','Mertens/totient conversion D5',
                'uniform CRT +1 aggregate D6/D7','all-param weighted D10','budget D11',
                'S minus SS','T_A unique global assignment','Gamma','global D_N'],
           'bindings':bindings, 'historical_readonly_bindings':deps,
           'concept_FINAL2_immutable_SHA':'48dbcc5875c140d6d4991fa7d6cd58749048e3cf151e35f476893c27f81ae595'}
exclusive_json(W/'final_receipt.json',receipt)
print(json.dumps({'report_SHA256':sha(report), 'receipt_SHA256':sha(W/'final_receipt.json'),
                  'counts_new_only':totals,'score':0,'victory':False},ensure_ascii=False))
