# Journal réel du compilateur — ROLE4, nœud 14.5

Ce journal ne décrit que des invocations nouvelles, autorisées par la gate explicite de la racine. Les échecs techniques ci-dessous ne constituent pas une détection du mur de la parité. Les snapshots PREEXEC, START, commandes, stdout, stderr, logs et codes de sortie sont conservés par `build.py` dans ce répertoire.

| Tentative | Module | Résultat | Diagnostic et réparation |
|---|---|---|---|
| 01 | FriablePhysicalPrefix | FAIL, exit 1 | `omega` échoue sur les deux wrappers `M ≤ resource0/1`, malgré les caps et préfixes établis. Remplacement par transitivités `calc`. |
| 02 | FriablePhysicalPrefix | FAIL, exit 1 | `omega` traite l'atome `Nat.div` sans nonnégativité dans les termes ajoutés. Remplacement des comparaisons par `Nat.le_add_right` et `Nat.mul_le_mul_right`. |
| 03 | FriablePhysicalPrefix | PASS, exit 0 | Tous les théorèmes imprimés utilisent seulement `propext`, `Classical.choice`, `Quot.sound`. Source et olean gelés. |
| 04 | FriableEulerRankin | FAIL, exit 1 | La projection `toFun` du `MonoidHom` construit n'est pas réduite avant `rw Nat.cast_mul`. Ajout d'un `change` explicite. |
| 05 | FriableEulerRankin | PASS, exit 0 | Produits Euler et véritables sommes de tau sur le support friable, puis tails Rankin ; axiomes standard seuls. Source et olean gelés. |
| 06 | FriableKernelEnvelope | FAIL, exit 1 | `simp` laisse un cas trivial de `Nat.prime_mul_iff` ; remplacement par deux cas explicites. `omega` oublie encore la nonnégativité de la division dans `e*q<N` ; remplacement par la chaîne additive issue du cap. |
| 07 | FriableKernelEnvelope | PASS, exit 0 | Véritable cofacteur physique et axes theta/raw, enveloppe W et borne TK explicitement conditionnelle ; axiomes standard seuls. Source et olean gelés. |
| 08 | FriablePrimeHarmonic | FAIL, exit 1 | Cas N=0 non fermés, import/namespace d'intégrales, nom de lemme d'inversion absent et commandes après fermeture du but. Corrections explicites de positivité, import et API. |
| 09 | FriablePrimeHarmonic | FAIL, exit 1 | `integral_rpow` est global dans ce cache, et non dans `intervalIntegral`. Nom corrigé. |
| 10 | FriablePrimeHarmonic | FAIL, exit 1 | Seul réarrangement algébrique `x−1=−1+x` après calcul intégral. Fermé par `ring`. |
| 11 | FriablePrimeHarmonic | PASS, exit 0 | P-série, Eminus, somme des premiers, Eplus≤u^27, masse réelle≤u^−37 et tail tau≤N*u^−42, avec gardes géométriques explicites. Axiomes standard seuls. |
| 12 | FriableTotientEnvelope | FAIL, exit 1 | Coercions `ArithmeticFunction`, conversion List/Multiset/Finset, commutativité exponentielle, réduction d'inverses et paramètre X non inféré. Raccords API et algèbre explicités. |
| 13 | FriableTotientEnvelope | PASS, exit 0 | TK≤3(1+log X) dérivé uniformément de vrais diviseurs squarefree, Euler fini, télescopage et injection des multiples. Aucun TK libre. Axiomes standard seuls. |
| 14 | FriablePhysicalPayment | FAIL, exit 1 | Réduction lambda de l'injection AP, front `Nat.div`, réarrangement sous somme, signature à trois arguments de `abs_sub_le`, dépliage tau et alpha implicite. Corrections ciblées. |
| 15 | FriablePhysicalPayment | FAIL, exit 1 | Un seul reste de distributivité sous la somme des fronts AP. Ajout de `add_mul`, `one_mul`, `mul_one`. F3 physique unique déjà sans `sorryAx`. |
| 16 | FriablePhysicalPayment | PASS, exit 0 | Vraie réunion des classes avec +1 et coût réciproque F1 physique unique≤7N*u^−39 sous gardes géométriques. Axiomes standard seuls. |

Les six modules de base sont gelés après seize invocations : six PASS et dix FAIL techniques conservés.

| Tentative extension | Module | Résultat | Diagnostic et réparation |
|---|---|---|---|
| 01 | FriablePhysicalDemand | FAIL, exit 1 | Placement de la négation dans `abs_add`, facteur 1 non simplifié et type implicite d'une transitivité. Corrections algébriques explicites ; intégrité post-exécution inchangée. |
| 02 | FriablePhysicalDemand | PASS, exit 0 | Rang réel e≤N/M, vrai C≤7u², ABS theta/raw≤7u³ et F2 sur un rang depuis la vraie réunion AP. Axiomes standard seuls ; intégrité post-exécution inchangée. |

| Tentative agrégation | Module | Résultat | Diagnostic et réparation |
|---|---|---|---|
| 01 | FriableDemandAggregation | FAIL, exit 1 | `Prod.snd` polymorphe bloque la coercion Finset/Set, réarrangement interne de la somme harmonique et Z implicite. Injection typée, distributivité et Z nommé ; intégrité post-exécution inchangée. |
| 02 | FriableDemandAggregation | PASS, exit 0 | F2 de tous les rangs physiques, cutoff dérivé N/M, vraies sommes fibrewise et masse Euler ->14*u^−34*(N*H_E+E*D*Y). Axiomes standard seuls ; intégrité post-exécution inchangée. |

| Tentative budget source | Module | Résultat | Diagnostic et réparation |
|---|---|---|---|
| 01 | FriableSourceBudget | FAIL, exit 1 | Une seule positivité échoue : `positivity` ne récupère pas automatiquement `g.u_pos` pour `8192*u*ell`. Remplacement par deux applications explicites de `mul_pos`. Le théorème final incomplet imprime `sorryAx` dans ce seul log FAIL ; aucun PASS ne lui est accordé. Intégrité post-exécution inchangée. |
| 02 | FriableSourceBudget | PASS, exit 0 | Le coût réel ABS des demandes friables theta de tous les rangs H et des réciproques F1 physiques uniques est ≤N/(8192*u*ell), depuis le seul onset original u≥10^24. Les neuf déclarations imprimées ont seulement les axiomes standard. Intégrité post-exécution inchangée. |

Les neuf modules propres gelés totalisent vingt-deux invocations, neuf PASS et treize FAIL techniques. La géométrie est un dixième module importé, produit séparément par ROLE4_geometry en deux invocations (un FAIL et un PASS). Le total logique ROLE4 est donc vingt-quatre invocations, dix PASS et quatorze FAIL techniques, sans reconstruction des anciens modules ni rejeu d'un PASS.

Le raccord source F4 est maintenant prouvé pour la somme positive précisément définie dans `sourceFriableAbsoluteCost`. Les gardes géométriques et TK sont déchargées. Le coût réciproque des incidences F0\F1 à m1 nonfriable reste impayé ; le pont H vers tout le support source, la partition du retrait et le ledger complet restent ouverts. Aucun échec technique n'est présenté comme un obstacle analytique, et aucun PASS auxiliaire n'est déclaré victoire.
