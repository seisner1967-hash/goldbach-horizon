# Boucle 17 — Selberg fini sur les quatre formes réelles

FINAL rôle 3, source et objet figés. `42` lemmes/théorèmes et `23` définitions dans un module nouveau. Dernier essai `14` : exit0, zéro erreur, zéro avertissement ; les `65` déclarations imprimées ont uniquement les axiomes standards `propext`, `Classical.choice`, `Quot.sound`. Aucun `sorry`, `admit`, nouvel axiome ou `native_decide` dans le source final. Score 0 ; aucune victoire.

## Contenu effectivement dérivé

Le module importe `FourFormRoots` figé du rôle 4, puis construit le vrai support `P=primeSupport z`, tous les premiers ≤z. Un sous-ensemble d représente le diviseur naturel `primeProduct d`. `support P z` impose exactement ce produit ≤z. `gprod`, `hprod` et `G` sont des produits/sommes finis, avec h(p)=g(p)/(1−g(p)). G n'est jamais une variable libre ou une borne postulée.

`transform` est l'inversion explicite du treillis des sous-ensembles. La cible diagonale y(d)=μ(d)h(d)/G est restreinte au support réel. `inverse_transform` et `diagonalization` sont démontrés par les sommes alternées sur les intervalles et le produit fini 1+1/h(p)=1/g(p). `principal_optimum` dérive ainsi

    Σ_(d,t⊆P) λ(d)λ(t)g(d∪t) = 1/G.

Les poids `weight` sont définis à partir de cette inversion. `canonical_weight_formula` donne la formule fermée et `canonical_moebius_weight` remplace le signe de l'ensemble par la vraie fonction `ArithmeticFunction.moebius` du produit :

    λ(d)=μ(product d) · product_(p∈d)(1−g(p))⁻¹ · cofactorG(d)/G.

`cofactorSupport` impose s⊆P\d et product(d∪s)≤z : la coprimalité des facteurs est conservée par le support disjoint, et la coupure n'est jamais remplacée par le primorial complet. `weight_empty` prouve λ(1)=1. `support_downward`, `weight_zero_outside` et `product_exceeds_weight_zero` prouvent λ(d)=0 lorsque product d>z.

La norme n'est pas supposée. `one_prime_contraction` injecte les ensembles contenant p dans leurs effacements, avec conservation du support inférieur. `upperMass_le` itère cette contraction et prouve la masse supérieure ≤g(d)G ; `weight_abs_le_one` en déduit |λ(d)|≤1.

Pour un vrai polynôme entier F, `remainder` est exactement

    r(d)=card{q∈J : ∀p∈d, p∣F(q)}−card(J)g(d).

`square_decomposition` prouve la somme du carré Selberg =card(J)·principale+Σλ(d)λ(t)r(d∪t). Le masque rugueux est majoré point par point par ce carré. `finite_support_upper_bound` dérive ensuite le majorant concret

    card{q∈J : ∀p∈P,p∤F(q)} ≤ card(J)/G+Σ_(d,t∈support)|r(d∪t)|.

Aucune distribution désirée, signe de reste ou borne 1/G n'apparaît en hypothèse.

## Raccord effectif aux quatre formes

`actualDensity N e p0 p` est exactement `FourFormRoots.localDensity p N e p0`, soit le cardinal des racines réelles de q(N−e q)(N−q)(N−p0 q) modulo p, divisé par p. `actualG`, `actualWeight` et `actualRemainder` utilisent ce g et le polynôme entier du rôle 4 ; aucune substitution par quatre racines libres ou un S libre n'est faite.

`actual_four_form_sieve_dichotomy` est inconditionnel sur les coefficients N,e,p0 et tout ensemble entier fini J, avec z≥1. Si un premier local est saturé, le rôle 4 fournit une preuve de cellule rugueuse vide. Sinon les racines réelles satisfont 0<g(p)<1 ; le théorème en déduit G>0, principale1/G, λ(1)=1, toutes les normes |λ|≤1 et le majorant fini ci-dessus. Les ressources premières ne sont jamais supposées disponibles. A7, W/U4 et le ledger ne sont ni redéfinis ni réprouvés.

## Limite quantitative et condition de victoire

Ce module certifie les poids, le carré et sa principale sur les quatre formes. Il ne prouve pas encore |r(d)|≤ρ(d) par CRT/+1, la multiplicité lcm et τ12, la minoration analytique C4 ou les constantes C5/C6 au source u≥10^24. Le rôle 4 poursuit la vraie troncature dans un autre module qui pourra importer ce source figé. Les inputs θ/RS ne sont pas importés comme G≥cible. Les majorants écrits C4/C6 du FINAL2 restent distincts de ce fichier.

Les cellules A et S, le déficit après consommation unique des capacités, les autres couches du ledger, Gamma_star/TypeII et D_N restent ouverts. Un crible supérieur fini ne contourne pas à lui seul le mur de la parité. Le banc neuf à N=10^8 appartient au rôle 6 ; aucun producteur, replay numérique ou test source-onset n'a été lancé par ce rôle.

## Chaque échec réel du compilateur

14 invocations nouvelles sur ce module, aucun probe API séparé ; 12 exit1 techniques, PASS aux essais [11, 14]. Chaque essai possède son snapshot intégral, log, SHA et commande dans `build_receipt.json`. Les objets PASS11 et final sont aussi préservés. Les anciennes sources, objets, banques et PDF n'ont jamais été compilés/réexécutés ici.

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

Source Selberg : `b1b658aa92f8e02cef29667e9e60b763ca3ef57bb25dcbc8aa9c50ba33591ce1` ; objet : `9639c1f7ae9eb03d07c1de2fd79cdea4dd503d29716e5de3adb4085de21fc46c`.
FourFormRoots importé : source `49cbf93fd8eb9aa75236419d5d7b95e1841d67571865171115ffbbdfcb71e9fa`, objet `4a13fc20feabfd5ff552f5dbd18c99c6b66bcfe1a65a3f44fff555417d7b4021`.
Rapport FINAL2 conceptuel, PROBE17 et feedback16 sont liés dans le reçu. Inventaire antérieur799 conservé par le préflight du rôle6 ; ce rôle n'a écrit que role3 et ce rapport. Aucun ancien rebuild, aucune victoire et aucun score global positif.
