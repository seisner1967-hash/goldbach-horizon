# BORD04 — réparation SOURCE du vrai FAIL24

Statut SOURCE uniquement. Le lot24 a réellement lancé une compilation du source03 1fa9de9a, START2026-10-03T21:59:06.178472UTC → FIN21:59:37.539934UTC, exit1, aucune olean, zéro crédit de module. Le log45c7c847, FIN et receipt sont lus FULL7e7c8a. Trente impressions : 26 standards et 4 récupérations sorryAx ; cinq avertissements linter. Les sorties gelées de23/24 et les sources02/03 sont préservées.

## Correction unique

Le diagnostic exact à la ligne123 est : la réécriture `rw [← inv_pow]` cherche `(a^n)⁻¹` alors que le but effectif est déjà `(-1)⁻¹ ^ N = (-1)^N`. La séquence précédente a donc déjà placé l’inverse à la base. La seule modification de preuve dans source04 est la suppression de cette ligne. Le `norm_num` préexistant traite l’inverse de la constante complexe −1 ; N demeure arbitraire et symbolique. Aucun nouvel énoncé, aucune prémisse finale et aucune hypothèse de périodicité n’est ajouté.

Les autres deux raccords réparés en03 (lambda de la dérivée du caractère et mise à plat de congrArg dans la récurrence) sont conservés exactement. Aucun autre diagnostic n’apparaît dans le log24, mais les 26 impressions partielles ne valent pas validation du module. Cette proposition doit être relue puis réellement compilée indépendamment dans un lot distinct, sans reprise24 ni compilation auteur.

## Contrat mathématique conservé

Un module, 30 déclarations manuelles =22 théorèmes et8 définitions, mêmes noms/énoncés/domaines/définitions/ordre des30 impressions que03, zéro dépendance locale. Pour a>0, q complexe arbitraire et N naturel :

`J(a,N,q)=(1/(2π)) ∫_(-π)^π (a−iθ)^(-q) exp(-iNθ) dθ`, avec puissance principale et volume.

La source construit le plan fendu et la non-annulation depuis Re(a−iθ)=a>0, la dérivée cpow, la dérivée du caractère et du produit, la continuité, les intégrabilités explicites et la formule fondamentale du calcul. Pour N>0 elle écrit

`J(a,N,q) = i(-1)^N [(a−iπ)^(-q)−(a+iπ)^(-q)]/(2πN) + (q/N) J(a,N,q+1)`.

Le terme de bord est conservé : nul à q=0 et égal à `−(-1)^N/[N(a²+π²)]`, réellement non nul, à q=1. Il n’est pas déclaré non nul pour tout q. L’égalité des caractères aux deux bords ne donne pas de périodicité de la puissance principale.

La révision n’assume aucune intégrabilité, dérivée ou égalité analytique finale. Elle ne prouve aucune annulation spectrale tronquée, trace globale ζ, uniformité θ du producteur, correction des puissances premières, positivité de frontière ou cible D_N. Aucun WIN et aucun crédit officiel.

## Lecture et préservation

Le seul changement est inspecté dans le code SOURCE ; pas de parseur Lean/Python, probe, calcul ou évaluateur. Les signatures mathlib et les lectures SOURCE02/03 demeurent dans leurs reçus immuables, TARGETED sans lecture FULL du cache. Aucun besoin de nouvelle identité inverse-puissance : la réécriture redondante est supprimée. La lecture combinée initiale des documents Mellin et du log24 a été globalement tronquée et exclue ; lecture24 complète de remplacement7e7c8a et lecture Mellin complète9b070a.

Le paquet disjoint Mellin SOURCE02 est fermé et suspendu : coree54cac5b +Holomorphy9d3d050f,37 déclarations non compilées, handoff2c10db3f. Il n’est pas modifié par BORD04 et n’est pas une dépendance de ce module. Les sources/rapports/gates/receipts anciens et les archives demeurent intacts. Aucun nouveau PREP, gate, actual ou olean auteur n’est créé.
