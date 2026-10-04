# BORD — identité exacte, SOURCE 02

Statut : source Lean rédigée et relue ; aucune élaboration, compilation, invocation de tactique, sonde d'API ou exécution numérique. Ce paquet ne remplace ni la monographie ni le ledger canonique. Les anciens PAPER, BUILD et sources restent immuables. Portée auxiliaire uniquement.

## Objet et domaines

Pour `a : ℝ`, `N : ℕ`, `q : ℂ`, poser, avec la puissance complexe principale de mathlib,

\[
 J_{a,N}(q)=\frac1{2\pi}\int_{-\pi}^{\pi}(a-i\theta)^{-q}e^{-iN\theta}\,d\theta.
\]

La normalisation est `angularNormalizer = (2 * (Real.pi : ℂ))⁻¹` ; elle ne réemploie pas la coupure canonique α. L'intégrale est une `intervalIntegral` complexe sur la mesure `volume` réelle. Le domaine analytique est **a>0, q quelconque dans ℂ**. L'affine `a−iθ` a partie réelle a, appartient au `Complex.slitPlane` et ne s'annule donc pas, pour tout θ réel. Aucune restriction `Re(q)>0` n'est nécessaire sur cet intervalle compact. Les identités de balance valent pour tout N naturel ; la récurrence divisée exige **N>0**.

## Conclusion exacte construite

La source fournit

\[
 J_{a,N}(q)=B_{a,N}(q)+\frac qN J_{a,N}(q+1),\qquad
 B_{a,N}(q)=\frac{i(-1)^N}{2\pi N}
 [(a-i\pi)^{-q}-(a+i\pi)^{-q}].
\]

Les deux bords sont conservés. Le caractère a les mêmes valeurs `(-1)^N` aux extrémités ; la puissance complexe n'est jamais déclarée périodique. `B(a,N,0)=0`. Pour a>0 et N>0,

\[
 B_{a,N}(1)=-\frac{(-1)^N}{N(a^2+\pi^2)}\ne0.
\]

Ainsi « terme de bord non nul » désigne un cas concret prouvé dans la source, et non une assertion fausse pour chaque exposant. Les formules sont falsifiables, mais aucun banc de quadrature ou calcul d'exemple n'a été lancé.

## Charges effectivement écrites

1. Construire la dérivée complexe de l'affine z↦a−Iz ; composer la dérivée de `cpow_const` sur le slit-plane ; restreindre au réel avec `HasDerivAt.comp_ofReal`. Le résultat est `I*q*(a−Iθ)^(-(q+1))`.
2. Construire la dérivée du caractère par l'affine complexe et `HasDerivAt.cexp`, puis celle du produit. La fonction dérivée concrète est `I*q*integrand(q+1) − I*N*integrand(q)`.
3. Déduire la continuité de ces fonctions de leurs dérivées, et l'intégrabilité des deux fonctions nécessaires sur le compact avec **volume explicitement typée**. Aucune intégrabilité finale n'est une prémisse.
4. Évaluer les caractères aux deux bords par `Complex.exp_nat_mul`, `Complex.exp_neg` et `Complex.exp_pi_mul_I`. Les coercitions négatives sont réécrites explicitement.
5. Appliquer `intervalIntegral.integral_eq_sub_of_hasDerivAt` à la vraie dérivée du produit ; extraire les constantes par les lemmes d'intégrale ; multiplier par I et utiliser `I*I=-1` ; diviser seulement après preuve de N≠0.
6. Pour q=1, utiliser `Complex.cpow_neg_one`, les non-annulations des deux bases et `a²+π²>0` ; réduire l'identité rationnelle complexe par `field_simp`/`ring`. Ces tactiques sont écrites dans la source, jamais invoquées par l'auteur.

## Dépendances et état précis

La source importe seulement des modules du cache mathlib 4.15 ; aucune dépendance locale non compilée n'est nécessaire. Les signatures de dérivation, transport réel, FTC, linéarité, exponentielle et slit-plane sont lues **TARGETED**, pas FULL pour les modules du cache. Le code et ce contrat sont lus FULL. Le catalogue est manuel : **30 déclarations =22 théorèmes +8 définitions**, avec 30 `#print axioms` qualifiés. Un futur juge devra élaborer le fichier, examiner l'absence de `sorryAx` et ses axiomes réels ; aucun `.olean`, PASS auteur ou PASS indépendant n'existe pour ce nouveau paquet.

Les API statiques n'ont pas identifié de déficit mathématique dans BORD. La réussite d'élaboration reste ouverte, particulièrement la normalisation des coercitions, les réécritures des deux valeurs aux bords et l'algèbre des inverses complexes. Il n'y a ni prémisse d'égalité finale, ni prémisse de dérivée ou majorant final, ni axiomatisation auxiliaire.

## Dettes globales conservées

BORD ne prouve pas la représentation Mellin de la vraie trace thermique à toute phase, l'échange spectral global, l'annulation de la corrélation tronquée ou une estimation signée. Il ne supprime aucune puissance première, aucune unité ou contribution de frontière et ne donne pas le coefficient additif N par lui-même. La chaîne vers le ledger, le contrôle de D_N et la condition de victoire restent ouverts. Aucun outil interdit d'estimation bilinéaire arithmétique, crible, Möbius, Vaughan ou restes de progressions n'est employé.
