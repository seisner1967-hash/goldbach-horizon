# Discret29 révision03 — revue indépendante ROLE5 SOURCE

Auteur ROLE3, reviewer ROLE5 ; aucune compilation/probe/calcul numérique. Source `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\role3\discrete_circle_source22\revision03\DiscreteThermalProjection22.lean` SHA f24c702b0a6cd71e88ae1279061a45e02fa04f12f8e8641444d3b5e1803e8f02, FULL propre 2ceb49. Rapport auteur SHA9fd8d6e2d25dd3cfed25f01adae5b9e559b40b468b19899a0ba615879bfe6350 et lectures SHAfcb78f20e00329ffa2b4519a0516a7d8fd4cd347c23d2498af6dac5bb1adb7c2, tous deux FULL propre f297aa.

Référence effective : lot14 FAILED exit1, log SHA879f2978a6de8935608661b3194a36c728fbff743c864c3f114405fc463c3d0a FULL propre8a6633 ; 29 prints dont sept sorryAx de récupération, aucun olean, zéro crédit. ROOT a clos physiquement14 : baseline75/1223 inchangée,18PASS8FAIL. Les anciennes sources/lots sont préservés.

Les quatre raccords répondent exactement aux quatre erreurs observées :

1. `sum_gridCharacter_no_alias` réécrit d'abord l'identité de somme, puis `simp only [grid_divides_iff_zero hK hlo hhi]` transporte l'équivalence sous l'ite en reconstruisant son instance Decidable. Aucun changement de divisibilité signée ou des bornes strictes.
2. `sum_rectangle_character` emploie `simp only [hz]` pour l'équivalence entière/naturelle sous l'ite ; le témoin hz et les conditions A0 restent identiques.
3. `discrete_normalizer_cancel` normalise maintenant **hc et le but** par `push_cast at hc ⊢`. Ils portent sur la même identité réelle transportée par Complex.ofReal, y compris l'exponentielle et la division. K>0 et exp non nul demeurent construits.
4. `sampled_trueCircle_eq_coefficient` termine par `simpa only [Int.cast_neg] using h`, explicitant exactement le cast signé rejeté. Aucun changement du caractère exp(-iN theta).

Aucun déficit SOURCE précis restant détecté dans ces quatre raccords. Cela n'est pas un PASS anticipé : leur élaboration reste à tester dans une nouvelle tentative autorisée. Le metadata builder vérifiera textuellement les 29 headers identiques et les 29 noms/prints avant freeze.

La chaîne mathématique intégrale de la précédente revue SOURCE02 reste applicable : racine complexe concrète, orthogonalité signée par somme géométrique, A0 sur tout le rectangle fini, N≤M, poids véritables Lambda incluant les puissances premières et normalisation K/exp exactement annulée. a∈R arbitraire convient au polynôme fini. Ni orthogonalité finale ni majorant/cible ne figure comme prémisse libre. L'expansion corrigée par sum_mul_sum/sum_product reste inchangée et n'avait produit aucune erreur dans le vrai lot14.

Scope proposé15 : un seul module29=20 théorèmes+9 définitions, aucune dépendance locale ni olean auteur ; auxiliaire CIRCLE uniquement. Pas de nouveau domaine, trace infinie à a=0, producteur NTT prêt, coefficient calculé à10^8, H1/C5global, élimination des puissances premières, D_N ou WIN.
