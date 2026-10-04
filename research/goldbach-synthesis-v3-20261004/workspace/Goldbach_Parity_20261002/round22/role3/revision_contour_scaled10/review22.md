# Révision SOURCE 10 de ContourChiScaled22

La source distincte corrige les trois diagnostics réels du Juge batch09, sans nouveau compilateur ni probe. La source ancienne d0aa03290fe806f9c84c0311a7e07a2fe0737148c9c1de7c80876118fb7a64d7 et le lot09 restent immuables. Le log réel SHA6fbd12cf496dbb66a5d25e69eb0668e6f5cafda352e29dc1e4f44c460a99d189 a été lu FULL66bf7f ; ces erreurs ne constituent ni une contradiction analytique ni un obstacle de parité.

Dans scaleTwo_image_Ioi, le témoin (u/2 : ℝ), son appartenance 0<u/2 et le type du dénominateur2 sont maintenant fixés avant div_pos. Cela empêche l'élaboration de la sous-preuve de positivité de garder une metavariable au lieu de u/2. L'équation de l'image demeure 2*(u/2)=u.

Dans scaleTwo_injOn_Ioi, change (2:ℝ)*v=2*w at h déroule les deux applications lambda avant linarith only[h]. L'injectivité et le domaine Ioi0 restent les mêmes.

Dans contourPsiPair_scaleTwo, les trois égalités d'exposants et le passage du scalar réel au facteur complexe2 sont conservés. Après ces égalités, on utilise la loi de corps avec zéro

2 * (A/(2*D)) = (2*A)/(2*D) = A/D,

via ←mul_div_assoc puis mul_div_mul_left _ _ (2≠0). La signature de mul_div_mul_left est relue directement dans Algebra/GroupWithZero/Units/Basic.lean431–432. Cette loi est valable même si D=0 dans la division totale Lean. Elle supprime les deux branches de l'ancien field_simp qui développaient 2*(1-exp) en une expression inverse opaque. Aucun nonzero de Gamma, ζ ou de 1-exp ne devient une prémisse ajoutée.

La preuve de transport ne change pas : elle paie le jacobien2, l'injectivité et l'image Ioi0 via les deux APIs Jacobian réelles. L'intégrabilité provient toujours de la vraie intégrabilité P1 du noyau apparié ; l'identité intégrale ne prétend pas permuter les deux intégrales de C5. La bande -1<Re(s)<0, les valeurs sur la droite gauche et les dix déclarations/dix prints qualifiés sont préservés. Le contrôle lexical SOURCE fa609b n'a trouvé aucun sorry/admit/axiome ajouté/unsafe/native_decide.

Statut SOURCE_CORRECTED_NOT_COMPILED : aucune preuve de compilation de cette révision n'est revendiquée. Le module Chi09 a un PASS indépendant, mais cela ne donne pas un PASS anticipé à Scaled10. Les trois modules aval non invoqués dans batch09 et le raccord global C5/H1/coefficientN/D_N/WIN restent ouverts. Le lancement numérique03, lorsqu'il sera autorisé séparément, ne compile aucun de ces fichiers.