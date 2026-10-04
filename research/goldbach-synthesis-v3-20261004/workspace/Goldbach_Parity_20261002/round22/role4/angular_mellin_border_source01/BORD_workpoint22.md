# BORD — point SOURCE suspendu avant preuve Lean

DRAFT, non gelé, aucune déclaration Lean écrite ni invoquée. ROOT donne priorité à la réparation BUILD04 après le vrai backendfail de BUILD03. Les acquis/PAPER/BUILD03 restent immuables.

Objet prévu : pour a>0, entier N≥1, q complexe, J=(2π)⁻¹∫[-π,π](a−iθ)^(−q)exp(−iNθ)dθ. La branche principale est légitime car la partie réelle vaut a. La dérivée réelle à construire est iq(a−iθ)^(−q−1). Le terme de bord exact vaut i(−1)^N[(a−iπ)^(−q)−(a+iπ)^(−q)]/(2πN), sans affirmation universelle de non-annulation pour tous q (q=0 donne zéro).

APIs locales lues TARGETED uniquement dans le cache q356/mathlib :

- Pow/Deriv.lean135–205, receipt9a0c36 : Complex.hasStrictDerivAt_cpow_const et HasDerivAt.cpow_const pour les fonctions complexes. Construire l'affine z↦a−Iz en variable complexe, puis restreindre au réel ; ne pas employer directement cette API sur une fonction ℝ→ℂ.
- Analysis/Complex/RealDeriv.lean70–117, receipt2f36a2 : HasDerivAt.comp_ofReal.
- Analysis/Complex/Basic.lean667–706, search2f36a2 : slitPlane contient tout complexe de partie réelle strictement positive.
- MeasureTheory/Integral/FundThmCalculus.lean1245–1308 et1320–1352, receiptde2800 : integral_deriv_mul_eq_sub_of_hasDerivAt, ou intégration par parties, exigent deux continuités, les dérivées concrètes et leurs IntervalIntegrable volume. Ces charges doivent être construites, pas fournies comme prémisses.
- IntervalIntegral.lean325–348 et552–578, receipt7646db : Continuous.intervalIntegrable avec mesure volume explicitement annotée ; extraction des constantes de l'intégrale.
- Trigonometric/Basic.lean1155–1205, receipt80d2c4 : exp_pi_mul_I ; Data/Complex/Exponential.lean208, search7646db : exp_nat_mul. Les valeurs aux deux extrémités se paient par exp(±iπ)=−1, puis la puissance naturelle, sans périodicité postulée de la puissance complexe.
- Pow/Complex.lean68–128, search8293e8 : cpow_neg_one/cpow_natCast si un exemple concret de bord non nul est ajouté ultérieurement.

Plan de preuve concret : intégrale de la dérivée du produit power×character ; la dérivée du produit est iq power(q+1)×character−iN power(q)×character. L'intégrale, normalisée, donne iq J(q+1)−iN J(q)=(2π)⁻¹(−1)^N différence de bord. Multiplier par i, utiliser I²=−1 puis N≠0 pour isoler J(q). Aucun signe du coefficient, aucune identité de trace de ζ/Mellin finale et aucune estimation de D_N n'est assumée. La prochaine phase doit encore écrire et relire cette preuve, avant toute préparation/gate.
