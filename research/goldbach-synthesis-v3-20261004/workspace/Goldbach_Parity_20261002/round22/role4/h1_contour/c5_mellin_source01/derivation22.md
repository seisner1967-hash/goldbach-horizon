# Raccord C5 — SOURCE ONLY

Les deux nouvelles sources sont `ThermalC5Mellin22.lean` (19 déclarations) et `ThermalC5Arch22.lean` (35). Elles n'ont été ni compilées ni préparées pour exécution. Le lot futur contient donc 54 nouvelles déclarations et les 16 déclarations déjà écrites de MellinThermal/Inversion, sans crédit officiel ajouté.

Pour (s=-1/2+it), (G_Y(s)=Y^s\Gamma(s+1)), (f_Y(x)=(x/Y)e^{-x/Y}) et (C_\pi=1/(2\pi)), le premier module construit l'intégrabilité des modes (G_Y(s)e^{-ws}), puis les évalue par la vraie inversion de Mellin. Le vrai majorant apparié de PsiMixedFubini paie l'échange (t,v). Le terme (1/s) est traité séparément par Laplace complexe à forme 1 et taux (-s), dont la partie réelle vaut (1/2); son intégrabilité produit est dérivée, puis un second Fubini donne (-\int_0^\infty f_Y(e^{-v})dv).

Le second module définit indépendamment le quotient archimédien de C2. Après (x=e^v), son noyau (A(v)) vérifie exactement

\[
A(v)=M(v)+f_Y(e^v)-2f_Y(1)\frac{e^{-v}}{1+e^{-v}}.
\]

Les primitives réelles, leurs limites et la non-négativité des dérivées paient les FTC et leurs intégrabilités : les trois intégrales correctrices valent (1-e^{-1/Y}), (e^{-1/Y}) et (\log 2). Le Jacobien (e^v), l'image (e^{(0,\infty)}=(1,\infty)), l'injectivité et tous les dénominateurs non nuls sont construits. Il en résulte le contrat source concret

\[
C_\pi\int_\mathbb R G_Y(-1/2+it)\frac{\chi'}{\chi}(-1/2+it)dt
=(\log(4\pi)+\gamma_E)f_Y(1)+\operatorname{Arch}_Y-1.
\]

Les FTC nécessitent (Y>0); inversion, Fubini utilisé et conclusion portent (Y\ge1). Le quotient est intégré sur (x>1), donc la valeur amovible en (x=1) n'est pas supposée. La continuité au point de couture et les erreurs quantitatives de C6 sont des contrats séparés.

Dépendances : GammaPrerequisites et GammaContour corrigé sont individuellement jugés PASS; MellinThermal12/Inversion4 demeurent SOURCE. Les modules \(\psi/\chi\)/Fubini du batch06 étaient NONINVOQUÉS après l'échec API de ZetaReflection. Toute future préparation doit sélectionner leurs sources réparées réellement jugées et conserver les anciennes captures. Il n'existe aucune hypothèse d'intégrabilité finale, d'égalité C5 ou de majorant cible libre dans ces deux nouveaux modules. Aucun PASS Lean, H1 global, coefficient additif ou résultat sur (D_N) n'est revendiqué. L'obligation additive est détaillée séparément dans `continuous_correlation_obligation22.md`.
