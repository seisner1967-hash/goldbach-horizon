# ROLE5 — revue indépendante SOURCE Mellin / C5 archimédien

Statut : SOURCE/PAPER uniquement ; aucune compilation, aucun calcul numérique ni préparation de nouveau lot. Batch08 distinct est PREPARED sans invocation Lean à la rédaction de ce rapport. Le compteur officiel demeure 71 modules /1146 déclarations auxiliaires avec définitions. Les quatre fichiers audités ne sont pas des PASS.

Base B : `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\role4\h1_contour`. Lectures complètes réelles, non des en-têtes :

| Chemin sous B | SHA256 | FULL indépendant | Déclarations / prints |
|---|---|---|---|
| analytic_batch02/source-final/MellinThermal22.lean | 1396cb0a0045c621ea3e8f0f8b905c1c2a0af3ec33a351e4e7150542f38352fe | 4fc86f | 12/12 :9thm3defs |
| analytic_batch02/source-final/MellinThermalInversion22.lean | ad42b7bf8cd9b94e4f2c04125201b6a82b62821b1cb38652aa4e2f6c41a1df66 | 715d1c | 4/4 :4thm |
| c5_mellin_source01/ThermalC5Mellin22.lean | 04561a25ac18a7ea0a308020ea5187c3d4939b3c9ede013b08c8d9199a69dc6d | 4accd9 | 19/19 :16thm3defs |
| c5_mellin_source01/ThermalC5Arch22.lean | d8ae350372c0160ea9201e286d9355fedb771d89359b6d2ed2b54de35c39c687 | 356c4d | 35/35 :30thm5defs |

Les 70 déclarations SOURCE se décomposent en 16 antérieures et 54 nouvelles. Le comptage textuel et les hashes ont été vérifiés dans 2a8e1d ; cela n'est pas un parse Lean. `derivation22.md`, SHA e7d71d551744490176c6a8a81f213c206be1d9ff6a9b50250183fbb9f1a02c76, FULL2a8e1d ; `source_handoff_receipt22.json`, SHA666dbc291ec3f6ff9d77981a7b8b6295690a4ff1328d61b65dcc52664804c3d8, FULL5db427. L'inventaire rg85e141 ultérieur est tronqué et ne sert pas de nouvelle lecture FULL.

La dérivation est cohérente sur papier et construit ses principales charges dans les sources. Le vrai test thermique est f_Y(x)=(x/Y)e^(−x/Y). Pour Y>0 et Re(s)>−1, le premier module calcule sa transformée Mellin Y^sΓ(s+1) via l'intégrale d'Euler de Gamma et une dilatation réelle positive. Le test dual a les arguments Y^(1−s)Γ(2−s), avec domaine Re(s)<2. Les branches concernent des bases réelles positives.

L'inversion cite le véritable théorème d'inversion Mellin de Mathlib et construit l'intégrabilité verticale via ΓContour indépendant, pour c dans [−1/2,3/2], Y≥1, x>0. Ce domaine Y≥1 est celui de l'inversion et des conclusions C5 présentes. Les primitives FTC ultérieures valables pour Y>0 ne justifient pas d'étendre ces conclusions automatiquement à tout Y>0.

Sur s=−1/2+it, les modes G_Y(s)e^(−ws), w réel, ont norme e^(w/2)|G_Y(s)|. La positivité de x=e^w permet de transformer la puissance complexe en exponentielle avec la branche explicite log(e^w)=w. L'inversion donne f_Y(e^w). La décomposition du noyau apparié se fait en trois modes intégrables en t pour v fixé ; elle ne sépare pas prématurément les termes singuliers de l'intégrale globale en v près de zéro.

Le passage global du noyau mixte cite l'intégrabilité concrète et Fubini de `PsiMixedFubini22`, dont l'enveloppe est réellement construite dans la chaîne batch08. Le terme 1/s est traité séparément par le produit G_Y(s)e^(sv), v>0, de norme |G_Y(s)|e^(−v/2). Sa mesurabilité et intégrabilité produit sont construites avant un second Fubini ; la vraie formule Laplace donne −G_Y(s)/s. Le signe obtenu dans la contribution de pôle est correct. L'intégrabilité finale de Gχ′/χ découle de ces contributions, et n'est pas une hypothèse hC5 libre.

Le noyau archimédien est défini indépendamment par `[f_Y(x)+f_Y(1/x)/x−2f_Y(1)/x]/[x−1/x]`, sur x>1. Le changement x=e^v donne une vraie bijection de Ioi0 vers Ioi1 et un Jacobien e^v positif. Le numérateur est algébriquement relié au noyau Mellin apparié, puis aux deux corrections intégrables f_Y(e^v) et −2f_Y(1)e^(−v)/(1+e^(−v)). Les FTC démontrent les intégrales 1−e^(−1/Y), e^(−1/Y) et log2 à partir de primitives, limites et intégrabilités. La constante finale `(log(4π)+γ)f_Y(1)−1` est donc correctement raccordée à l'intégrale archimédienne. Le noyau complexe est ensuite identifié à l'intégrale du noyau réel ; son intégrabilité réelle est rédigée explicitement.

Aucune prémisse finale gratuite d'intégrabilité, de Fubini, de majorant Gamma ou de C5 n'a été détectée dans cette chaîne SOURCE. Cela ne ferme pas l'élaboration des preuves, les obligations API et leurs axiomes transitifs. Le premier déficit acquis demeure double : Mellin12/Inversion4 et C5Mellin19/Arch35 ne sont pas compilés ; χ/ψ/Fubini batch08 ne sont pas encore jugés. Les vieux ΓReflection8e070… et Reflection54e32… ayant FAIL dans les lots clos ne peuvent servir de dépendances acquises. Un futur lot doit lier les vraies sources/oleans indépendants réparés, et leur fermeture d'import, sans olean auteur.

La valeur amovible en x=1, sa régularité pour une quadrature utilisant cet endpoint et les constantes d'erreur C6 sont des charges distinctes : l'intégrabilité sur Ioi1 ne les prouve pas. Aucun budget quadrature/arrondi ne provient de ce paquet. Même quatre futurs PASS fermeraient ici l'identité C5 concrète seulement ; les limites de contours, résidus et compte complet de zéros de H1, la représentation uniforme en phase, le coefficient additif/D_N et WIN demeureraient à démontrer. Aucune modification des quatre sources auteur ni des lots Juge clos n'a été faite.
