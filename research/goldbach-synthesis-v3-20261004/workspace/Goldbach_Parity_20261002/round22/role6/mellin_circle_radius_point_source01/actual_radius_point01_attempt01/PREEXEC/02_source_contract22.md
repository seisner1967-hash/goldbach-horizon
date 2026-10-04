# Point du rayon Mellin–Λ — SOURCE seulement

**NUMERIC_RADIUS_BOUND_ONLY_NOT_IDENTITY_OR_LEAN_PROOF**

`radius_point22.py` est une source Python de bibliothèque standard, non lancée,
non importée, non parsée par un outil candidat et sans PREP. Une revue SOURCE
indépendante et un gate ROOT sont requis avant toute invocation mathématique.
Aucun résultat de comparaison, point ACTUAL, PASS, coefficient ou WIN n'est
présumé. Les reçus de lecture et les SHA portent uniquement sur des octets.

Le contrat de référence est SOURCE34DECL, `LambdaCircleTruncationEnvelope22.lean`
SHA256 `bf9b8257760a20d33dd21714221401cd8fd327596f72e56c4d024200b2cb6c4c`.
Ses dépendances prospectives et sa preuve du raccord COEFF ne sont pas validées
par ce programme. Le catalogue et le handoff ont été lus FULL ; leurs états
historiques restent attribués à leurs auteurs, sans nouvelle vérification ici.

Le seul point prévu est N=100000000, a=1/N, H=100000000000 et τ=1/1000000.
Le rayon scalaire du contrat est

\[
E_N=e^{aN}(2U\varepsilon+\varepsilon^2),\quad
U=\frac{e^{-a}}{(1-e^{-a})^2},\quad
d=\frac{\arctan(a/\pi)}2,\quad
\varepsilon=\frac{24e^{-dH}}{\pi a^2d}.
\]

Raccords réels PAPER, repris de `mellin_lambda_feasibility_paper01/feasibility22.md`
(lecture FULL, aucune validation Lean) :

1. U=1/(2sinh(a/2))² et 2sinh(a/2)≥a>0 donnent U≤a⁻²=N².
2. Pour x≥0, atan(x)≥x/(1+x) : la différence vaut zéro en zéro et
   sa dérivée est 2x/((1+x²)(1+x)²)≥0. Le PAPER donne 3<π<7/2.
   Au point fixé π+a<4, donc d≥a/(2(π+a))>a/8=1/(8N).
3. H≥0, la monotonie de exp et la positivité des dénominateurs donnent
   e⁻ᵈᴴ≤e⁻ᴴ⁄⁽⁸ᴺ⁾, 1/d≤8N et 1/π<1/3. Ainsi
   ε≤24·(1/3)·N²·8N·e⁻ᴴ⁄⁽⁸ᴺ⁾=64N³e⁻ᴴ⁄⁽⁸ᴺ⁾.
4. aN=1, e<3 (borne PAPER), U≥0, ε≥0 et H/(8N)=125 donnent
   E_N≤3(128N⁵e⁻¹²⁵+4096N⁶e⁻²⁵⁰). Le terme ε² est conservé.

Ces raccords n'utilisent aucune constante choisie pour ajuster la cible. Les
bornes sur π et e sont les bornes élémentaires du PAPER ; elles ne sont pas
recalculées ni attestées par le programme. Le raccord de E_N à |C_N−C_{N,H}|
reste le théorème SOURCE COEFF avec ses dépendances impayées au gel cité.

Le remplacement dirigé de l'exponentielle est exclusivement
S=Σ(k=0..150)125ᵏ/k!, e¹²⁵≥S>0, q=1/S, e⁻¹²⁵≤q et e⁻²⁵⁰≤q².
Tous les termes, réciproques, carrés et comparaisons sont `Fraction`/entiers
exacts ; aucun reste estimé, float, Decimal ou approximation non dirigée.

Le degré fixe 150 est justifié sans recherche adaptative : S₆(5)>100 par
comparaison rationnelle exacte, et S₆(5)²⁵≤S₁₅₀(125) par l'identité
multinomiale et la positivité. Chaque multi-indice du produit a degré total
≤6·25=150 ; ses termes sont inclus dans la somme Taylor de exp(25·5).
Cela fournit le témoin conservateur S>100²⁵=10⁵⁰. Le programme revérifie
ces comparaisons rationnelles lorsqu'il sera autorisé, puis construit
B=3(128N⁵q+4096N⁶q²) et compare strictement B<τ par produits croisés entiers.
Il émet les numérateurs/dénominateurs exacts de S, q, q², ε_majorée, B et τ,
les paramètres et les deux entiers du témoin de comparaison. Un échec de la
comparaison retourne 2 ; une incohérence d'un raccord rationnel provoque une
erreur explicite. Aucun résultat de ces opérations n'est joint au présent gel.

Ce B majorerait seulement le rayon fermé de coupure Mellin H, sous les
raccords réels PAPER. Il ne calcule ni E_N lui-même, ni P, P_H, D, K, C_N ou
D_N ; il ne teste aucune identité. Il ne paie ni troncature de D, quadrature
en t/θ, noyaux, primitives, nœuds, poids, ni erreur d'une autre évaluation.
Les objets de référence gardent toutes les puissances premières : aucun
retrait PP, signe canonique ou terme de frontière n'est traité. Aucune
quadrature, crible, Möbius/Vaughan, progression, forme bilinéaire, bibliothèque
native/NTT ni allocation de 400 MB n'est introduite.

Frontière Lean : ce programme n'élabore aucune des 34 déclarations, ne produit
aucun olean et ne transforme ni PAPER ni SOURCE en PASS. La revue du code
reste elle-même SOURCE sans contrôle syntaxique Python exécuté. Les anciens
fichiers, judge5 et archives sont restés en lecture seule. Aucun goal, budget,
automation, thread, Git, installation, probe ou préparation n'a été créé.
