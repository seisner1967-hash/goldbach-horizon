# Revue indépendante SOURCE — Λ–Mellin, main30

Verdict : chaîne mathématique cohérente sur Re(w)>0 ; aucun déficit logique ou incompatibilité précise des signatures examinées identifié. Les 30 déclarations restent SOURCE non élaborée, sans crédit Lean. Revue ROLE5 distincte de l'auteur ROLE4, après clôture effective du FAIL29. Aucun PREP, import candidat, probe, compilateur ou calcul numérique exécuté pour cette revue.

La lecture manuelle retrouve exactement 6 définitions, 24 théorèmes et leurs 30 impressions qualifiées, dans `GoldbachComplexGammaMellin22`. Les preuves sont écrites ; aucune occurrence de commande `sorry`, `admit`, `axiom`, `native_decide` ou `unsafe` n'est employée. Cela décrit la SOURCE, pas les axiomes que constaterait un futur compilateur.

La fonction utilisée est la vraie `ArithmeticFunction.vonMangoldt` du cache : log(minFac n) pour une puissance première, zéro sinon. Les termes 0 et 1 sont nuls et toutes les puissances premières sont conservées. `lambda_direct_le_log` utilise cette définition et minFac≤n directement, sans inversion de diviseurs. L'inégalité log n≤2√n donne Λ(n)n⁻²≤2n⁻³ᐟ². Le test intégral compare les termes n≥2 à l'intégrale de x⁻³ᐟ² sur [1,K+1], au plus 2 ; le terme n=1 ajoute 1 et le terme n=0 vaut zéro dans la convention rpow du cache. Ainsi Q=ΣΛ(n)n⁻²≤6 est une conséquence construite, pas une prémisse libre.

La norme exacte de Λ(n)n⁻²⁻ⁱᵗ vaut Λ(n)n⁻². La majoration sommable indépendante de t paie la convergence uniforme et la continuité de D(t), puis ‖D(t)‖≤6. Pour K(w,t)=Γ(2+it)w⁻²⁻ⁱᵗ, le vrai L1 acquis Local26 donne chaque intégrande L1 par continuité et domination. La série de leurs intégrales de normes est Q·∫‖K‖ ; sa sommabilité est écrite avant `integral_tsum_of_summable_integral_norm`. La signature réelle de cette API demande précisément ces deux charges, présentes dans la SOURCE. Les intégrales sont des intégrales de Bochner sur ℝ avec volume ; le facteur 1/(2π) correspond à l'inversion acquise.

Pour n>0, la multiplication de w par le réel positif n conserve la branche principale : log(nw)=log n+log w, donc (nw)⁻ˢ=n⁻ˢw⁻ˢ. Re(nw)>0 permet d'appliquer l'inversion complexe réellement PASS27 au point nw. Le cas n=0 est traité séparément par Λ(0)=0. L'inversion terme par terme construit aussi la convergence absolue de la série thermique. La conclusion proposée est bien

\[
\sum_{n\ge0}\Lambda(n)e^{-nw}
=\frac1{2\pi}\int_{\mathbb R}D(t)\Gamma(2+it)w^{-2-it}\,dt,
\qquad \operatorname{Re}w>0.
\]

Le majorant local de D·K multiplie la vraie borne Local/Holo par 6. La boule, le contrôle de norme et d'argument, et le taux positif `localDecayGap` proviennent du vrai PASS27 ; l'intégrabilité du majorant simple est construite depuis son moment exponentiel pondéré. Ici d_local=(π/2−|Arg w|)/4, tandis que le rayon Tail à w fixe emploie δ=(π/2−|Arg w|)/2. Ces taux ne doivent pas être confondus. La SOURCE ne conclut ni continuité de la série thermique en w, ni holomorphie de cette série, même si le majorant local permet des développements ultérieurs.

Les constants compactes du contrat, pour w=a−iθ, a>0 et |θ|≤Θ, sont cohérentes sur papier : A=atan(Θ/a), η=(π/2+A)/2, d=(π/2−A)/2 et C*=a⁻²sec²η. Mais le transport Arg/atan et la majoration sur ce rectangle ne sont pas des théorèmes du main30. De même ‖P−P_H‖≤6R(w,H) exige l'intégration des deux queues du produit D·K ; la borne sur l'intégrale Gamma non pondérée ne suffit pas. Cette enveloppe est PAPER seulement, non acquise par main30 ni par FAIL29. La continuité du rayon ne remplace pas ces identités ou l'évaluation de primitives.

La dépendance directe est Holo27 SOURCE b8b69c16… / olean f831358e… / reçu 63bc0f74…, réellement PASS, avec Local26 e54cac5b… / olean364ac79… comme rowPASS22 d'un reçu globalFAILED conservé. Gamma02 et Thermal20 restent transitives et readonly. Les 32 bindings auteur ont été physiquement rehashés, sans écart ; les oleans sont lus comme bytes seulement. Tail n'est pas importé. Le bridge2 est exclu de cette revue et reste PENDING ; le contrat, gelé avant FAIL29, décrit encore Tail02 comme remis, ce qui n'est pas un PASS.

Les API examinées existent dans le cache Lean4.15/mathlib9837ca9d : comparaison somme/intégrale, integral_rpow, p-series, continuité de tsum, norme de cpow positif, logarithme principal positif, sommabilité bornée et échange somme/intégrale. Des normalisations et inférences restent à constater par un futur vrai compilateur ; aucune absence d'erreur de compilation n'est anticipée.

Le résultat est un raccord analytique exact de la vraie trace thermique, sans identification D=−ζ′/ζ, sans zéro de ζ, sans loi de signe canonique en phase, sans correction PP ou frontière r>α. Le coefficient N=10⁸ et D_N ne sont pas évalués. La cible D_N et WIN restent ouverts ; baseline officielle 85 modules / 1434 déclarations inchangée.

Provenance exacte :

- [SOURCE main30](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_lambda_source01/ComplexGammaMellinLambda22.lean), SHA c0653c546413d5f2aac9715a301303c2ac5750dca5d96054bfb450c91ab3249c, FULL aa0ebd.
- [Contrat](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_lambda_source01/source_contract22.md), SHA f22355b45749755605a2e28245984760f72e1d49a45323a94a8d4a11c9e6a09a, et catalogue SHA c580f9713f97677d0b866db62102d1c8802be3980278c20ae313e6a6c3f60b4a, FULL ddf615.
- Handoff SHA 7cbd95b3bb74cbfec4587aa5a40c4b0be420865b83e15794888a3f3bae56e1e3, FULL 0f53c2 ; lectures auteur SHA 29a8be4f74bde8b1a98813062add1f881cc203db9efb3a7ebef27e6d190d0322, FULL 8b6d80.
- API cache TARGETED seulement 0259e1 / 0cd312 / b95add ; bindings32 BYTE_HASH b95add. L'appel agrégé tronqué initial est exclu de toute revendication FULL ; les lectures séparées ci-dessus le remplacent.

Les lots28/29 et toutes les sources auteur restent immuables. Ce rapport ne prépare aucun lot ni aucune banque.
