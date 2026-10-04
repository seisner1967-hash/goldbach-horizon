# Revue indépendante C5 — SOURCE uniquement

ROLE5, 2026-10-03. Aucun compilateur, probe, calcul numérique, écriture de preuve,
manifest d'exécution ou rejeu. Le total officiel transmis par ROOT reste
66 modules / 1109 déclarations auxiliaires, définitions incluses.

La chaîne proposée est cohérente à la lecture et construit les charges
analytiques concrètes jusqu'à Fubini. Les six nouvelles sources restent
non compilées : cette revue ne leur accorde aucun PASS. Le premier verrou de
certification est une dépendance réellement en échec, `GammaContourComponent22`.
C5 complet, H1, coefficient N, D_N et WIN ne sont pas acquis.

Base des chemins ci-dessous :
`B = D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002`.
Tous les SHA256 sont ceux des fichiers réellement lus ; les lectures FULL
désignent des sorties intégrales non tronquées, pas la fermeture de leurs imports.

| Source exacte sous B/round22/role3/h1_psi | SHA256 | Lecture FULL | Théorèmes/définitions/prints futurs |
|---|---|---|---|
| C5_checkpoint_after_psi05.md | 9119650574a298e229f620623d50c14d7e749d915305ffe0fa459a9dc6c889f7 | 456589 | checkpoint |
| GammaPsiReflection22.lean | 8e070c18a483ac71703f66b80dbcf4129f0f16ada8f2a933497655b3a7cdaa30 | f1fcbe | 5/0/5 |
| ContourChiPsi22.lean | a90d536187fe342d01cf913a56c80a34e6846eb273a533bcdd843289f7d83248 | 2a235d | 9/1/10 |
| ContourChiScaled22.lean | d0aa03290fe806f9c84c0311a7e07a2fe0737148c9c1de7c80876118fb7a64d7 | 85d47b | 8/2/10 |
| PsiKernelEnvelope22.lean | 949c6fc0d895003b522518e18ae89bdf6b5062448d5273f146685645afb72ef8 | 7a213c | 8/1/9 |
| PsiKernelDomination22.lean | 80b85c14c7db79121f7c9cb003edf97a7d5e947f785ce8402f910ea93aad48bc | 3f4e37 | 19/2/21 |
| PsiMixedFubini22.lean | d143b0fbdf795a1b400f737274a5eae5c8c5bba0c2e4ecaf145d86932df0b250 | d3989e | 17/2/19 |

Total lexical : 74 déclarations = 66 théorèmes + 8 définitions, avec 74
commandes `#print axioms` qualifiées. Liste ciblée vérifiée en 17a438. Ces
commandes n'ont pas été exécutées ; aucune couverture d'axiomes compilée n'est
prétendue pour C5. La lecture des preuves ne relève aucun `sorry`, `admit`,
déclaration `axiom`, `native_decide` ou `unsafe` dans ces six fichiers.

## Chaîne analytique et prémisses

1. **Réflexion Γ puis χ′/χ.** La réflexion est différentiée sur le voisinage
   ouvert −1 < Re s < 0. Les arguments différentiés 1−s/2 et 1+s/2 ont une
   partie réelle positive. Le sinus non nul est déduit de la vraie réflexion
   et des non-annulations de Γ. `contourChi` est celui de ROLE4, pas une fonction
   de substitution. La duplication et la réflexion donnent la formule
   symétrique avec log π, 1/s et les deux vraies Ψ. Le logarithme de 2π utilise
   la positivité du réel, donc aucune branche complexe arbitraire n'est postulée.

2. **P1 puis noyau.** Les deux intégrales Ψ sont celles de P1, indépendamment
   certifiée dans le lot Juge52 clos. Leur intégrabilité est réutilisée et le
   changement u=2v transporte le Jacobien absolu 2. Sur s=−1/2+it, le noyau est
   exactement
   `(exp((-3/2+it)v)+exp((-3/2-it)v)-2exp(-2v))/(1-exp(-2v))`.
   Le numérateur reste apparié ; aucun échange de termes individuellement
   divergents à v=0 n'est employé. L'identité de changement de variable
   totalisée pour tout s n'est pas à elle seule une preuve d'intégrabilité :
   celle-ci est séparément rédigée dans la bande ouverte.

3. **Domination du noyau.** N(t,0)=0 et la borne ‖N′‖ ≤ 7+2|t| sont établies
   par les dérivées des exponentielles. La valeur moyenne donne
   ‖N(t,v)‖ ≤ (7+2|t|)v. Le dénominateur positif satisfait
   1−exp(−2v) ≥ 2v/(1+2v), puis ≥v/2 pour 0<v≤1 et ≥1/2 pour v≥1.
   Cela donne les bornes 14+4|t| près de zéro et 8exp(−3v/2) en queue.
   L'enveloppe E(t,v)=(14+4|t|)exp(1−v)+8exp(−3v/2) est continue et son
   intégrabilité en v est construite par changement de variable Laplace.

4. **Facteur réel et Fubini proposé.** Le facteur est
   G(Y,t)=Y^(−1/2+it)Γ(1/2+it), pour Y>0, via le vrai
   `gammaContourFactor Y (-1/2) 1 t`. La récurrence vers Γ(3/2+it), la borne
   Γ sur [1,2] déjà jugée et ‖1/2+it‖≥1/2 donnent la borne source
   4Y^(−1/2)exp(−π|t|/4). L'enveloppe mixte correspondante est continue en
   (t,v) pour chaque Y fixé. Deux produits de fonctions Laplace construisent
   son intégrabilité sur volume × volume|_(v>0), y compris le facteur |t|.
   La continuité du véritable intégrande sur v>0 paie la mesurabilité ; la
   domination et `mono'` précèdent `integral_integral_swap`.

Les conclusions concrètes ont seulement les domaines nécessaires, notamment
Y>0, v>0 ou −1<Re s<0. Elles ne reçoivent aucune hypothèse libre de majorant,
de Fubini, de trace ou de cible D_N. Le helper `integrable_abs_extension`
reçoit une intégrabilité générique hf ; ses usages concrets la construisent
avec des intégrales Laplace. Il n'est donc pas une preuve par hypothèse de
l'intégrabilité mixte finale. Tout ceci reste un audit de SOURCE, avec risques
d'élaboration et de compatibilité des APIs non testés ici.

## Dépendances et lacunes exactes

- `GammaPsiDuplication22` : source
  `B/round22/role3/h1_psi/revision05/source_final/GammaPsiDuplication22.lean`,
  SHA0491177c6cfc1ef35b28796be404a3ca7975bac357cc6551b80d12333726812e,
  FULL a01498. Son reçu `revision05/psi_batch05_attempt01/receipt.json`,
  SHA74b5dfe2fd4f1b470714fd2d27aee62e678e77ab33f64b36e04eab92fc3ea531,
  FULL f63d83, confirme un vrai PASS auteur de deux déclarations. Aucun PASS
  Juge indépendant de cette dépendance n'est accordé dans cette revue.
- `ZetaReflection22` : source
  `B/round22/role4/h1_contour/ZetaReflection22.lean`,
  SHA54e32a95a62929c7251bf130156adbc7da7d66ceb1cb77609382e33c025f4a42,
  FULL 676a6d. Elle apporte le vrai objet χ, mais importe `ZetaEulerDirect22`.
  Aucun résultat de compilation de cette chaîne n'a été acquis par cette
  revue. La simple importation ne paie pas la réflexion ζ ni H1.
- `GammaContourComponent22` : source exacte auteur en échec
  `B/round22/role4/h1_contour/analytic_batch02/source-final/GammaContourComponent22.lean`,
  SHA244f20f0d0198101b6b2a27841b273b01f7c52f28a38b7b51b4db588446f4265,
  FULL 40bb1a. FIN réel
  `analytic_batch02/actual_attempt01/GammaContourComponent22_FIN.json`,
  SHAa707b3e777404d75e15af543ae5e5fefa1f24b4ff377159c111decca01aac442,
  FULL e418ff : exit1, aucun olean. Vrais stdout/stderr lus FULL819c0a,
  stdoutSHA1e72a122b34680b073571e620e16125e55ce4a7b6c20ed43fdd62128bd588510.
  Erreurs : mauvais argument dans `ContinuousAt.comp` à la ligne61 et constante
  `Real.integral_exp_neg_Ioi` absente à la ligne87. La récupération produit
  `sorryAx`, notamment dans `gammaContourFactor_continuous`, utilisé par la
  mesurabilité de Fubini. Cette version ne peut donc soutenir un crédit C5.
  La révision corrigée future et sa liaison d'import devront être explicites ;
  aucune version homonyme différente n'est implicitement substituée ici.

Lectures supplémentaires **TARGETED seulement** : ΓPrerequisites déjà jugée,
`B/round22/judge5/batch02_sources/GammaPrerequisites22.lean` lignes41–54 et
302–335, sortie e4325d ; définition weightedGammaTerm/égalité cpow dans
`B/round22/role4/h1_contour/analytic_batch02/source-final/GammaBoxBounds22.lean`,
sortie 361df1 ; mathlib cache sous
`D:/Users/Utilisateur/Desktop/Maths/q356-canonical-binding-replay/.lake/packages/mathlib/Mathlib/`,
`MeasureTheory/Integral/Prod.lean` et `MeasureTheory/Measure/Prod.lean`, APIs
`integral_integral_swap` et `prod_restrict`, sortie ceb03e. Aucune lecture FULL
de ces bibliothèques ni audit complet des imports n'est revendiqué.

Après certification des dépendances et des six nouvelles sources, Fubini
concernerait uniquement G(Y,t)K(t,v) sur la ligne Re s=−1/2. Resteraient le
raccord à l'inversion Mellin réelle, la normalisation et l'orientation du
contour, le transport x=exp(v), l'identification de l'Arch original, la
primitive log2 et les deux intégrales f/x donnant le terme final −1 de C5.
Ces fichiers ne fournissent pas non plus une erreur quantitative de quadrature
ou de troncature double certifiée : une enveloppe intégrable n'est pas à elle
seule ce contrat numérique. H1 et les contours infinis, le compte complet
des zéros, coefficient N et la cible D_N restent distincts et ouverts.

Incidents de lecture sans portée mathématique : un nom de log inexistant
(95a099), puis deux chemins de cache placés initialement sous B (361df1), ont
été corrigés par inventaire/chemin réel. Aucun de ces incidents n'est un FAIL
Lean, un probe ou une revendication FULL. La revue est close ; aucune
préparation d'exécution supplémentaire n'a été produite.
