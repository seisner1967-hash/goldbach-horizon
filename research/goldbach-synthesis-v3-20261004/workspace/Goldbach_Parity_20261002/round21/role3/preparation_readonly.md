# ROLE3 — préparation API en lecture seule, boucle21

Statut : PREPARED_READONLY_API_INVENTORY. Le candidat signé21 est une proposition de ROLE1 gelée, encore soumise à sélection par root. Aucun nouveau théorème, fichier Lean de preuve, producteur mathématique Python, probe Lean, compilation, ancien PASS ou test numérique n’a été exécuté. Aucun fichier historique n’a été modifié. Ce document est un inventaire de signatures, pas un résultat mathématique, un PASS ou une victoire.

Les lectures portent sur PROBE21, FINAL3_20, FINAL5_20, la proposition signée21 et les objets exacts20. Le cache local au commit9837ca9d65d9de6fad1ef4381750ca688774e608 est l’autorité des signatures ci-dessous. Aucune consultation de documentation plus récente ni installation/version-probe n’a été utilisée.

## Objets acquis à importer en lecture seule

Namespace `GoldbachRound20.SwitchedComposite` : `physicalQDomain`, `mem_physicalQDomain`, `physicalQDomain_prime`, `physicalQDomain_front`, `physicalQDomain_unit`, `physicalCandidate_unit_tN`, `physicalCompositeWindow`, `physicalCompositeWindow_cap`, `physical_candidate_AP_iff`, `physical_nonunit_AP_impossible`, `actualPrimeAP`, `actualCompositeAP`, `frameLower`, `frameUpper`, `frameInterval`, `logarithmicAPIntegral`, `compositeAPIntegral`, `compatibleAPMain`, `actualAPMain`, `actualPrimeAP_nonunit_zero`, les deux expansions AP et les deux restes réels.

Le module20 `SwitchedIncidenceEstimator` importe `CompositeAPConductor`; celui-ci importe `PhysicalCompositeSubtraction` et `RankCalibrationFace`. Les sources physiques18 ont le namespace `GoldbachRound18.SeparatedTypeII`. Les paramètres possèdent N,c,r,a,Q,M. Le témoin réel18 contient explicitement les quatre primalités, les ordres c<r<s, s≤a<q, cr≤a, cs≤a<rs<q, a<crs, b=s*q, unité, bulk et front strict original. Le futur bridge doit satisfaire ces champs réels; une somme AP générique seule ne remplace pas `actualPrimeAP` ou `actualCompositeAP`.

`physicalCompositeWindow_cap` prend la positivité du conducteur et l’appartenance à `physicalQDomain`, puis donne p²≤N et q≤(N−p²)/t. Il conserve l’égalité p²=j. `compatibleAPMain` garde sa branche non unitaire zéro; le conducteur partagé et son traitement des nonunités sont déjà acquis20.

## Sommation d’Abel : signature effective

Import : `Mathlib.NumberTheory.AbelSummation` (fichier lu FULL). Le théorème `_root_.sum_mul_eq_sub_sub_integral_mul` a comme paramètres de section `{𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ}` et comme hypothèses explicites :

* `ha : 0 ≤ a`, `hab : a ≤ b`;
* `hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t`;
* `hf_int : IntegrableOn (deriv f) (Set.Icc a b)`.

Sa conclusion utilise `∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k`. Les deux sommes partielles sont `∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k` et l’analogue en a. L’intégrale finale est **sur `Set.Ioc a b`**, du produit `deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k`. La conversion vers `∫t in a..b` est `intervalIntegral.integral_of_le hab`, dans le sens adapté. Aucun endpoint L ne doit remplacer implicitement A=L−1.

Attention API : les lemmes internes `abelSummationProof.integrablemulsum`, `integralmulsum`, `sumlocc` sont déclarés **private**. Ils ne sont pas des API publiques à invoquer par leur nom imprimé. Le nouveau module devra établir les obligations d’intégrabilité de ses produits/reste; le seul fait que la formule d’Abel compile dans mathlib ne donne pas cette obligation pour une nouvelle fonction.

## Variation réelle, intégrales et maximum fini

| Import local | Déclarations effectivement repérées | Forme utile de la signature |
|---|---|---|
| `Mathlib.Analysis.SpecialFunctions.Log.Deriv` | `Real.hasDerivAt_log`, `HasDerivAt.log`, `Real.deriv_log` | `HasDerivAt.log hf hx` exige `f x ≠ 0` et donne dérivée `f' / f x` |
| `Mathlib.Analysis.Calculus.Deriv.Inv` | `HasDerivAt.div` | dérivée `(c' * d x - c x * d') / d x ^ 2`, garde `d x ≠ 0` |
| `Mathlib.Analysis.Calculus.Deriv.Add`, `.Mul`, `.Basic` | `HasDerivAt.sub`, `.sub_const`, `.const_mul`, `.div_const`, `hasDerivAt_id`, `hasDerivAt_id'` | noms/signatures visibles dans les hits rg; aucun probe d’élaboration |
| `Mathlib.Analysis.Calculus.MeanValue` | `antitoneOn_of_deriv_nonpos`, `antitoneOn_of_hasDerivWithinAt_nonpos` | convexité, continuité sur D, dérivabilité/signe sur `interior D` |
| `Mathlib.MeasureTheory.Integral.FundThmCalculus` | `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `.integral_deriv_eq_sub`, `.integral_deriv_eq_sub'` | endpoints `uIcc`; `IntervalIntegrable` de la dérivée est une hypothèse réelle |
| même fichier | `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` | continuité u,v sur `uIcc`, dérivées sur `Ioo (min a b) (max a b)`, intégrabilité des deux dérivées |
| `Mathlib.MeasureTheory.Integral.IntervalIntegral` | `ContinuousOn.intervalIntegrable`, `.intervalIntegrable_of_Icc`, `intervalIntegral.abs_integral_le_integral_abs`, `.integral_mono_on` | `integral_mono_on` requiert hab et les deux intégrabilités avant sa borne pointwise |
| même fichier | `intervalIntegral.integral_of_le`, `.integral_neg`, `.integral_const_mul`, `.integral_mul_const`; `intervalIntegrable_iff_integrableOn_Icc_of_le` | conversions et algèbre des intégrales avec orientation explicite |
| `Mathlib.MeasureTheory.Function.LocallyIntegrable` | `ContinuousOn.integrableOn_Icc` | continuité sur le compact Icc donne `IntegrableOn` |
| `Mathlib.MeasureTheory.Function.Floor` | `Nat.measurable_floor`, `Measurable.nat_floor` | noms confirmés par recherche; facilite la mesurabilité des sommes partielles à floor |
| `Mathlib.Data.Finset.Lattice.Fold` | `Finset.sup'`, `sup'_le_iff`, `sup'_le`, `le_sup'`, `le_sup'_of_le` | `sup'` exige un Finset non vide, sans imposer de `OrderBot ℝ` |
| `Mathlib.Algebra.Order.Floor` | `Nat.floor_le`, `lt_floor_add_one`, `floor_natCast`, `floor_le_of_le`, `floor_eq_iff`, `floor_eq_on_Ico`, `Nat.le_ceil`, `Nat.ceil_le` | les bornes réelles de floor/ceil et leurs casts sont explicitement exposées |
| `Mathlib.Data.Nat.Defs` | `Nat.div_le_iff_le_mul_add_pred`, `Nat.le_div_iff_mul_le`, `Nat.div_lt_iff_lt_mul` | la première donne `a/b≤c ↔ a≤b*c+(b−1)` sous `0<b`; les deux dernières sont employées par les sources cache/acquises |
| `Mathlib.Analysis.SpecialFunctions.Pow.Real` | `Real.log_rpow` | `0<x` puis `log(x^y)=y*log x` |
| `Mathlib.Analysis.SpecialFunctions.Log.Basic` | `Real.log_nat_eq_sum_factorization` | `log n = n.factorization.sum (fun p t => t * log p)` |
| `Mathlib.Data.Nat.Factorization.Defs` | `Nat.support_factorization`, `Nat.Prime.factorization_pos_of_dvd` | support=facteurs premiers; exposant positif pour un premier divisant n≠0 |
| `Mathlib.Data.Nat.Totient` | `Nat.totient_pos` | équivalence `0 < φ n ↔ 0 < n` |

Il faudra distinguer les valeurs d’erreur après saut `Theta(m)−m/phi` et les limites avant le saut `Theta(m)−min(m+1,U)/phi`, avec le **même** Theta(m). Le maximum fini `sup'` est une API adaptée aux deux familles construites et non vides. L’inventaire ne prouve aucune domination d’erreur sur un segment ni équivalence avec sSup; ces énoncés appartiendront au travail autorisé après sélection.

Les sourceguards et la constante16/7 devront provenir des fonctions sourceceil/SourceOnset acquises et de nouvelles preuves explicites. Aucun champ libre « erreur petite », ni B6/SD, ni objectif D_N, n’est ajouté au contrat par cet inventaire. Le prix de tous les coefficients, les grands modules, slack/queue, M0 et le ledger restent ouverts.

## Lecture et traçabilité

`preparation_read_manifest.json` lie les bytes des fichiers consultés, avec scopes FULL/TARGETED honest et les chunks effectifs. PROBE21, candidat ROLE1, FINAL3_20, FINAL5_20, les trois sources20 et AbelSummation ont été lus intégralement. Le premier affichage combiné des sources20 avait subi une troncature globale; Estimator a été relu séparément FULL dans le chunkb8291d. Les autres fichiers cache et PhysicalWitness18 ont seulement une lecture ciblée aux déclarations/ranges mentionnées.

Plusieurs premières recherches rg ont rencontré des glob Windows non résolus ou un ancien chemin de module absent. Elles ont été remplacées par des chemins exacts/répertoires. Ce sont des échecs de recherche read-only, pas des invocations Lean, des erreurs de preuve, des FAIL mathématiques ou des tests numériques. Aucun résultat de ces recherches n’est crédité comme une victoire.

ROLE1 a reçu l’avertissement exact sur `Set.Ioc`, les hypothèses d’Abel et le front L−1. Root a reçu l’état de préparation sans compilation. Le travail de preuve et l’EXEC Lean attendent leurs autorisations de phase respectives.
