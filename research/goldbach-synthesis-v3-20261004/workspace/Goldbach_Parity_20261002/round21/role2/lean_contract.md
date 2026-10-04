# Contrat Lean21 ROLE2 — signatures concrètes non compilées

Ces déclarations décrivent les résultats à implémenter après une gate numérique distincte. Elles n'ont pas de preuve exécutée et ne donnent aucun PASS. Ne pas créer des axiomes, `sorry`, `admit`, unsafe, native_decide ou hypothèse libre de moment/cardinal/coût. Toutes les déclarations explicites nouvelles doivent avoir `#print axioms` qualifié, puis une compilation indépendante des seuls nouveaux modules.

Imports readonly audités : `FriableSourceBudget`, `FriableDemandAggregation`, `FriablePhysicalPayment`, `FriablePhysicalPrefix`, `FriableSourceGeometry`, via **round20/judge/audit**, puis caches historiques19/18/16/13. Les sources auteurs20 ne servent pas à reconstruire ces modules. Les imports de mathlib sont ceux du cache9837ca9 : `Mathlib.NumberTheory.ArithmeticFunction`, `Mathlib.NumberTheory.Harmonic.Bounds`, `Mathlib.Algebra.Order.BigOperators.Ring.Finset`, et les APIs Nat gcd/lcm/divisors déjà importées. Le chemin Harmonic local a été vérifié par rg ; ne pas remplacer ces API par une API web récente non présente.

Namespace proposé `GoldbachRound21.NonfriableReciprocal`, open GoldbachRound19.NonSS, GoldbachRound19.Switch, GoldbachRound20.Friable et GoldbachRound20.Friable.SourceGeometry.

## Module1 DivisorSecondMoment

Définir un vrai domaine fini de quadruplets positifs et de produit n, puis d4(n) son cardinal :

```lean
def factorQuadDomain (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Finset.Icc 1 n).product (Finset.Icc 1 n)).product
    ((Finset.Icc 1 n).product (Finset.Icc 1 n))).filter
    (fun v => v.1.1 * v.1.2 * v.2.1 * v.2.2 = n)

def fourDivisorCount (n : ℕ) : ℕ := (factorQuadDomain n).card

-- À prouver par injection (r,s) -> ((gcd r s,r/gcd r s),(s/gcd r s,n/lcm r s)).
theorem actual_tau_square_le_fourDivisorCount (n : ℕ) :
  tau n ^ 2 ≤ (fourDivisorCount n : ℝ)

-- À prouver par reindexation des quadruplets et floor<=quotient, pas en prémisse.
theorem actual_four_divisor_sum_le_harmonic_cube (N : ℕ) :
  (∑ n ∈ Finset.Icc 1 N, (fourDivisorCount n : ℝ)) ≤
    (N : ℝ) * (harmonic N : ℝ) ^ 3

theorem actual_tau_second_moment_le_harmonic_cube (N : ℕ) :
  (∑ n ∈ Finset.Icc 1 N, tau n ^ 2) ≤
    (N : ℝ) * (harmonic N : ℝ) ^ 3

theorem actual_tau_second_moment_le_eight {N : ℕ}
  (hu : 1 ≤ Real.log (N : ℝ)) :
  (∑ n ∈ Finset.Icc 1 N, tau n ^ 2) ≤ 8*(N : ℝ)*Real.log (N : ℝ)^3
```

Un remplacement de factorQuadDomain par le vrai ζ^4 est permis seulement avec un raccord démontré. Aucun moment générique supposé bon ne remplace la dernière conclusion.

## Module2 NonfriableReciprocalProjection

```lean
def labels0not1 (alpha N Z M Y : ℕ) : Finset (ℕ × ℕ) :=
  (physicalDomain alpha N Z M).filter (fun v =>
    Smooth Y (resource0 N v.2) ∧ ¬ Smooth Y (resource1 N v.2))

def q0not1 (alpha N Z M Y : ℕ) : Finset ℕ :=
  (labels0not1 alpha N Z M Y).image (fun v => v.2)

def q01 (alpha N Z M Y : ℕ) : Finset ℕ :=
  (friableDemandDomain alpha N Z M Y).image (fun v => v.2)

theorem q0not1_witness {alpha N Z M Y q : ℕ}
  (hq : q ∈ q0not1 alpha N Z M Y) :
  ∃ e, StructuralSupport alpha N Z M e q ∧
    Smooth Y (resource0 N q) ∧ ¬ Smooth Y (resource1 N q)

theorem q0not1_resource_injective (alpha N Z M Y : ℕ) :
  Set.InjOn (resource1 N) (q0not1 alpha N Z M Y)

theorem q01_partition (alpha N Z M Y : ℕ) :
  q01 alpha N Z M Y = friableQ1 alpha N Z M Y ∪ q0not1 alpha N Z M Y

theorem q01_partition_disjoint (alpha N Z M Y : ℕ) :
  Disjoint (friableQ1 alpha N Z M Y) (q0not1 alpha N Z M Y)

theorem actual_q0not1_card_le_mass {alpha N Z M D Y : ℕ}
  (hD : 1 < D) (hDM : D ≤ M) (hY : 0 < Y) :
  ((q0not1 alpha N Z M Y).card : ℝ) ≤
    (N : ℝ) * (∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹) +
      ((divisorBand D Y).card : ℝ)

theorem actual_source_q0not1_card_le_three {N : ℕ} (h : SourceOnset N) :
  ((q0not1 (sourceAlpha N) N (sourceZ N) (sourceM N) (sourceY N)).card : ℝ) ≤
    3*(N : ℝ)*sourceU N ^ (-37 : ℝ)
```

Le domaine peut être vide ; l'inégalité conserve +1 pour toute classe non vide et laisse les non-unités exactes vides. L'existence variable de e ne doit jamais devenir un e commun gratuit. Réutiliser `resource0_divisor_class`, `anchor_resource0_coprime`, le certificat20 et le lemme fini de classe sur [M,N].

## Module3 NonfriableReciprocalBudget

```lean
def uniqueF0notF1Cost (alpha a N Z M Y : ℕ) : ℝ :=
  ∑ q ∈ q0not1 alpha N Z M Y,
    |GoldbachRound11.sourceBracket alpha a N q (resource1 N q)|

def sourceUniqueF0notF1Cost (N : ℕ) : ℝ :=
  uniqueF0notF1Cost (sourceAlpha N) (sourceA N) N
    (sourceZ N) (sourceM N) (sourceY N)

def sourceExtendedFriableCost (N : ℕ) : ℝ :=
  sourceFriableAbsoluteCost N + sourceUniqueF0notF1Cost N

theorem actual_source_q0not1_tau_sum_le_five {N : ℕ} (h : SourceOnset N) :
  (∑ q ∈ q0not1 (sourceAlpha N) N (sourceZ N) (sourceM N) (sourceY N),
    tau (resource1 N q)) ≤ 5*(N : ℝ)*sourceU N ^ (-17 : ℝ)

theorem actual_source_F0notF1_reciprocal_le_thirty_five {N : ℕ}
  (h : SourceOnset N) :
  sourceUniqueF0notF1Cost N ≤ 35*(N : ℝ)*sourceU N ^ (-14 : ℝ)

theorem actual_source_extended_friable_cost_budget {N : ℕ}
  (h : SourceOnset N) :
  sourceExtendedFriableCost N ≤ (N : ℝ)/(8192*sourceU N*sourceEll N)
```

Ajouter les images physiques de demande `(N-e*q,e*q)` et de réciproque `(q,N-q)`, leur union réelle, et le lemme `union_abs_cost_le_extended_cost` avec le vrai sourceBracket. Il doit conserver chaque paire une fois ; l'intersection peut être surmajorée positivement pour cette borne, sans être deux capacités. Le wrapper source de cette union doit conclure le même1/8192. La preuve n'a pas besoin d'une hypothèse de parent favorable, d'une borne Omega ou d'un field `smallCost`.

Les imports réels suffisent à dériver les gardes source. N=10^8 reste une annexe finie où les gardes asymptotiques sont fausses ; aucune hypothèse `SourceOnset 100000000` n'est introduite. Tous les quatre modules éventuels, si l'union est séparée, restent des ingrédients auxiliaires même après PASS indépendant.
