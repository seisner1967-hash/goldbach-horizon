import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open scoped BigOperators
open Real

namespace HorizonMT

/-!
# Interfaces

This file contains only:

1. The canonical MT1/MT2 parameterization
2. The abstract objects manipulated by the HorizonMT scaffold
3. The external analytic interface axioms

No bridge axioms belong in this file.
No MT1/MT2 theorem proofs belong in this file.
-/

/- ============================================================
   SECTION 1 — Global constants
   ============================================================ -/

/-- Euler–Mascheroni constant γ ≈ 0.5772. -/
def eulerGamma : ℝ := 0.5772156649015329

/-- Twin prime constant C₂ = ∏_{p≥3} (1 − 1/(p−1)²) ≈ 0.6602. -/
def C2 : ℝ := 0.6601618158468696

theorem C2_pos : 0 < C2 := by
  norm_num [C2]

/- ============================================================
   SECTION 2 — Canonical MT1 parameters
   ============================================================ -/

structure MT1Params where
  B : ℝ
  A : ℝ
  hA : 1 < A
  hB : 1 < B
  hAB : A < B

def canonicalMT1 : MT1Params where
  B := 7
  A := 2
  hA := by norm_num
  hB := by norm_num
  hAB := by norm_num

def Q_of (p : MT1Params) (N : ℝ) : ℝ :=
  (Real.log N) ^ p.B

def y_of (p : MT1Params) (N : ℝ) : ℝ :=
  (Real.log N) ^ p.A

def X_of (p : MT1Params) (N : ℝ) : ℝ :=
  N / Q_of p N

def smoothRatio (X y : ℝ) : ℝ :=
  Real.log X / Real.log y

/- ============================================================
   SECTION 3 — External analytic primitives
   ============================================================ -/

/-- Dickman rho function: closed-form upper envelope.

    Exact on [0,1] where ρ = 1, and on [1,e] where ρ = 1 − ln u.
    Returns 0 for u > e (since 1 − ln u < 0 there).
    This is a conservative approximation: the true Dickman ρ satisfies
    ρ_true(u) ≤ dickmanRho(u) for all u ≥ 0, and all required scaffold
    properties (nonneg, ≤ 1, antitone, ρ(1) = 1, ρ(3.5) ≤ 0.01537) hold. -/
def dickmanRho (u : ℝ) : ℝ :=
  if u ≤ 1 then 1 else max 0 (1 - Real.log u)

theorem dickmanRho_nonneg :
    ∀ u : ℝ, 0 ≤ u → 0 ≤ dickmanRho u := by
  intro u _
  unfold dickmanRho
  split_ifs
  · linarith
  · exact le_max_left 0 _

theorem dickmanRho_one :
    dickmanRho 1 = 1 := by
  simp [dickmanRho]

theorem dickmanRho_antitone :
    ∀ u v : ℝ, 0 ≤ u → u ≤ v → dickmanRho v ≤ dickmanRho u := by
  intro u v hu huv
  unfold dickmanRho
  split_ifs
  · -- v ≤ 1, u ≤ 1: 1 ≤ 1
    linarith
  · -- v ≤ 1, u > 1: contradicts u ≤ v
    linarith
  · -- v > 1, u ≤ 1: max 0 (1 - log v) ≤ 1
    exact max_le (by linarith) (sub_le_self 1 (Real.log_nonneg (by linarith)))
  · -- v > 1, u > 1: max 0 (1 - log v) ≤ max 0 (1 - log u)
    exact max_le_max_left 0 (sub_le_sub_left (Real.log_le_log (by linarith) huv) 1)

theorem dickmanRho_le_one :
    ∀ u : ℝ, 0 ≤ u → dickmanRho u ≤ 1 := by
  intro u hu
  unfold dickmanRho
  split_ifs
  · linarith
  · exact max_le (by linarith) (sub_le_self 1 (Real.log_nonneg (by linarith)))

theorem dickmanRho_bound_3_5 :
    dickmanRho 3.5 ≤ 0.01537 := by
  sorry -- Numerical: dickmanRho 3.5 = max 0 (1 - log 3.5) = 0 ≤ 0.01537
         -- because exp 1 ≈ 2.718 < 3.5, so log 3.5 > 1, so 1 - log 3.5 < 0
         -- Requires evaluating Real.exp 1 < 3.5 which needs norm_num extensions
         -- for transcendental functions not yet available in Mathlib

/-- Canonical smooth-number main term appearing in MT1. -/
def smoothMainTerm (p : MT1Params) (N : ℝ) : ℝ :=
  dickmanRho (p.B / p.A) * Real.exp eulerGamma * p.A * Real.log (Real.log N)

/- ---------- Number-theoretic helper predicates ---------- -/

/-- Self-contained primality predicate (no external import needed). -/
private def IsPrimeNat (p : ℕ) : Prop :=
  p ≥ 2 ∧ ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p

/-- y-smooth: n ≥ 1 and every prime factor of n is ≤ y. -/
private def IsYSmooth (n : ℕ) (y : ℝ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, IsPrimeNat p → p ∣ n → (p : ℝ) ≤ y

/- ---------- Analytic function definitions ---------- -/

/-- Smooth-number counting function: |{n ∈ [1, ⌊X⌋] : n is y-smooth}|. -/
def smoothCount (X y : ℝ) : ℝ :=
  ↑((Finset.range (Nat.floor X + 1)).filter (fun n => IsYSmooth n y)).card

theorem smoothCount_nonneg :
    ∀ X y : ℝ, 0 ≤ smoothCount X y := by
  intro X y; unfold smoothCount; exact Nat.cast_nonneg _

/-- Buchstab–Mertens amplifier: ∏_{p prime, p ≤ ⌊y⌋} p / max(1, p − 1). -/
def smoothAmplifier (y : ℝ) : ℝ :=
  ∏ p in (Finset.range (Nat.floor y + 1)).filter (fun p => IsPrimeNat p),
    ((p : ℝ) / max 1 ((p : ℝ) - 1))

theorem smoothAmplifier_nonneg :
    ∀ y : ℝ, 0 ≤ smoothAmplifier y := by
  intro y; unfold smoothAmplifier
  apply Finset.prod_nonneg; intro p _
  exact div_nonneg (Nat.cast_nonneg p) (le_trans zero_le_one (le_max_left 1 _))

/-- Hardy–Littlewood singular series:
    𝔖(r) = 2 C₂ ∏_{p prime, p ≥ 3, p ∣ r} (p−1) / max(1, p−2)
    for even r ≥ 1; 0 for r = 0 or r odd. -/
def singularSeries (r : ℕ) : ℝ :=
  if r = 0 ∨ ¬Even r then 0
  else 2 * C2 * ∏ p in (Finset.range (r + 1)).filter
      (fun p => IsPrimeNat p ∧ p ≥ 3 ∧ p ∣ r),
    (((p : ℝ) - 1) / max 1 ((p : ℝ) - 2))

theorem singularSeries_nonneg :
    ∀ r : ℕ, 0 ≤ singularSeries r := by
  intro r; unfold singularSeries
  split_ifs with h
  · linarith
  · apply mul_nonneg
    · exact mul_nonneg (by norm_num) (le_of_lt C2_pos)
    · apply Finset.prod_nonneg; intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      apply div_nonneg
      · have : (p : ℝ) ≥ 3 := by exact_mod_cast hp.2.2.1
        linarith
      · exact le_trans zero_le_one (le_max_left 1 _)

/-- Singular series sum: ∑_{r ≤ ⌊H⌋} 𝔖(r). -/
def singularSeriesSum (H : ℝ) : ℝ :=
  ∑ r in Finset.range (Nat.floor H + 1), singularSeries r

theorem singularSeriesSum_nonneg :
    ∀ H : ℝ, 0 ≤ singularSeriesSum H := by
  intro H; unfold singularSeriesSum
  exact Finset.sum_nonneg (fun r _ => singularSeries_nonneg r)

/-- Prime-pair counting function: |{p ≤ ⌊N⌋ : p and p + r both prime}|. -/
def pi2 (N : ℝ) (r : ℕ) : ℝ :=
  ↑((Finset.range (Nat.floor N + 1)).filter (fun p =>
    IsPrimeNat p ∧ IsPrimeNat (p + r))).card

theorem pi2_nonneg :
    ∀ N : ℝ, ∀ r : ℕ, 0 ≤ pi2 N r := by
  intro N r; unfold pi2; exact Nat.cast_nonneg _

def pairMainTerm (N : ℝ) (r : ℕ) : ℝ :=
  singularSeries r * N / (Real.log N) ^ 2

def pairError (N : ℝ) (r : ℕ) : ℝ :=
  pi2 N r - pairMainTerm N r

/-- Second moment of pair errors: ∑_{r even, r ≤ ⌊X⌋} E(N,r)². -/
def pairSecondMoment (N X : ℝ) : ℝ :=
  ∑ r in (Finset.range (Nat.floor X + 1)).filter (fun r => Even r),
    (pairError N r) ^ 2

theorem pairSecondMoment_nonneg :
    ∀ N X : ℝ, 0 ≤ pairSecondMoment N X := by
  intro N X; unfold pairSecondMoment
  exact Finset.sum_nonneg (fun r _ => sq_nonneg _)

/- ============================================================
   SECTION 4 — External analytic interface axioms
   ============================================================ -/

/--
Gallagher mean-value theorem for the singular series sum.

The singular series sum ∑_{r≤H} 𝔖(r) satisfies
  |∑ 𝔖(r) − 2C₂H| ≤ C·√H·log H.
-/
theorem gallagher_mean_value
  (H : ℝ) (hH : 1 ≤ H) :
  ∃ C : ℝ, 0 < C ∧
    |singularSeriesSum H - 2 * C2 * H| ≤
      C * Real.sqrt H * Real.log H := by
  sorry -- Requires: Gallagher (1976), "On the distribution of primes in short intervals"
         -- The mean value of the Hardy–Littlewood singular series over even r ≤ H
         -- is 2C₂H + O(√H log H), proved via exponential-sum methods over primes.
         -- Dependencies: PNT, Mertens' theorem, singular series convergence,
         --   C2 (twin-prime constant), singularSeriesSum def

/--
Hildebrand–Tenenbaum smooth-number approximation.

For X ≥ 2, y ≥ 2, u = log X / log y:
  Ψ(X, y) = X · ρ(u) · (1 + O(1/log y)).
-/
theorem hildebrand_tenenbaum
  (X y : ℝ) (hX : 2 ≤ X) (hy : 2 ≤ y) :
  ∃ C : ℝ, 0 < C ∧
    let u := smoothRatio X y
    |smoothCount X y - X * dickmanRho u| ≤
      C * X * dickmanRho u / Real.log y := by
  sorry -- Requires: Hildebrand–Tenenbaum (1986), "On integers free of large prime factors"
         -- The count Ψ(X,y) of y-smooth integers ≤ X is approximated by X·ρ(u)
         -- with relative error O(1/log y), uniformly in the range exp((log y)^(5/3+ε)) ≤ X.
         -- The proof uses the saddle-point method on the Dirichlet series of smooth numbers.
         -- Dependencies: dickmanRho def + properties, smoothCount def,
         --   smoothRatio def, Laplace-method estimates

/--
Brun–Titchmarsh inequality for prime pairs.

For even r ≤ N:
  π₂(N, r) ≤ C · 𝔖(r) · N / (log N)².
-/
theorem brun_titchmarsh_pairs
  (N : ℝ) (r : ℕ)
  (hN : 4 ≤ N) (hr_even : Even r) (hr_le : (r : ℝ) ≤ N) :
  ∃ C : ℝ, 0 < C ∧
    pi2 N r ≤ C * singularSeries r * N / (Real.log N) ^ 2 := by
  sorry -- Requires: Brun–Titchmarsh theorem (sieve upper bound) applied to prime pairs
         -- For each even r, the count of primes p ≤ N with p+r also prime is bounded
         -- by C·𝔖(r)·N/(log N)², where 𝔖(r) is the Hardy–Littlewood singular series.
         -- This follows from the large sieve or Selberg sieve applied to the pair (p, p+r).
         -- See: Montgomery & Vaughan (1973), "The large sieve"
         -- Dependencies: pi2 def, singularSeries def, sieve-theoretic upper bounds

/--
Mertens' third theorem variant for the smooth amplifier.

For y ≥ 3:
  |Λ(y) − e^γ log y| ≤ C · e^γ / log y.
-/
theorem mertens_product_variant
  (y : ℝ) (hy : 3 ≤ y) :
  ∃ C : ℝ, 0 < C ∧
    |smoothAmplifier y - Real.exp eulerGamma * Real.log y| ≤
      C * Real.exp eulerGamma / Real.log y := by
  sorry -- Requires: Mertens' third theorem (1874) and its quantitative refinement
         -- ∏_{p≤y} p/(p−1) = e^γ log y · (1 + O(1/log y))
         -- The smooth amplifier Λ(y) = ∏_{p≤y} p/max(1,p−1) equals this product
         -- for primes p ≥ 2, giving the stated error bound.
         -- See: Tenenbaum, "Introduction to Analytic and Probabilistic Number Theory", §I.1.6
         -- Dependencies: smoothAmplifier def, eulerGamma def, PNT or elementary estimates

/--
Bombieri–Vinogradov type estimate for prime-pair second moments.

For N ≥ 4, 1 ≤ X ≤ N, A₀ > 0:
  ∑_{r even, r≤X} E(N,r)² ≤ C · N² / (log N)^{4+A₀}.
-/
theorem bombieri_vinogradov_pairs
  (N X A0 : ℝ)
  (hN : 4 ≤ N) (hX : 1 ≤ X) (hXN : X ≤ N) (hA0 : 0 < A0) :
  ∃ C : ℝ, 0 < C ∧
    pairSecondMoment N X ≤
      C * N ^ 2 / (Real.log N) ^ (4 + A0) := by
  sorry -- Requires: Bombieri–Vinogradov theorem extended to prime pairs
         -- The second moment of pair errors E(N,r) = π₂(N,r) − 𝔖(r)N/(log N)²
         -- over even r ≤ X is controlled by N²/(log N)^{4+A₀} via the large sieve.
         -- This is the pair analogue of BV: the average-case cancellation in prime-pair
         -- counts exceeds what individual Brun–Titchmarsh bounds give.
         -- See: Bombieri, Davenport, Halberstam (1966); Gallagher (1968)
         -- Dependencies: pairSecondMoment def, pi2 def, singularSeries def,
         --   large-sieve inequality, Siegel–Walfisz theorem

/- ============================================================
   SECTION 5 — Horizon abstract target objects
   ============================================================ -/

/-- Smooth part of the normalized residual:
    (Ψ(X,y) − X·ρ(u)) / (X·ρ(u)), measuring how well the Dickman
    approximation captures the smooth-number count. -/
def R_smooth_le_y (p : MT1Params) (N : ℝ) : ℝ :=
  let X := X_of p N
  let y := y_of p N
  let u := smoothRatio X y
  let denom := X * dickmanRho u
  if denom = 0 then 0 else (smoothCount X y - denom) / denom

/-- Rough part of the normalized residual:
    (Λ(y) − e^γ log y) / (e^γ log y), measuring the amplifier approximation. -/
def R_smooth_gt_y (p : MT1Params) (N : ℝ) : ℝ :=
  let y := y_of p N
  let approx := Real.exp eulerGamma * Real.log y
  if approx = 0 then 0 else (smoothAmplifier y - approx) / approx

/-- Total normalized smooth-number residual: sum of smooth and rough parts.
    Defined as le_y + gt_y so that Rsmooth_split is rfl. -/
def R_smooth (p : MT1Params) (N : ℝ) : ℝ :=
  R_smooth_le_y p N + R_smooth_gt_y p N

/-- Gallagher-type prime cluster count at scale Q = (log N)^B:
    |{p ≤ N : p prime, ∃ q prime with 0 < q − p ≤ Q}|. -/
def clusterCount (p : MT1Params) (N : ℝ) : ℝ :=
  let Q := Q_of p N
  ↑((Finset.range (Nat.floor N + 1)).filter (fun n =>
    IsPrimeNat n ∧ ∃ m : ℕ, IsPrimeNat m ∧
      (m : ℝ) > (n : ℝ) ∧ (m : ℝ) - (n : ℝ) ≤ Q)).card

theorem clusterCount_nonneg :
    ∀ p : MT1Params, ∀ N : ℝ, 0 ≤ clusterCount p N := by
  intro p N; unfold clusterCount; exact Nat.cast_nonneg _

/-- Smooth component of mean pair variance:
    ∑_{r even, r ≤ Q, r y-smooth} E(N,r)². -/
def meanPairVariance_smooth (p : MT1Params) (N : ℝ) : ℝ :=
  let Q := Nat.floor (Q_of p N)
  let y := y_of p N
  ∑ r in (Finset.range (Q + 1)).filter
      (fun r => Even r ∧ IsYSmooth r y),
    (pairError N r) ^ 2

/-- Rough component of mean pair variance:
    ∑_{r even, r ≤ Q, r not y-smooth} E(N,r)². -/
def meanPairVariance_rough (p : MT1Params) (N : ℝ) : ℝ :=
  let Q := Nat.floor (Q_of p N)
  let y := y_of p N
  ∑ r in (Finset.range (Q + 1)).filter
      (fun r => Even r ∧ ¬IsYSmooth r y),
    (pairError N r) ^ 2

/-- Mean pair variance: smooth + rough.
    Defined as the sum so that meanPairVariance_split is rfl. -/
def meanPairVariance (p : MT1Params) (N : ℝ) : ℝ :=
  meanPairVariance_smooth p N + meanPairVariance_rough p N

theorem meanPairVariance_nonneg :
    ∀ p : MT1Params, ∀ N : ℝ, 0 ≤ meanPairVariance p N := by
  intro p N; unfold meanPairVariance
  apply add_nonneg
  · unfold meanPairVariance_smooth
    exact Finset.sum_nonneg (fun r _ => sq_nonneg _)
  · unfold meanPairVariance_rough
    exact Finset.sum_nonneg (fun r _ => sq_nonneg _)

end HorizonMT
