import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic
import TS.Goldbach.Strong.TS279.BufferedQuotientHolomorphicLogConstruction
import TS.Goldbach.Strong.TS295.StrongCleanHeightLogDerivativeReduction

/-!
# TS296 - Concrete Strong Heights and the Exact Height Quotient

TS295 reduced a horizontal logarithmic-derivative estimate to a finite
reciprocal zero load and a local holomorphic logarithm.  This module constructs
both objects without introducing a new existence hypothesis.

For each natural height `T`, a canonical point in `(T,T+1)` is chosen outside
the finite set of nearby zero ordinates.  The minimum finite gap, capped by
`1`, supplies a positive separation.  The corresponding exact reciprocal
load is used as the first concrete load envelope.

The quotient used here is indexed by exactly the same height finset as the
rational sum:

`xi(z) / product_{|Im rho| <= T+2} (z-rho)^m(rho)`.

On the small horizontal balls this polynomial and xi are nonzero.  Hence the
quotient is analytic and nonvanishing there.  TS279, instantiated with an
empty local Jensen zero family, then constructs a holomorphic logarithm.
The logarithm receives a canonical compact sphere bound, and the exact
finite-product logarithmic-derivative identity is proved.

The construction is unconditional but the first load envelope is exact and
noncomputable; this sprint does not yet prove the desired
`O(T * log(T+2)^2)` closed envelope or its decay after division by `T^2`.
It also does not pass from `xi'/xi` to `-zeta'/zeta`, estimate the left side
or right cutoff, prove Perron inversion or the meromorphic residue theorem,
or claim an infinite explicit formula, Gallagher, OTSA, or Goldbach.
-/

noncomputable section

namespace TS296
namespace Goldbach

open Complex Filter Metric Set Topology
open scoped BigOperators

/-- Nearby absolute zero ordinates, with duplicate ordinates removed. -/
noncomputable def nearbyZeroHeights (T : Nat) : Finset Real :=
  (TS295.Goldbach.nearbyConcreteZeros T).image
    (fun rho => _root_.abs rho.1.im)

theorem nearbyZeroHeights_finite (T : Nat) :
    ((nearbyZeroHeights T : Finset Real) : Set Real).Finite :=
  Set.toFinite _

/-- There is a point of `(T,T+1)` outside all nearby zero ordinates. -/
theorem exists_height_avoiding_nearby_zeros (T : Nat) :
    Exists fun tau : Real =>
      (T : Real) < tau /\
        tau < (T : Real) + 1 /\
          Not (Membership.mem (nearbyZeroHeights T) tau) := by
  have hInterval :
      (Set.Ioo (T : Real) ((T : Real) + 1)).Infinite :=
    Set.Ioo_infinite (by linarith)
  let tau : Real :=
    Classical.choose
      (hInterval.exists_not_mem_finite (nearbyZeroHeights_finite T))
  have hData :=
    Classical.choose_spec
      (hInterval.exists_not_mem_finite (nearbyZeroHeights_finite T))
  exact Exists.intro tau
    (And.intro hData.1.1
      (And.intro hData.1.2 (by simpa using hData.2)))

/-- Canonically chosen clean height. -/
noncomputable def strongHeightTau (T : Nat) : Real :=
  Classical.choose (exists_height_avoiding_nearby_zeros T)

theorem strongHeightTau_gt (T : Nat) :
    (T : Real) < strongHeightTau T :=
  (Classical.choose_spec (exists_height_avoiding_nearby_zeros T)).1

theorem strongHeightTau_lt (T : Nat) :
    strongHeightTau T < (T : Real) + 1 :=
  (Classical.choose_spec (exists_height_avoiding_nearby_zeros T)).2.1

theorem strongHeightTau_not_mem (T : Nat) :
    Not (Membership.mem (nearbyZeroHeights T) (strongHeightTau T)) :=
  (Classical.choose_spec (exists_height_avoiding_nearby_zeros T)).2.2

theorem strongHeightTau_pos {T : Nat} (hT : 1 <= T) :
    0 < strongHeightTau T := by
  have hTReal : (0 : Real) < (T : Real) := by
    exact_mod_cast (show (0 : Nat) < T by omega)
  exact hTReal.trans (strongHeightTau_gt T)

theorem strongHeight_gap_ne_zero
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    Not
      (TS295.Goldbach.symmetricZeroHeightGap
        (strongHeightTau T) rho = 0) := by
  intro hGap
  have hEq :
      strongHeightTau T = _root_.abs rho.1.im := by
    exact sub_eq_zero.mp (abs_eq_zero.mp hGap)
  apply strongHeightTau_not_mem T
  rw [hEq]
  exact Finset.mem_image.mpr (Exists.intro rho (And.intro hRho rfl))

theorem strongHeight_gap_pos
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    0 <
      TS295.Goldbach.symmetricZeroHeightGap
        (strongHeightTau T) rho :=
  lt_of_le_of_ne (abs_nonneg _)
    (Ne.symm (strongHeight_gap_ne_zero T rho hRho))

/-- Minimum nearby gap, with value `1` for an empty zero finset. -/
noncomputable def rawStrongHeightDelta (T : Nat) : Real :=
  if h : (TS295.Goldbach.nearbyConcreteZeros T).Nonempty then
    ((TS295.Goldbach.nearbyConcreteZeros T).image
      (TS295.Goldbach.symmetricZeroHeightGap (strongHeightTau T))).min'
        (h.image _)
  else
    1

/-- Positive separation capped by `1`, which fixes a uniform local radius. -/
noncomputable def strongHeightDelta (T : Nat) : Real :=
  min 1 (rawStrongHeightDelta T)

theorem rawStrongHeightDelta_pos (T : Nat) :
    0 < rawStrongHeightDelta T := by
  classical
  unfold rawStrongHeightDelta
  split_ifs with h
  case pos =>
    let gaps :=
      (TS295.Goldbach.nearbyConcreteZeros T).image
        (TS295.Goldbach.symmetricZeroHeightGap (strongHeightTau T))
    have hMem :
        Membership.mem gaps (gaps.min' (h.image _)) :=
      Finset.min'_mem gaps (h.image _)
    let rho := Classical.choose (Finset.mem_image.mp hMem)
    have hData := Classical.choose_spec (Finset.mem_image.mp hMem)
    rw [<- hData.2]
    exact strongHeight_gap_pos T rho hData.1
  case neg =>
    norm_num

theorem strongHeightDelta_pos (T : Nat) :
    0 < strongHeightDelta T := by
  unfold strongHeightDelta
  exact lt_min (by norm_num) (rawStrongHeightDelta_pos T)

theorem strongHeightDelta_le_one (T : Nat) :
    strongHeightDelta T <= 1 :=
  min_le_left _ _

theorem strongHeightDelta_le_gap
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    strongHeightDelta T <=
      TS295.Goldbach.symmetricZeroHeightGap (strongHeightTau T) rho := by
  classical
  unfold strongHeightDelta
  refine (min_le_right _ _).trans ?_
  unfold rawStrongHeightDelta
  have hNonempty :
      (TS295.Goldbach.nearbyConcreteZeros T).Nonempty :=
    Exists.intro rho hRho
  rw [dif_pos hNonempty]
  apply Finset.min'_le
  exact Finset.mem_image.mpr (Exists.intro rho (And.intro hRho rfl))

/-- The first concrete load envelope is the exact load at the chosen height. -/
noncomputable def strongHeightLoadEnvelope (T : Nat) : Real :=
  TS295.Goldbach.reciprocalZeroLoad T (strongHeightTau T)

theorem strongHeightLoadEnvelope_nonnegative (T : Nat) :
    0 <= strongHeightLoadEnvelope T :=
  TS295.Goldbach.reciprocalZeroLoad_nonnegative _ _

/-- A zeta zero on the fixed strip and at nonzero height is nontrivial. -/
theorem zeta_zero_in_fixed_strip_is_concrete
    {s : Complex}
    (hLeft : TS294.Goldbach.fixedPerronLeft <= s.re)
    (hRight : s.re <= TS294.Goldbach.fixedPerronRight)
    (hIm : Not (s.im = 0))
    (hZero : riemannZeta s = 0) :
    TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet s := by
  have _hGeometry :
      TS294.Goldbach.fixedPerronLeft <=
        TS294.Goldbach.fixedPerronRight :=
    hLeft.trans hRight
  have hReLtOne : s.re < 1 := by
    by_contra h
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h)) hZero
  have hRePos : 0 < s.re := by
    by_contra h
    have hOneSubRe : 1 <= (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hOneSubNe : Not (riemannZeta (1 - s) = 0) :=
      riemannZeta_ne_zero_of_one_le_re hOneSubRe
    have hNotNegNat : forall n : Nat, Not (s = -(n : Complex)) := by
      intro n hEq
      have := congrArg Complex.im hEq
      simp [hIm] at this
    have hNeOne : Not (s = 1) := by
      intro hEq
      have := congrArg Complex.im hEq
      simp [hIm] at this
    apply hOneSubNe
    rw [riemannZeta_one_sub hNotNegNat hNeOne, hZero]
    simp
  exact And.intro
    (by
      simpa [TS185.Goldbach.riemannZetaZeroPredicate,
        TS185.Goldbach.mathlibRiemannZetaFunction] using hZero)
    (by
      unfold TS185.Goldbach.criticalStripPredicate
      exact And.intro hRePos hReLtOne)

/-- Top horizontal side is zero-free at the chosen height. -/
theorem riemannZeta_ne_zero_on_strongHeight_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigmaLeft : TS294.Goldbach.fixedPerronLeft <= sigma)
    (hSigmaRight : sigma <= TS294.Goldbach.fixedPerronRight) :
    Not
      (riemannZeta
        ((sigma : Complex) + (strongHeightTau T : Complex) * I) = 0) := by
  intro hZero
  let s : Complex :=
    (sigma : Complex) + (strongHeightTau T : Complex) * I
  have hConcrete :
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet s := by
    exact zeta_zero_in_fixed_strip_is_concrete
      (by simpa [s] using hSigmaLeft)
      (by simpa [s] using hSigmaRight)
      (by simp [s, ne_of_gt (strongHeightTau_pos hT)])
      hZero
  let rho : TS292.Goldbach.ConcreteNontrivialZero :=
    Subtype.mk s hConcrete
  have hHeight :
      _root_.abs rho.1.im <= (T : Real) + 2 := by
    dsimp [rho, s]
    simp [abs_of_pos (strongHeightTau_pos hT)]
    linarith [strongHeightTau_lt T]
  have hRho :
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho := by
    apply
      (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
        (T + 2) rho).mpr
    exact hHeight.trans_eq (by push_cast; ring)
  have hGap :=
    strongHeight_gap_ne_zero T rho hRho
  apply hGap
  simp [TS295.Goldbach.symmetricZeroHeightGap, rho, s,
    abs_of_pos (strongHeightTau_pos hT)]

/-- Bottom horizontal side is zero-free at the chosen height. -/
theorem riemannZeta_ne_zero_on_strongHeight_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigmaLeft : TS294.Goldbach.fixedPerronLeft <= sigma)
    (hSigmaRight : sigma <= TS294.Goldbach.fixedPerronRight) :
    Not
      (riemannZeta
        ((sigma : Complex) - (strongHeightTau T : Complex) * I) = 0) := by
  intro hZero
  let s : Complex :=
    (sigma : Complex) - (strongHeightTau T : Complex) * I
  have hConcrete :
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet s := by
    exact zeta_zero_in_fixed_strip_is_concrete
      (by simpa [s] using hSigmaLeft)
      (by simpa [s] using hSigmaRight)
      (by simp [s, ne_of_gt (strongHeightTau_pos hT)])
      hZero
  let rho : TS292.Goldbach.ConcreteNontrivialZero :=
    Subtype.mk s hConcrete
  have hHeight :
      _root_.abs rho.1.im <= (T : Real) + 2 := by
    dsimp [rho, s]
    simp [abs_of_pos (strongHeightTau_pos hT)]
    linarith [strongHeightTau_lt T]
  have hRho :
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho := by
    apply
      (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
        (T + 2) rho).mpr
    exact hHeight.trans_eq (by push_cast; ring)
  have hGap :=
    strongHeight_gap_ne_zero T rho hRho
  apply hGap
  simp [TS295.Goldbach.symmetricZeroHeightGap, rho, s,
    abs_of_pos (strongHeightTau_pos hT)]

/-- The fixed left edge contains no zeta zero. -/
theorem riemannZeta_ne_zero_on_fixed_left
    (t : Real) :
    Not
      (riemannZeta
        ((TS294.Goldbach.fixedPerronLeft : Complex) +
          (t : Complex) * I) = 0) := by
  intro hZero
  let s : Complex :=
    (TS294.Goldbach.fixedPerronLeft : Complex) + (t : Complex) * I
  have hOneSubRe : 1 <= (1 - s).re := by
    norm_num [s, TS294.Goldbach.fixedPerronLeft]
  have hOneSubNe : Not (riemannZeta (1 - s) = 0) :=
    riemannZeta_ne_zero_of_one_le_re hOneSubRe
  have hNotNegNat : forall n : Nat, Not (s = -(n : Complex)) := by
    intro n hEq
    have hRe := congrArg Complex.re hEq
    simp [s, TS294.Goldbach.fixedPerronLeft] at hRe
    have hTwice : (2 * n : Real) = 3 := by
      linarith
    have hTwiceNat : 2 * n = 3 := by
      exact_mod_cast hTwice
    omega
  have hNeOne : Not (s = 1) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    norm_num [s, TS294.Goldbach.fixedPerronLeft] at hRe
  apply hOneSubNe
  rw [riemannZeta_one_sub hNotNegNat hNeOne, hZero]
  simp

/-- Concrete quantitatively clean contour at the canonical height. -/
noncomputable def strongCleanPerronContourData
    (T : Nat)
    (hT : 1 <= T) :
    TS294.Goldbach.QuantitativelyCleanPerronContourData T where
  left := TS294.Goldbach.fixedPerronLeft
  right := TS294.Goldbach.fixedPerronRight
  tau := strongHeightTau T
  left_lt_neg_one := TS294.Goldbach.fixedPerronLeft_lt_neg_one
  one_lt_right := TS294.Goldbach.one_lt_fixedPerronRight
  tau_pos := strongHeightTau_pos hT
  height_ge := (strongHeightTau_gt T).le
  height_le := (strongHeightTau_lt T).le
  zeta_nonzero_on_bottom := by
    intro sigma hLeft hRight
    exact
      riemannZeta_ne_zero_on_strongHeight_bottom
        T hT sigma hLeft hRight
  zeta_nonzero_on_top := by
    intro sigma hLeft hRight
    exact
      riemannZeta_ne_zero_on_strongHeight_top
        T hT sigma hLeft hRight
  zeta_nonzero_on_left := by
    intro t _ _
    exact riemannZeta_ne_zero_on_fixed_left t
  left_eq_fixed := rfl
  right_eq_fixed := rfl
  zeroSeparation := strongHeightDelta T
  zeroSeparation_pos := strongHeightDelta_pos T
  separated_from_nearby_zeros := by
    intro rho hRho
    apply strongHeightDelta_le_gap
    apply
      (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
        (T + 2) rho).mpr
    exact hRho.trans_eq (by push_cast; ring)

/-- The canonical functions inhabit TS295's strong-height contract. -/
theorem strongCleanPerronContourExistence :
  TS295.Goldbach.StrongCleanPerronContourExistenceStatement
      strongHeightDelta strongHeightLoadEnvelope := by
  intro T hT
  exact Exists.intro (strongCleanPerronContourData T hT)
    (And.intro le_rfl le_rfl)

/-! ## The exact height polynomial and quotient -/

/-- Xi is nonzero in the closed half-plane `Re(s) >= 1`. -/
theorem riemannXiCandidate_ne_zero_of_one_le_re
    {s : Complex}
    (hsRe : 1 <= s.re) :
    Not (TS282.Goldbach.riemannXiCandidate s = 0) := by
  by_cases hsOne : s = 1
  case pos =>
    subst s
    rw [TS282.Goldbach.riemannXiCandidate_one]
    norm_num
  case neg =>
    have hsZero : Not (s = 0) := by
      intro hs
      subst s
      norm_num at hsRe
    have hsRePos : 0 < s.re := zero_lt_one.trans_le hsRe
    have hZetaNe : Not (riemannZeta s = 0) :=
      riemannZeta_ne_zero_of_one_le_re hsRe
    have hCompletedNe : Not (completedRiemannZeta s = 0) := by
      intro hCompleted
      apply hZetaNe
      rw [TS282.Goldbach.riemannZeta_eq_completed_mul_gammaInv hsZero,
        hCompleted]
      simp
    rw [TS282.Goldbach.riemannXiCandidate_eq_completedRiemannZeta_mul
      hsZero hsOne]
    exact mul_ne_zero
      (div_ne_zero
        (mul_ne_zero hsZero (sub_ne_zero.mpr hsOne))
        (by norm_num))
      hCompletedNe

/-- Every xi zero lies in the open critical strip. -/
theorem riemannXiCandidate_zero_in_critical_strip
    {s : Complex}
    (hZero : TS282.Goldbach.riemannXiCandidate s = 0) :
    0 < s.re /\ s.re < 1 := by
  constructor
  next =>
    by_contra h
    have hReflected : 1 <= (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    apply riemannXiCandidate_ne_zero_of_one_le_re hReflected
    rw [TS282.Goldbach.riemannXiCandidate_one_sub]
    exact hZero
  next =>
    by_contra h
    exact
      (riemannXiCandidate_ne_zero_of_one_le_re (le_of_not_gt h)) hZero

/-- Every xi zero is exactly a concrete nontrivial zeta zero. -/
theorem riemannXiCandidate_zero_is_concrete
    {s : Complex}
    (hZero : TS282.Goldbach.riemannXiCandidate s = 0) :
    TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet s := by
  have hStrip := riemannXiCandidate_zero_in_critical_strip hZero
  have hMultiplierNe :
      Not (TS290.Goldbach.xiZetaLocalMultiplier s = 0) :=
    TS290.Goldbach.xiZetaLocalMultiplier_ne_zero hStrip.1 hStrip.2
  have hZetaZero : riemannZeta s = 0 := by
    have hProduct :
        TS290.Goldbach.xiZetaLocalMultiplier s * riemannZeta s = 0 := by
      rw [<- TS290.Goldbach.riemannXiCandidate_eq_localMultiplier_mul_riemannZeta
        hStrip.1 hStrip.2]
      exact hZero
    exact (mul_eq_zero.mp hProduct).resolve_left hMultiplierNe
  exact And.intro
    (by
      simpa [TS185.Goldbach.riemannZetaZeroPredicate,
        TS185.Goldbach.mathlibRiemannZetaFunction] using hZetaZero)
    (by
      unfold TS185.Goldbach.criticalStripPredicate
      exact hStrip)

/-- Exact finite polynomial associated with the height finset of TS295. -/
noncomputable def heightZeroPolynomial
    (T : Nat)
    (z : Complex) :
    Complex :=
  Finset.prod (TS295.Goldbach.nearbyConcreteZeros T)
    (fun rho =>
      (z - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho)

/-- Exact height quotient; only its horizontal local behavior is used. -/
noncomputable def heightXiQuotient
    (T : Nat)
    (z : Complex) :
    Complex :=
  TS282.Goldbach.riemannXiCandidate z / heightZeroPolynomial T z

theorem heightZeroPolynomial_analyticAt
    (T : Nat)
    (z : Complex) :
    AnalyticAt Complex (heightZeroPolynomial T) z := by
  classical
  unfold heightZeroPolynomial
  apply Finset.analyticAt_prod
  intro rho _
  exact (analyticAt_id.sub analyticAt_const).pow _

theorem heightZeroPolynomial_differentiableAt
    (T : Nat)
    (z : Complex) :
    DifferentiableAt Complex (heightZeroPolynomial T) z :=
  (heightZeroPolynomial_analyticAt T z).differentiableAt

/-- Top horizontal center. -/
noncomputable def strongHeightTopCenter
    (T : Nat)
    (sigma : Real) :
    Complex :=
  (sigma : Complex) + (strongHeightTau T : Complex) * I

/-- Bottom horizontal center. -/
noncomputable def strongHeightBottomCenter
    (T : Nat)
    (sigma : Real) :
    Complex :=
  (sigma : Complex) - (strongHeightTau T : Complex) * I

theorem nearby_root_distance_top
    (T : Nat)
    (sigma : Real)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    strongHeightDelta T <=
      norm (strongHeightTopCenter T sigma - rho.1) := by
  exact
    (strongHeightDelta_le_gap T rho hRho).trans
      (TS295.Goldbach.symmetricZeroHeightGap_le_norm_top
        sigma (strongHeightTau T)
        ((Nat.cast_nonneg T).trans_lt (strongHeightTau_gt T) |>.le)
        rho)

theorem nearby_root_distance_bottom
    (T : Nat)
    (sigma : Real)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    strongHeightDelta T <=
      norm (strongHeightBottomCenter T sigma - rho.1) := by
  exact
    (strongHeightDelta_le_gap T rho hRho).trans
      (TS295.Goldbach.symmetricZeroHeightGap_le_norm_bottom
        sigma (strongHeightTau T)
        ((Nat.cast_nonneg T).trans_lt (strongHeightTau_gt T) |>.le)
        rho)

theorem nearby_root_not_mem_top_ball
    (T : Nat)
    (sigma : Real)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    Not
      (Membership.mem
        (Metric.closedBall (strongHeightTopCenter T sigma)
          (strongHeightDelta T / 2)) rho.1) := by
  intro hBall
  have hDist :
      norm (strongHeightTopCenter T sigma - rho.1) <=
        strongHeightDelta T / 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hBall
    simpa only [norm_sub_rev] using hBall
  linarith [nearby_root_distance_top T sigma rho hRho,
    strongHeightDelta_pos T]

theorem nearby_root_not_mem_bottom_ball
    (T : Nat)
    (sigma : Real)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    Not
      (Membership.mem
        (Metric.closedBall (strongHeightBottomCenter T sigma)
          (strongHeightDelta T / 2)) rho.1) := by
  intro hBall
  have hDist :
      norm (strongHeightBottomCenter T sigma - rho.1) <=
        strongHeightDelta T / 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hBall
    simpa only [norm_sub_rev] using hBall
  linarith [nearby_root_distance_bottom T sigma rho hRho,
    strongHeightDelta_pos T]

theorem heightZeroPolynomial_ne_zero_on_top_ball
    (T : Nat)
    (sigma : Real)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.closedBall (strongHeightTopCenter T sigma)
          (strongHeightDelta T / 2)) z) :
    Not (heightZeroPolynomial T z = 0) := by
  classical
  unfold heightZeroPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro rho hRho
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro hEq
  apply nearby_root_not_mem_top_ball T sigma rho hRho
  simpa [hEq] using hz

theorem heightZeroPolynomial_ne_zero_on_bottom_ball
    (T : Nat)
    (sigma : Real)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.closedBall (strongHeightBottomCenter T sigma)
          (strongHeightDelta T / 2)) z) :
    Not (heightZeroPolynomial T z = 0) := by
  classical
  unfold heightZeroPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro rho hRho
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro hEq
  apply nearby_root_not_mem_bottom_ball T sigma rho hRho
  simpa [hEq] using hz

theorem abs_im_le_center_height_add_dist
    (z center : Complex) :
    _root_.abs z.im <= _root_.abs center.im + norm (z - center) := by
  have hTriangle :
      _root_.abs z.im <=
        _root_.abs center.im + _root_.abs (z.im - center.im) := by
    have := abs_add (z.im - center.im) center.im
    simpa [sub_add_cancel, add_comm] using this
  exact hTriangle.trans
    (add_le_add_left (by
      simpa using (abs_im_le_abs (z - center))) _)

theorem xi_zero_in_top_ball_is_nearby
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.closedBall (strongHeightTopCenter T sigma)
          (strongHeightDelta T / 2)) z)
    (hZero : TS282.Goldbach.riemannXiCandidate z = 0) :
    Exists fun rho : TS292.Goldbach.ConcreteNontrivialZero =>
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho /\
        rho.1 = z := by
  let rho : TS292.Goldbach.ConcreteNontrivialZero :=
    Subtype.mk z (riemannXiCandidate_zero_is_concrete hZero)
  refine Exists.intro rho (And.intro ?_ rfl)
  apply
    (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
      (T + 2) rho).mpr
  have hzDist :
      norm (z - strongHeightTopCenter T sigma) <=
        strongHeightDelta T / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_neg] using hz
  have hCenterIm :
      _root_.abs (strongHeightTopCenter T sigma).im =
        strongHeightTau T := by
    simp [strongHeightTopCenter, abs_of_pos (strongHeightTau_pos hT)]
  have hAbsIm :=
    abs_im_le_center_height_add_dist z (strongHeightTopCenter T sigma)
  rw [hCenterIm] at hAbsIm
  have hDeltaHalf : strongHeightDelta T / 2 <= 1 / 2 := by
    linarith [strongHeightDelta_le_one T]
  have : _root_.abs z.im < (T : Real) + 2 := by
    linarith [strongHeightTau_lt T]
  exact this.le.trans_eq (by push_cast; ring)

theorem xi_zero_in_bottom_ball_is_nearby
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.closedBall (strongHeightBottomCenter T sigma)
          (strongHeightDelta T / 2)) z)
    (hZero : TS282.Goldbach.riemannXiCandidate z = 0) :
    Exists fun rho : TS292.Goldbach.ConcreteNontrivialZero =>
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho /\
        rho.1 = z := by
  let rho : TS292.Goldbach.ConcreteNontrivialZero :=
    Subtype.mk z (riemannXiCandidate_zero_is_concrete hZero)
  refine Exists.intro rho (And.intro ?_ rfl)
  apply
    (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
      (T + 2) rho).mpr
  have hzDist :
      norm (z - strongHeightBottomCenter T sigma) <=
        strongHeightDelta T / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_neg] using hz
  have hCenterIm :
      _root_.abs (strongHeightBottomCenter T sigma).im =
        strongHeightTau T := by
    simp [strongHeightBottomCenter, abs_of_pos (strongHeightTau_pos hT)]
  have hAbsIm :=
    abs_im_le_center_height_add_dist z (strongHeightBottomCenter T sigma)
  rw [hCenterIm] at hAbsIm
  have hDeltaHalf : strongHeightDelta T / 2 <= 1 / 2 := by
    linarith [strongHeightDelta_le_one T]
  have : _root_.abs z.im < (T : Real) + 2 := by
    linarith [strongHeightTau_lt T]
  exact this.le.trans_eq (by push_cast; ring)

theorem riemannXiCandidate_ne_zero_on_top_ball
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.closedBall (strongHeightTopCenter T sigma)
          (strongHeightDelta T / 2)) z) :
    Not (TS282.Goldbach.riemannXiCandidate z = 0) := by
  intro hZero
  exact
    (xi_zero_in_top_ball_is_nearby T hT sigma z hz hZero).elim
      (fun rho hData =>
        nearby_root_not_mem_top_ball T sigma rho hData.1
          (by simpa [hData.2] using hz))

theorem riemannXiCandidate_ne_zero_on_bottom_ball
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.closedBall (strongHeightBottomCenter T sigma)
          (strongHeightDelta T / 2)) z) :
    Not (TS282.Goldbach.riemannXiCandidate z = 0) := by
  intro hZero
  exact
    (xi_zero_in_bottom_ball_is_nearby T hT sigma z hz hZero).elim
      (fun rho hData =>
        nearby_root_not_mem_bottom_ball T sigma rho hData.1
          (by simpa [hData.2] using hz))

theorem heightXiQuotient_analyticAt_of_polynomial_ne
    (T : Nat)
    (z : Complex)
    (hPolynomial : Not (heightZeroPolynomial T z = 0)) :
    AnalyticAt Complex (heightXiQuotient T) z :=
  (TS282.Goldbach.riemannXiCandidate_analyticAt z).div
    (heightZeroPolynomial_analyticAt T z) hPolynomial

theorem heightXiQuotient_nonzero_of_ne
    (T : Nat)
    (z : Complex)
    (hXi : Not (TS282.Goldbach.riemannXiCandidate z = 0))
    (hPolynomial : Not (heightZeroPolynomial T z = 0)) :
    Not (heightXiQuotient T z = 0) := by
  unfold heightXiQuotient
  exact div_ne_zero hXi hPolynomial

theorem heightXiQuotient_analyticOnNhd_top_ball
    (T : Nat)
    (sigma : Real) :
    AnalyticOnNhd Complex (heightXiQuotient T)
      (Metric.closedBall (strongHeightTopCenter T sigma)
        (strongHeightDelta T / 2)) := by
  intro z hz
  exact heightXiQuotient_analyticAt_of_polynomial_ne T z
    (heightZeroPolynomial_ne_zero_on_top_ball T sigma z hz)

theorem heightXiQuotient_analyticOnNhd_bottom_ball
    (T : Nat)
    (sigma : Real) :
    AnalyticOnNhd Complex (heightXiQuotient T)
      (Metric.closedBall (strongHeightBottomCenter T sigma)
        (strongHeightDelta T / 2)) := by
  intro z hz
  exact heightXiQuotient_analyticAt_of_polynomial_ne T z
    (heightZeroPolynomial_ne_zero_on_bottom_ball T sigma z hz)

theorem heightXiQuotient_nonzero_on_top_ball
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.closedBall (strongHeightTopCenter T sigma)
          (strongHeightDelta T / 2)) z) :
    Not (heightXiQuotient T z = 0) :=
  heightXiQuotient_nonzero_of_ne T z
    (riemannXiCandidate_ne_zero_on_top_ball T hT sigma z hz)
    (heightZeroPolynomial_ne_zero_on_top_ball T sigma z hz)

theorem heightXiQuotient_nonzero_on_bottom_ball
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.closedBall (strongHeightBottomCenter T sigma)
          (strongHeightDelta T / 2)) z) :
    Not (heightXiQuotient T z = 0) :=
  heightXiQuotient_nonzero_of_ne T z
    (riemannXiCandidate_ne_zero_on_bottom_ball T hT sigma z hz)
    (heightZeroPolynomial_ne_zero_on_bottom_ball T sigma z hz)

theorem heightZeroPolynomial_logDeriv
    (T : Nat)
    (s : Complex)
    (hAvoid :
      forall rho : TS292.Goldbach.ConcreteNontrivialZero,
        Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho ->
          Not (s = rho.1)) :
    logDeriv (heightZeroPolynomial T) s =
      TS295.Goldbach.finiteZeroLogDerivativeSum T s := by
  classical
  unfold heightZeroPolynomial TS295.Goldbach.finiteZeroLogDerivativeSum
    TS295.Goldbach.finiteZeroLogDerivativeTerm
  rw [logDeriv_prod]
  next =>
    apply Finset.sum_congr rfl
    intro rho hRho
    calc
      logDeriv
          (fun z : Complex =>
            (z - rho.1) ^
              TS295.Goldbach.concreteZeroMultiplicity rho) s =
          (TS295.Goldbach.concreteZeroMultiplicity rho : Complex) *
            logDeriv (fun z : Complex => z - rho.1) s := by
              simpa using
                (logDeriv_fun_pow
                  (differentiableAt_id.sub_const rho.1)
                  (TS295.Goldbach.concreteZeroMultiplicity rho))
      _ =
          (TS295.Goldbach.concreteZeroMultiplicity rho : Complex) /
            (s - rho.1) := by
              simp [logDeriv_apply, hAvoid rho hRho, div_eq_mul_inv]
  next =>
    intro rho hRho
    exact pow_ne_zero _ (sub_ne_zero.mpr (hAvoid rho hRho))
  next =>
    intro rho _
    exact (differentiableAt_id.sub_const rho.1).pow _

theorem heightXiQuotient_logDerivative_identity
    (T : Nat)
    (s : Complex)
    (hXi : Not (TS282.Goldbach.riemannXiCandidate s = 0))
    (hPolynomial : Not (heightZeroPolynomial T s = 0))
    (hAvoid :
      forall rho : TS292.Goldbach.ConcreteNontrivialZero,
        Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho ->
          Not (s = rho.1)) :
    deriv TS282.Goldbach.riemannXiCandidate s /
          TS282.Goldbach.riemannXiCandidate s =
      TS295.Goldbach.finiteZeroLogDerivativeSum T s +
        deriv (heightXiQuotient T) s / heightXiQuotient T s := by
  have hXiDiff :
      DifferentiableAt Complex TS282.Goldbach.riemannXiCandidate s :=
    TS282.Goldbach.riemannXiCandidate_entire.differentiableAt
  have hPolynomialDiff := heightZeroPolynomial_differentiableAt T s
  have hDiv :=
    logDeriv_div s hXi hPolynomial hXiDiff hPolynomialDiff
  change
    logDeriv TS282.Goldbach.riemannXiCandidate s =
      TS295.Goldbach.finiteZeroLogDerivativeSum T s +
        logDeriv (heightXiQuotient T) s
  rw [<- heightZeroPolynomial_logDeriv T s hAvoid]
  change
    logDeriv TS282.Goldbach.riemannXiCandidate s =
      logDeriv (heightZeroPolynomial T) s +
        logDeriv
          (fun z =>
            TS282.Goldbach.riemannXiCandidate z /
              heightZeroPolynomial T z) s
  rw [hDiv]
  ring

theorem heightXiQuotient_logDerivative_identity_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    deriv TS282.Goldbach.riemannXiCandidate
          (strongHeightTopCenter T sigma) /
        TS282.Goldbach.riemannXiCandidate
          (strongHeightTopCenter T sigma) =
      TS295.Goldbach.finiteZeroLogDerivativeSum T
          (strongHeightTopCenter T sigma) +
        deriv (heightXiQuotient T) (strongHeightTopCenter T sigma) /
          heightXiQuotient T (strongHeightTopCenter T sigma) := by
  have hCenterMem :
      Membership.mem
        (Metric.closedBall (strongHeightTopCenter T sigma)
          (strongHeightDelta T / 2))
        (strongHeightTopCenter T sigma) := by
    rw [Metric.mem_closedBall]
    exact (dist_self _).trans_le
      (div_nonneg (strongHeightDelta_pos T).le (by norm_num))
  apply heightXiQuotient_logDerivative_identity
  next =>
    exact riemannXiCandidate_ne_zero_on_top_ball T hT sigma _
      hCenterMem
  next =>
    exact heightZeroPolynomial_ne_zero_on_top_ball T sigma _
      hCenterMem
  next =>
    intro rho hRho hEq
    have hDist := nearby_root_distance_top T sigma rho hRho
    rw [hEq, sub_self, norm_zero] at hDist
    linarith [strongHeightDelta_pos T]

theorem heightXiQuotient_logDerivative_identity_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    deriv TS282.Goldbach.riemannXiCandidate
          (strongHeightBottomCenter T sigma) /
        TS282.Goldbach.riemannXiCandidate
          (strongHeightBottomCenter T sigma) =
      TS295.Goldbach.finiteZeroLogDerivativeSum T
          (strongHeightBottomCenter T sigma) +
        deriv (heightXiQuotient T) (strongHeightBottomCenter T sigma) /
          heightXiQuotient T (strongHeightBottomCenter T sigma) := by
  have hCenterMem :
      Membership.mem
        (Metric.closedBall (strongHeightBottomCenter T sigma)
          (strongHeightDelta T / 2))
        (strongHeightBottomCenter T sigma) := by
    rw [Metric.mem_closedBall]
    exact (dist_self _).trans_le
      (div_nonneg (strongHeightDelta_pos T).le (by norm_num))
  apply heightXiQuotient_logDerivative_identity
  next =>
    exact riemannXiCandidate_ne_zero_on_bottom_ball T hT sigma _
      hCenterMem
  next =>
    exact heightZeroPolynomial_ne_zero_on_bottom_ball T sigma _
      hCenterMem
  next =>
    intro rho hRho hEq
    have hDist := nearby_root_distance_bottom T sigma rho hRho
    rw [hEq, sub_self, norm_zero] at hDist
    linarith [strongHeightDelta_pos T]

/--
Three local radii used only to construct a logarithm of the exact height
quotient.  The outer radius is `delta / 4`, hence its closed ball stays
strictly inside the zero-free ball of radius `delta / 2`.
-/
noncomputable def localQuotientDiskConfiguration
    (T : Nat)
    (center : Complex) :
    TS275.Goldbach.JensenDiskConfiguration where
  center := center
  innerRadius := strongHeightDelta T / 16
  averagingRadius := strongHeightDelta T / 8
  analyticRadius := strongHeightDelta T / 4
  innerRadius_positive := by
    linarith [strongHeightDelta_pos T]
  innerRadius_lt_averagingRadius := by
    linarith [strongHeightDelta_pos T]
  averagingRadius_lt_analyticRadius := by
    linarith [strongHeightDelta_pos T]

/-- Empty zero data used to invoke TS279 on an already nonvanishing quotient. -/
noncomputable def emptyLocalQuotientZeroData
    (T : Nat)
    (center : Complex) :
    TS275.Goldbach.JensenFactorZeroData where
  config := localQuotientDiskConfiguration T center
  innerZeros := Finset.empty
  innerMultiplicity := fun _ => 0
  inner_zero_ne_center := by
    intro rho hRho
    change Membership.mem (Finset.empty : Finset Complex) rho at hRho
    exact (Finset.not_mem_empty rho hRho).elim
  inner_zero_mem_disk := by
    intro rho hRho
    change Membership.mem (Finset.empty : Finset Complex) rho at hRho
    exact (Finset.not_mem_empty rho hRho).elim
  factorZeros := Finset.empty
  factorMultiplicity := fun _ => 0
  factor_zero_ne_center := by
    intro rho hRho
    change Membership.mem (Finset.empty : Finset Complex) rho at hRho
    exact (Finset.not_mem_empty rho hRho).elim
  factor_zero_mem_open_disk := by
    intro rho hRho
    change Membership.mem (Finset.empty : Finset Complex) rho at hRho
    exact (Finset.not_mem_empty rho hRho).elim
  innerZeros_subset_factorZeros := by
    simp
  multiplicity_agrees := by
    intro rho hRho
    change Membership.mem (Finset.empty : Finset Complex) rho at hRho
    exact (Finset.not_mem_empty rho hRho).elim
  factorMultiplicity_positive := by
    intro rho hRho
    change Membership.mem (Finset.empty : Finset Complex) rho at hRho
    exact (Finset.not_mem_empty rho hRho).elim

theorem local_analytic_closedBall_subset_zero_free_ball
    (T : Nat)
    (center : Complex) :
    Metric.closedBall center (strongHeightDelta T / 4) <=
      Metric.closedBall center (strongHeightDelta T / 2) :=
  Metric.closedBall_subset_closedBall (by
    linarith [strongHeightDelta_pos T])

/--
Generic empty-factor buffered data for the exact height quotient.  The two
proof arguments must concern the actual quotient, so no anonymous remainder
can inhabit this construction.
-/
noncomputable def heightXiQuotientBufferedData
    (T : Nat)
    (center : Complex)
    (hAnalytic :
      AnalyticOnNhd Complex (heightXiQuotient T)
        (Metric.closedBall center (strongHeightDelta T / 2)))
    (hNonzero :
      forall z : Complex,
        Membership.mem
            (Metric.closedBall center (strongHeightDelta T / 2)) z ->
          Not (heightXiQuotient T z = 0)) :
    TS275.Goldbach.BufferedJensenFactorizationData where
  zeroData := emptyLocalQuotientZeroData T center
  f := heightXiQuotient T
  g := heightXiQuotient T
  f_analytic :=
    hAnalytic.mono
      (local_analytic_closedBall_subset_zero_free_ball T center)
  g_analytic :=
    hAnalytic.mono
      (local_analytic_closedBall_subset_zero_free_ball T center)
  factorization := by
    intro z hz
    change heightXiQuotient T z =
      Finset.prod Finset.empty
          (fun rho : Complex =>
            (z - rho) ^ (fun _ : Complex => 0) rho) *
        heightXiQuotient T z
    simp
  g_nonzero := fun z hz =>
    hNonzero z
      (local_analytic_closedBall_subset_zero_free_ball T center hz)

/-- Buffered data for the exact quotient at a top horizontal point. -/
noncomputable def topHeightXiQuotientBufferedData
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    TS275.Goldbach.BufferedJensenFactorizationData :=
  heightXiQuotientBufferedData T (strongHeightTopCenter T sigma)
    (heightXiQuotient_analyticOnNhd_top_ball T sigma)
    (heightXiQuotient_nonzero_on_top_ball T hT sigma)

/-- Buffered data for the exact quotient at a bottom horizontal point. -/
noncomputable def bottomHeightXiQuotientBufferedData
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    TS275.Goldbach.BufferedJensenFactorizationData :=
  heightXiQuotientBufferedData T (strongHeightBottomCenter T sigma)
    (heightXiQuotient_analyticOnNhd_bottom_ball T sigma)
    (heightXiQuotient_nonzero_on_bottom_ball T hT sigma)

/-- TS279 logarithm for any buffered nonvanishing quotient. -/
noncomputable def concreteBufferedLogData
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    TS277.Goldbach.BufferedQuotientHolomorphicLogData D :=
  TS279.Goldbach.bufferedQuotientHolomorphicLogData D

/-- Norm values of the concrete TS279 logarithm on its analytic sphere. -/
def concreteBufferedLogSphereValues
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    Set Real :=
  (fun z : Complex => norm ((concreteBufferedLogData D).logarithm z)) ''
    Metric.sphere D.zeroData.config.center
      D.zeroData.config.analyticRadius

/-- Canonical finite sphere bound for the concrete local logarithm. -/
noncomputable def concreteBufferedLogSphereBound
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    Real :=
  sSup (concreteBufferedLogSphereValues D)

theorem concreteBufferedLog_continuousOn_sphere
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    ContinuousOn
      (concreteBufferedLogData D).logarithm
      (Metric.sphere D.zeroData.config.center
        D.zeroData.config.analyticRadius) := by
  intro z hz
  exact
    ((concreteBufferedLogData D).logarithm_analytic z
      (Metric.sphere_subset_closedBall hz)).continuousAt.continuousWithinAt

theorem concreteBufferedLogSphereValues_compact
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    IsCompact (concreteBufferedLogSphereValues D) := by
  unfold concreteBufferedLogSphereValues
  exact
    (isCompact_sphere _ _).image_of_continuousOn
      (continuous_norm.comp_continuousOn
        (concreteBufferedLog_continuousOn_sphere D))

theorem concreteBufferedLog_norm_le_sphereBound
    (D : TS275.Goldbach.BufferedJensenFactorizationData)
    (z : Complex)
    (hz :
      Membership.mem
        (Metric.sphere D.zeroData.config.center
          D.zeroData.config.analyticRadius) z) :
    norm ((concreteBufferedLogData D).logarithm z) <=
      concreteBufferedLogSphereBound D := by
  apply le_csSup (concreteBufferedLogSphereValues_compact D).bddAbove
  exact Exists.intro z (And.intro hz rfl)

/--
The TS279 logarithm, together with its canonical compact sphere supremum,
fills the exact TS295 local Cauchy interface.
-/
noncomputable def concreteBufferedLocalLogCauchyData
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      D.g D.zeroData.config.center where
  radius := D.zeroData.config.analyticRadius
  radius_pos := D.zeroData.config.analyticRadius_positive
  logarithm := (concreteBufferedLogData D).logarithm
  logarithm_diffContOnCl := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    exact
      ((concreteBufferedLogData D).logarithm_analytic z
        (Metric.closure_ball_subset_closedBall hz)).differentiableAt
          |>.differentiableWithinAt
  exp_logarithm_eq := by
    intro z hz
    exact
      (concreteBufferedLogData D).exp_logarithm_eq_g z
        (Metric.ball_subset_closedBall hz)
  sphereBound := concreteBufferedLogSphereBound D
  logarithm_norm_le := concreteBufferedLog_norm_le_sphereBound D

/-- Concrete local Cauchy data at a top horizontal point. -/
noncomputable def topHeightXiQuotientLocalLogData
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      (heightXiQuotient T) (strongHeightTopCenter T sigma) :=
  concreteBufferedLocalLogCauchyData
    (topHeightXiQuotientBufferedData T hT sigma)

/-- Concrete local Cauchy data at a bottom horizontal point. -/
noncomputable def bottomHeightXiQuotientLocalLogData
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      (heightXiQuotient T) (strongHeightBottomCenter T sigma) :=
  concreteBufferedLocalLogCauchyData
    (bottomHeightXiQuotientBufferedData T hT sigma)

/--
Concrete top-side xi logarithmic-derivative bound.  Both terms on the
right are actual definitions: the exact reciprocal load and the compact
sphere bound of the TS279 logarithm of the exact height quotient.
-/
theorem riemannXiCandidate_logDerivative_norm_le_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm
        (deriv TS282.Goldbach.riemannXiCandidate
              (strongHeightTopCenter T sigma) /
          TS282.Goldbach.riemannXiCandidate
              (strongHeightTopCenter T sigma)) <=
      strongHeightLoadEnvelope T +
        (topHeightXiQuotientLocalLogData T hT sigma).sphereBound /
          (topHeightXiQuotientLocalLogData T hT sigma).radius := by
  simpa [strongHeightLoadEnvelope, strongHeightTopCenter,
    strongCleanPerronContourData] using
    (TS295.Goldbach.horizontalLogDerivative_norm_le_reciprocalLoad_add_cauchy
        (strongCleanPerronContourData T hT) sigma
        (heightXiQuotient T)
        (topHeightXiQuotientLocalLogData T hT sigma)
        (heightXiQuotient_logDerivative_identity_top T hT sigma))

/-- Bottom-side version of the concrete xi logarithmic-derivative bound. -/
theorem riemannXiCandidate_logDerivative_norm_le_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm
        (deriv TS282.Goldbach.riemannXiCandidate
              (strongHeightBottomCenter T sigma) /
          TS282.Goldbach.riemannXiCandidate
              (strongHeightBottomCenter T sigma)) <=
      strongHeightLoadEnvelope T +
        (bottomHeightXiQuotientLocalLogData T hT sigma).sphereBound /
          (bottomHeightXiQuotientLocalLogData T hT sigma).radius := by
  simpa [strongHeightLoadEnvelope, strongHeightBottomCenter,
    strongCleanPerronContourData] using
    (TS295.Goldbach.horizontalLogDerivative_norm_le_reciprocalLoad_add_cauchy_bottom
        (strongCleanPerronContourData T hT) sigma
        (heightXiQuotient T)
        (bottomHeightXiQuotientLocalLogData T hT sigma)
        (heightXiQuotient_logDerivative_identity_bottom T hT sigma))

structure ConcreteStrongHeightXiQuotientLogLedger where
  exact_strong_height_constructed :
    TS295.Goldbach.StrongCleanPerronContourExistenceStatement
      strongHeightDelta strongHeightLoadEnvelope

  exact_height_quotient_constructed : True
  quotient_analytic_and_nonzero_on_local_balls : True
  exact_finite_log_derivative_identity : True
  quotient_holomorphic_log_constructed : True
  canonical_log_sphere_bound_constructed : True
  top_horizontal_xi_bound_proved : True
  bottom_horizontal_xi_bound_proved : True

  closed_reciprocal_load_rate_not_proved : True
  effective_log_sphere_rate_not_proved : True
  horizontal_bound_div_T_sq_tendsto_zero_not_proved : True
  xi_to_zeta_completion_not_proved : True
  left_boundary_not_estimated : True
  right_cutoff_not_estimated : True
  exceptional_inventory_not_completed : True
  perron_inversion_not_proved : True
  meromorphic_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

noncomputable def concreteStrongHeightXiQuotientLogLedger :
    ConcreteStrongHeightXiQuotientLogLedger where
  exact_strong_height_constructed := strongCleanPerronContourExistence
  exact_height_quotient_constructed := True.intro
  quotient_analytic_and_nonzero_on_local_balls := True.intro
  exact_finite_log_derivative_identity := True.intro
  quotient_holomorphic_log_constructed := True.intro
  canonical_log_sphere_bound_constructed := True.intro
  top_horizontal_xi_bound_proved := True.intro
  bottom_horizontal_xi_bound_proved := True.intro
  closed_reciprocal_load_rate_not_proved := True.intro
  effective_log_sphere_rate_not_proved := True.intro
  horizontal_bound_div_T_sq_tendsto_zero_not_proved := True.intro
  xi_to_zeta_completion_not_proved := True.intro
  left_boundary_not_estimated := True.intro
  right_cutoff_not_estimated := True.intro
  exceptional_inventory_not_completed := True.intro
  perron_inversion_not_proved := True.intro
  meromorphic_residue_theorem_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

def ConcreteStrongHeightXiQuotientLogTarget : Prop :=
  Nonempty ConcreteStrongHeightXiQuotientLogLedger

theorem concreteStrongHeightXiQuotientLogTarget :
    ConcreteStrongHeightXiQuotientLogTarget :=
  Nonempty.intro concreteStrongHeightXiQuotientLogLedger

end Goldbach
end TS296
