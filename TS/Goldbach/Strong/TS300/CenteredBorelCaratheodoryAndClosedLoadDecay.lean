import Mathlib.Analysis.Complex.Schwarz
import TS.Goldbach.Strong.TS299.FiniteGridStrongHeightReciprocalLoad

/-!
# TS300 - Centered Borel-Caratheodory and Closed Load Decay

This sprint backports the minimal Borel-Caratheodory estimate needed by the
local finite-quotient route.  The proof uses the Schwarz transform
`f / (2 * M - f)` and only APIs available in the locked Mathlib revision.

The quotient logarithm is centered before it is estimated.  This removes the
irrelevant additive branch constant and reduces the quotient logarithmic
derivative to an explicit bound on the real part of the centered logarithm.
That real-part envelope is named but not constructed here: nonvanishing alone
does not provide a quantitative lower bound for the quotient at the center.

Independently, the finite-grid load envelope of TS299 is converted into a
closed horizontal Perron component.  Its `T^-2` normalized form tends to zero
for every fixed arithmetic scale.
-/

namespace TS300
namespace Goldbach

open Complex Filter Metric Set
open scoped Topology

section BorelCaratheodoryBackport

variable {f : Complex -> Complex} {M R : Real} {z w : Complex}

/-- Inverse identity for the Schwarz transform used below. -/
lemma eq_mul_div_one_add_of_eq_div_sub
    (hM : Not (M = 0))
    (hDen : Not (2 * M - z = 0))
    (h : w = z / (2 * M - z)) :
    z = 2 * M * w / (1 + w) := by
  have hMC : Not (((M : Real) : Complex) = 0) := by
    exact_mod_cast hM
  rw [h]
  field_simp [hDen, hMC]

/-- A strict real-part bound strictly separates the Schwarz denominator. -/
lemma norm_lt_norm_two_mul_sub
    (hM : 0 < M)
    (hz : z.re < M) :
    norm z < norm (2 * M - z) := by
  have hSq : norm z ^ 2 < norm (2 * M - z) ^ 2 := by
    rw [<- Complex.normSq_eq_norm_sq, <- Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg z, norm_nonneg (2 * M - z)]

/-- Schwarz applied to `f / (2M - f)` in the locked Mathlib API. -/
lemma schwarz_transform_norm_le
    (hM : 0 < M)
    (hf : DifferentiableOn Complex f (ball 0 R))
    (hfRe : MapsTo f (ball 0 R) {u | u.re < M})
    (hz : Membership.mem (ball 0 R) z)
    (hf0 : f 0 = 0) :
    norm (f z / (2 * M - f z)) <= (1 / R) * norm z := by
  rw [<- dist_zero_right, <- dist_zero_right]
  nth_rw 1 [<- zero_div (2 * M - f 0), <- hf0]
  apply Complex.dist_le_div_mul_dist_of_mapsTo_ball ?_ (fun x hx => ?_) hz
  next =>
    apply hf.div (hf.const_sub _) fun x hx h => ?_
    have hEq : f x = 2 * M := (sub_eq_zero.mp h).symm
    have hRe := hfRe hx
    change (f x).re < M at hRe
    have hReEq := congrArg Complex.re hEq
    norm_num at hReEq
    linarith
  next =>
    have hNormLt := norm_lt_norm_two_mul_sub hM (hfRe hx)
    have hDenPos : 0 < norm (2 * M - f x) :=
      (norm_nonneg (f x)).trans_lt hNormLt
    simpa [hf0] using (div_lt_one hDenPos).mpr hNormLt

/--
Minimal Borel-Caratheodory theorem for a function vanishing at the origin.
This is a local backport of the later Mathlib theorem, proved from the locked
Schwarz lemma rather than imported from a newer revision.
-/
theorem centered_borelCaratheodory_zero
    (hM : 0 < M)
    (hf : DifferentiableOn Complex f (ball 0 R))
    (hfRe : MapsTo f (ball 0 R) {u | u.re < M})
    (hR : 0 < R)
    (hz : Membership.mem (ball 0 R) z)
    (hf0 : f 0 = 0) :
    norm (f z) <= 2 * M * norm z / (R - norm z) := by
  let w : Complex := f z / (2 * M - f z)
  have hzR : norm z < R := mem_ball_zero_iff.mp hz
  have hwR : norm w <= norm z / R := by
    simpa only [dist_zero_right, div_one, mul_comm (1 / R), mul_one_div] using
      schwarz_transform_norm_le hM hf hfRe hz hf0
  have hwOne : norm w < 1 :=
    hwR.trans_lt ((div_lt_one hR).mpr hzR)
  have hDen : Not (2 * M - f z = 0) := by
    intro hZero
    have hEq : f z = 2 * M := (sub_eq_zero.mp hZero).symm
    have hRe := hfRe hz
    change (f z).re < M at hRe
    have hReEq := congrArg Complex.re hEq
    norm_num at hReEq
    linarith
  calc
    norm (f z) = norm (2 * M * w / (1 + w)) := by
      rw [eq_mul_div_one_add_of_eq_div_sub hM.ne' hDen rfl]
    _ <= 2 * M * norm w / (1 - norm w) := by
      simp only [norm_div, norm_mul, norm_ofNat, norm_real,
        Real.norm_eq_abs, abs_of_pos hM]
      have hDenLower : 1 - norm w <= norm (1 + w) := by
        simpa using norm_sub_norm_le (1 : Complex) (-w)
      exact div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (by norm_num) hM.le) (norm_nonneg w))
        (sub_pos.mpr hwOne) hDenLower
    _ = 2 * M * (norm w / (1 - norm w)) := by ring
    _ <= 2 * M * ((norm z / R) / (1 - norm z / R)) := by
      gcongr
      simpa [div_lt_one hR]
    _ = 2 * M * norm z / (R - norm z) := by field_simp

end BorelCaratheodoryBackport

section CenteredLogarithm

variable {g : Complex -> Complex} {center : Complex}

/-- Center a logarithm to remove its irrelevant additive branch constant. -/
def centeredLogarithm
    (logarithm : Complex -> Complex)
    (center z : Complex) : Complex :=
  logarithm z - logarithm center

@[simp] theorem centeredLogarithm_self
    (logarithm : Complex -> Complex)
    (center : Complex) :
    centeredLogarithm logarithm center center = 0 := by
  simp [centeredLogarithm]

/-- Adding any global branch constant leaves the centered logarithm unchanged. -/
theorem centeredLogarithm_add_const
    (logarithm : Complex -> Complex)
    (a center z : Complex) :
    centeredLogarithm (fun w => logarithm w + a) center z =
      centeredLogarithm logarithm center z := by
  simp [centeredLogarithm]

/-- Exact derivative invariance after centering. -/
theorem deriv_centeredLogarithm
    (logarithm : Complex -> Complex)
    (center : Complex) :
    deriv (centeredLogarithm logarithm center) center =
      deriv logarithm center := by
  unfold centeredLogarithm
  exact deriv_sub_const (f := logarithm) (x := center) (logarithm center)

/--
The genuinely missing analytic input for a centered local quotient logarithm:
an upper bound for its real part on the original logarithm ball.
-/
structure CenteredLogRealPartEnvelopeData
    (L : TS295.Goldbach.LocalHolomorphicLogCauchyData g center) where
  bound : Real
  bound_pos : 0 < bound
  realPart_le :
    forall z : Complex, Membership.mem (ball center L.radius) z ->
      (centeredLogarithm L.logarithm center z).re < bound

/-- Translate the centered logarithm to a function on a ball about zero. -/
def translatedCenteredLogarithm
    (L : TS295.Goldbach.LocalHolomorphicLogCauchyData g center)
    (z : Complex) : Complex :=
  centeredLogarithm L.logarithm center (center + z)

@[simp] theorem translatedCenteredLogarithm_zero
    (L : TS295.Goldbach.LocalHolomorphicLogCauchyData g center) :
    translatedCenteredLogarithm L 0 = 0 := by
  simp [translatedCenteredLogarithm]

theorem translatedCenteredLogarithm_differentiableOn
    (L : TS295.Goldbach.LocalHolomorphicLogCauchyData g center) :
    DifferentiableOn Complex (translatedCenteredLogarithm L)
      (ball 0 L.radius) := by
  intro z hz
  have hMem : Membership.mem (ball center L.radius) (center + z) := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hDiff : DifferentiableAt Complex L.logarithm (center + z) :=
    L.logarithm_diffContOnCl.differentiableAt isOpen_ball hMem
  unfold translatedCenteredLogarithm centeredLogarithm
  fun_prop

theorem translatedCenteredLogarithm_mapsTo_realPart
    (L : TS295.Goldbach.LocalHolomorphicLogCauchyData g center)
    (E : CenteredLogRealPartEnvelopeData L) :
    MapsTo (translatedCenteredLogarithm L) (ball 0 L.radius)
      {u | u.re < E.bound} := by
  intro z hz
  apply E.realPart_le
  simpa [mem_ball, dist_eq_norm] using hz

/-- Borel-Caratheodory bound on the half-radius centered-log sphere. -/
theorem centeredLogarithm_norm_le_on_half_sphere
    (L : TS295.Goldbach.LocalHolomorphicLogCauchyData g center)
    (E : CenteredLogRealPartEnvelopeData L)
    (z : Complex)
    (hz : Membership.mem (sphere center (L.radius / 2)) z) :
    norm (centeredLogarithm L.logarithm center z) <= 2 * E.bound := by
  let w : Complex := z - center
  have hwNorm : norm w = L.radius / 2 := by
    simpa [w, mem_sphere_iff_norm] using hz
  have hwMem : Membership.mem (ball 0 L.radius) w := by
    rw [mem_ball_zero_iff, hwNorm]
    linarith [L.radius_pos]
  have hBound := centered_borelCaratheodory_zero E.bound_pos
    (translatedCenteredLogarithm_differentiableOn L)
    (translatedCenteredLogarithm_mapsTo_realPart L E)
    L.radius_pos hwMem (translatedCenteredLogarithm_zero L)
  have hTranslate : center + w = z := by
    simp [w]
  rw [translatedCenteredLogarithm, hTranslate, hwNorm] at hBound
  have hHalfPos : 0 < L.radius / 2 := by linarith [L.radius_pos]
  calc
    norm (centeredLogarithm L.logarithm center z) <=
        2 * E.bound * (L.radius / 2) /
          (L.radius - L.radius / 2) := hBound
    _ = 2 * E.bound := by
      rw [show L.radius - L.radius / 2 = L.radius / 2 by ring]
      rw [mul_div_assoc, div_self (ne_of_gt hHalfPos), mul_one]

/--
Centered Borel-Caratheodory plus Cauchy controls the quotient logarithmic
derivative by `4 * M / R`.  Only the centered real-part envelope is required;
the additive choice of logarithm branch has disappeared.
-/
theorem LocalHolomorphicLogCauchyData.logDerivative_norm_le_centered
    (L : TS295.Goldbach.LocalHolomorphicLogCauchyData g center)
    (E : CenteredLogRealPartEnvelopeData L) :
    norm (deriv g center / g center) <= 4 * E.bound / L.radius := by
  have hHalfPos : 0 < L.radius / 2 := by
    linarith [L.radius_pos]
  have hSub : ball center (L.radius / 2) <= ball center L.radius :=
    ball_subset_ball (by linarith [L.radius_pos])
  have hDiffCentered :
      DiffContOnCl Complex (centeredLogarithm L.logarithm center)
        (ball center (L.radius / 2)) :=
    (L.logarithm_diffContOnCl.sub_const (L.logarithm center)).mono hSub
  have hCauchy :
      norm (deriv (centeredLogarithm L.logarithm center) center) <=
        (2 * E.bound) / (L.radius / 2) :=
    norm_deriv_le_of_forall_mem_sphere_norm_le hHalfPos hDiffCentered
      (centeredLogarithm_norm_le_on_half_sphere L E)
  rw [L.logDerivative_eq]
  calc
    norm (deriv L.logarithm center) =
        norm (deriv (centeredLogarithm L.logarithm center) center) := by
      rw [deriv_centeredLogarithm]
    _ <=
        (2 * E.bound) / (L.radius / 2) := hCauchy
    _ = 4 * E.bound / L.radius := by
      rw [show (2 * E.bound) / (L.radius / 2) =
        (4 * E.bound) / L.radius by
          field_simp [L.radius_pos.ne']
          ring]

end CenteredLogarithm

section ClosedLoadDecay

/-- Constant introduced when the nested logarithm in the TS299 envelope is opened. -/
noncomputable def finiteGridLoadLogConstant : Real :=
  Real.log (4 * (TS290.Goldbach.xiGlobalLogLinearConstant + 1))

theorem finiteGridLoadLogConstant_nonnegative :
    0 <= finiteGridLoadLogConstant := by
  unfold finiteGridLoadLogConstant
  apply Real.log_nonneg
  have hC := TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative
  nlinarith

/-- A log-polynomial envelope whose decay after division by `T^2` is transparent. -/
noncomputable def finiteGridClosedLoadDecayEnvelope (T : Nat) : Real :=
  48 * TS290.Goldbach.xiGlobalLogLinearConstant *
    (Real.log ((T : Real) + 4) *
      (1 + finiteGridLoadLogConstant +
        2 * Real.log ((T : Real) + 4)) / (T : Real))

theorem finiteGridMultiplicityEnvelope_le_quadratic
    (T : Nat) (hT : 1 <= T) :
    TS299.Goldbach.finiteGridMultiplicityEnvelope T <=
      TS290.Goldbach.xiGlobalLogLinearConstant * ((T : Real) + 4) ^ 2 := by
  have hC := TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative
  have hYPos : 0 < (T : Real) + 4 := by positivity
  have hYOne : 1 <= (T : Real) + 4 := by
    have hT0 : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have hLogNonnegative : 0 <= Real.log ((T : Real) + 4) :=
    Real.log_nonneg hYOne
  have hLogLe : Real.log ((T : Real) + 4) <= (T : Real) + 4 :=
    (Real.log_le_sub_one_of_pos hYPos).trans (by linarith)
  have hProduct :
      ((T : Real) + 2) * Real.log ((T : Real) + 4) <=
        ((T : Real) + 4) * ((T : Real) + 4) :=
    mul_le_mul (by linarith) hLogLe hLogNonnegative (by positivity)
  unfold TS299.Goldbach.finiteGridMultiplicityEnvelope
  rw [pow_two]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hProduct hC

/-- The nested TS299 logarithm is at most one constant plus twice `log(T+4)`. -/
theorem finiteGrid_nestedLog_le
    (T : Nat) (hT : 1 <= T) :
    Real.log
        (4 * (TS299.Goldbach.finiteGridMultiplicityEnvelope T + 1)) <=
      finiteGridLoadLogConstant + 2 * Real.log ((T : Real) + 4) := by
  let C : Real := TS290.Goldbach.xiGlobalLogLinearConstant
  let A : Real := TS299.Goldbach.finiteGridMultiplicityEnvelope T
  let Y : Real := (T : Real) + 4
  have hC : 0 <= C := TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative
  have hA : 0 <= A :=
    TS299.Goldbach.finiteGridMultiplicityEnvelope_nonnegative T hT
  have hY : 1 <= Y := by
    dsimp [Y]
    have hT0 : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have hAY : A <= C * Y ^ 2 := by
    simpa [A, C, Y] using finiteGridMultiplicityEnvelope_le_quadratic T hT
  have hArgPos : 0 < 4 * (A + 1) := by positivity
  have hTargetPos : 0 < 4 * (C + 1) * Y ^ 2 := by positivity
  have hArgLe : 4 * (A + 1) <= 4 * (C + 1) * Y ^ 2 := by
    have hOne : 1 <= Y ^ 2 := by
      nlinarith [sq_nonneg (Y - 1)]
    nlinarith
  have hLog := Real.log_le_log hArgPos hArgLe
  calc
    Real.log (4 * (A + 1)) <= Real.log (4 * (C + 1) * Y ^ 2) := hLog
    _ = Real.log (4 * (C + 1)) + Real.log (Y ^ 2) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    _ = Real.log (4 * (C + 1)) + 2 * Real.log Y := by
      rw [Real.log_pow]
      norm_num
    _ = finiteGridLoadLogConstant + 2 * Real.log ((T : Real) + 4) := by
      rfl

/-- The normalized closed TS299 load is bounded by the transparent decay envelope. -/
theorem finiteGridClosedLoad_div_sq_le_decayEnvelope
    (T : Nat) (hT : 1 <= T) :
    TS299.Goldbach.finiteGridClosedLoadEnvelope T / (T : Real) ^ 2 <=
      finiteGridClosedLoadDecayEnvelope T := by
  let C : Real := TS290.Goldbach.xiGlobalLogLinearConstant
  let L : Real := Real.log ((T : Real) + 4)
  let K : Real := finiteGridLoadLogConstant
  have hTR : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hC : 0 <= C := TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative
  have hL : 0 <= L := by
    dsimp [L]
    apply Real.log_nonneg
    have hT0 : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have hK : 0 <= K := finiteGridLoadLogConstant_nonnegative
  have hNested := finiteGrid_nestedLog_le T hT
  have hFactor :
      0 <= 1 + K + 2 * L := by nlinarith
  have hClosed :
      TS299.Goldbach.finiteGridClosedLoadEnvelope T <=
        16 * C * ((T : Real) + 2) * L * (1 + K + 2 * L) := by
    unfold TS299.Goldbach.finiteGridClosedLoadEnvelope
    unfold TS299.Goldbach.finiteGridMultiplicityEnvelope
    unfold TS299.Goldbach.finiteGridMultiplicityEnvelope at hNested
    have hT2 : 0 <= (T : Real) + 2 := by positivity
    have hPrefix :
        0 <= 16 * TS290.Goldbach.xiGlobalLogLinearConstant *
          ((T : Real) + 2) * Real.log ((T : Real) + 4) :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative)
          hT2)
        hL
    simpa [mul_assoc, add_assoc] using
      mul_le_mul_of_nonneg_left (add_le_add_left hNested 1) hPrefix
  have hRatio : ((T : Real) + 2) / (T : Real) ^ 2 <= 3 / (T : Real) := by
    have hTone : 1 <= (T : Real) := by exact_mod_cast hT
    have hNumerator : ((T : Real) + 2) / (T : Real) <= 3 := by
      calc
        ((T : Real) + 2) / (T : Real) <=
            (3 * (T : Real)) / (T : Real) :=
          div_le_div_of_nonneg_right (by nlinarith) hTR.le
        _ = 3 := by field_simp [hTR.ne']
    rw [show (T : Real) ^ 2 = (T : Real) * (T : Real) by ring]
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hNumerator hTR.le
  calc
    TS299.Goldbach.finiteGridClosedLoadEnvelope T / (T : Real) ^ 2 <=
        (16 * C * ((T : Real) + 2) * L * (1 + K + 2 * L)) /
          (T : Real) ^ 2 :=
      div_le_div_of_nonneg_right hClosed (sq_nonneg (T : Real))
    _ = 16 * C * L * (1 + K + 2 * L) *
          (((T : Real) + 2) / (T : Real) ^ 2) := by ring
    _ <= 16 * C * L * (1 + K + 2 * L) * (3 / (T : Real)) := by
      gcongr
    _ = finiteGridClosedLoadDecayEnvelope T := by
      unfold finiteGridClosedLoadDecayEnvelope
      dsimp [C, L, K]
      ring

theorem finiteGridClosedLoadDecayEnvelope_nonnegative
    (T : Nat) (_hT : 1 <= T) :
    0 <= finiteGridClosedLoadDecayEnvelope T := by
  unfold finiteGridClosedLoadDecayEnvelope
  have hLog : 0 <= Real.log ((T : Real) + 4) := by
    apply Real.log_nonneg
    have hT0 : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have hFactor :
      0 <= 1 + finiteGridLoadLogConstant +
        2 * Real.log ((T : Real) + 4) := by
    nlinarith [finiteGridLoadLogConstant_nonnegative]
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative)
    (div_nonneg
      (mul_nonneg
        hLog hFactor)
      (Nat.cast_nonneg T))

theorem finiteGridClosedLoadEnvelope_nonnegative
    (T : Nat) (hT : 1 <= T) :
    0 <= TS299.Goldbach.finiteGridClosedLoadEnvelope T := by
  unfold TS299.Goldbach.finiteGridClosedLoadEnvelope
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (TS299.Goldbach.finiteGridMultiplicityEnvelope_nonnegative T hT))
    (add_nonneg zero_le_one
      (Real.log_nonneg (by
        have hA :=
          TS299.Goldbach.finiteGridMultiplicityEnvelope_nonnegative T hT
        nlinarith)))

theorem tendsto_log_shift_div_nat :
    Tendsto
      (fun T : Nat => Real.log ((T : Real) + 4) / (T : Real))
      atTop (nhds 0) := by
  have hShift :
      Tendsto (fun T : Nat => (T : Real) + 4) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hBase :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-4) 1 one_ne_zero).comp hShift
  apply hBase.congr'
  filter_upwards with T
  norm_num [Function.comp_def, pow_one]

theorem tendsto_log_sq_shift_div_nat :
    Tendsto
      (fun T : Nat => Real.log ((T : Real) + 4) ^ 2 / (T : Real))
      atTop (nhds 0) := by
  have hShift :
      Tendsto (fun T : Nat => (T : Real) + 4) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hBase :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-4) 2 one_ne_zero).comp hShift
  apply hBase.congr'
  filter_upwards with T
  norm_num [Function.comp_def]

theorem finiteGridClosedLoadDecayEnvelope_tendsto_zero :
    Tendsto finiteGridClosedLoadDecayEnvelope atTop (nhds 0) := by
  have hLinear :=
    (tendsto_log_shift_div_nat.const_mul
      (1 + finiteGridLoadLogConstant))
  have hSquare := tendsto_log_sq_shift_div_nat.const_mul 2
  have hInside := hLinear.add hSquare
  have hTotal := hInside.const_mul
    (48 * TS290.Goldbach.xiGlobalLogLinearConstant)
  convert hTotal using 1
  case h.e'_3 =>
    funext T
    unfold finiteGridClosedLoadDecayEnvelope
    ring
  case h.e'_5 => ring

/-- The TS299 closed reciprocal-load envelope is `o(T^2)`. -/
theorem finiteGridClosedLoad_div_sq_tendsto_zero :
    Tendsto
      (fun T : Nat =>
        TS299.Goldbach.finiteGridClosedLoadEnvelope T / (T : Real) ^ 2)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ finiteGridClosedLoadDecayEnvelope_tendsto_zero
  next =>
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_nonneg
      (finiteGridClosedLoadEnvelope_nonnegative T hT)
      (sq_nonneg (T : Real))
  next =>
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact finiteGridClosedLoad_div_sq_le_decayEnvelope T hT

/-- Fixed arithmetic scaling of the normalized load component. -/
noncomputable def finiteGridHorizontalZeroLoadComponent
    (x T : Nat) : Real :=
  (7 / 2 : Real) * TS298.Goldbach.rightLineScale x *
    (TS299.Goldbach.finiteGridClosedLoadEnvelope T / (T : Real) ^ 2)

noncomputable def finiteGridTopHorizontalPoint
    (T : Nat) (sigma : Real) : Complex :=
  (sigma : Complex) + (TS299.Goldbach.finiteGridStrongTau T : Complex) * I

noncomputable def finiteGridBottomHorizontalPoint
    (T : Nat) (sigma : Real) : Complex :=
  (sigma : Complex) - (TS299.Goldbach.finiteGridStrongTau T : Complex) * I

theorem finiteGridTopHorizontalPoint_ne_zero
    (T : Nat) (hT : 1 <= T) (sigma : Real) :
    Not (finiteGridTopHorizontalPoint T sigma = 0) := by
  intro hZero
  have hIm := congrArg Complex.im hZero
  simp [finiteGridTopHorizontalPoint] at hIm
  linarith [TS299.Goldbach.finiteGridStrongTau_pos hT]

theorem finiteGridBottomHorizontalPoint_ne_zero
    (T : Nat) (hT : 1 <= T) (sigma : Real) :
    Not (finiteGridBottomHorizontalPoint T sigma = 0) := by
  intro hZero
  have hIm := congrArg Complex.im hZero
  simp [finiteGridBottomHorizontalPoint] at hIm
  linarith [TS299.Goldbach.finiteGridStrongTau_pos hT]

theorem nat_cpow_finiteGridTop_norm_le_rightLineScale
    (x T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    norm ((x : Complex) ^ (finiteGridTopHorizontalPoint T sigma)) <=
      TS298.Goldbach.rightLineScale x := by
  by_cases hx : x = 0
  case pos =>
    subst x
    simpa [Complex.zero_cpow (finiteGridTopHorizontalPoint_ne_zero T hT sigma)] using
      TS298.Goldbach.rightLineScale_nonnegative 0
  case neg =>
    have hxPos : 0 < x := Nat.pos_of_ne_zero hx
    rw [Complex.norm_natCast_cpow_of_pos hxPos]
    have hBase : (1 : Real) <= (x : Real) := by exact_mod_cast hxPos
    have hRe : (finiteGridTopHorizontalPoint T sigma).re <= 2 := by
      simpa [finiteGridTopHorizontalPoint, TS294.Goldbach.fixedPerronRight] using hSigma
    have hPow := Real.rpow_le_rpow_of_exponent_le hBase hRe
    rw [Real.rpow_two] at hPow
    exact hPow.trans (TS298.Goldbach.nat_sq_le_rightLineScale x)

theorem nat_cpow_finiteGridBottom_norm_le_rightLineScale
    (x T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    norm ((x : Complex) ^ (finiteGridBottomHorizontalPoint T sigma)) <=
      TS298.Goldbach.rightLineScale x := by
  by_cases hx : x = 0
  case pos =>
    subst x
    simpa [Complex.zero_cpow (finiteGridBottomHorizontalPoint_ne_zero T hT sigma)] using
      TS298.Goldbach.rightLineScale_nonnegative 0
  case neg =>
    have hxPos : 0 < x := Nat.pos_of_ne_zero hx
    rw [Complex.norm_natCast_cpow_of_pos hxPos]
    have hBase : (1 : Real) <= (x : Real) := by exact_mod_cast hxPos
    have hRe : (finiteGridBottomHorizontalPoint T sigma).re <= 2 := by
      simpa [finiteGridBottomHorizontalPoint, TS294.Goldbach.fixedPerronRight] using hSigma
    have hPow := Real.rpow_le_rpow_of_exponent_le hBase hRe
    rw [Real.rpow_two] at hPow
    exact hPow.trans (TS298.Goldbach.nat_sq_le_rightLineScale x)

theorem triangleSplineMellinKernel_finiteGridTop_norm_le
    (T : Nat) (hT : 1 <= T) (sigma : Real) :
    norm
        (TS257.Goldbach.triangleSplineMellinKernel
          (finiteGridTopHorizontalPoint T sigma)) <=
      1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 := by
  let tau : Real := TS299.Goldbach.finiteGridStrongTau T
  let s : Complex := finiteGridTopHorizontalPoint T sigma
  have hTau : 0 < tau := TS299.Goldbach.finiteGridStrongTau_pos hT
  have hs : tau <= norm s := by
    have hIm := Complex.abs_im_le_abs s
    simpa [s, tau, finiteGridTopHorizontalPoint, Complex.norm_eq_abs,
      abs_of_pos hTau] using hIm
  have hsOne : tau <= norm (s + 1) := by
    have hIm := Complex.abs_im_le_abs (s + 1)
    simpa [s, tau, finiteGridTopHorizontalPoint, Complex.norm_eq_abs,
      abs_of_pos hTau] using hIm
  have hProduct : tau ^ 2 <= norm s * norm (s + 1) := by
    rw [pow_two]
    exact mul_le_mul hs hsOne hTau.le (norm_nonneg s)
  unfold TS257.Goldbach.triangleSplineMellinKernel
  rw [norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hTau) hProduct

theorem triangleSplineMellinKernel_finiteGridBottom_norm_le
    (T : Nat) (hT : 1 <= T) (sigma : Real) :
    norm
        (TS257.Goldbach.triangleSplineMellinKernel
          (finiteGridBottomHorizontalPoint T sigma)) <=
      1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 := by
  let tau : Real := TS299.Goldbach.finiteGridStrongTau T
  let s : Complex := finiteGridBottomHorizontalPoint T sigma
  have hTau : 0 < tau := TS299.Goldbach.finiteGridStrongTau_pos hT
  have hs : tau <= norm s := by
    have hIm := Complex.abs_im_le_abs s
    simpa [s, tau, finiteGridBottomHorizontalPoint, Complex.norm_eq_abs,
      abs_of_pos hTau] using hIm
  have hsOne : tau <= norm (s + 1) := by
    have hIm := Complex.abs_im_le_abs (s + 1)
    simpa [s, tau, finiteGridBottomHorizontalPoint, Complex.norm_eq_abs,
      abs_of_pos hTau] using hIm
  have hProduct : tau ^ 2 <= norm s * norm (s + 1) := by
    rw [pow_two]
    exact mul_le_mul hs hsOne hTau.le (norm_nonneg s)
  unfold TS257.Goldbach.triangleSplineMellinKernel
  rw [norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hTau) hProduct

noncomputable def finiteGridTopZeroLoadPointwise
    (x T : Nat) (sigma : Real) : Real :=
  TS295.Goldbach.reciprocalZeroLoad T (TS299.Goldbach.finiteGridStrongTau T) *
    norm ((x : Complex) ^ (finiteGridTopHorizontalPoint T sigma)) *
    norm
      (TS257.Goldbach.triangleSplineMellinKernel
        (finiteGridTopHorizontalPoint T sigma))

noncomputable def finiteGridBottomZeroLoadPointwise
    (x T : Nat) (sigma : Real) : Real :=
  TS295.Goldbach.reciprocalZeroLoad T (TS299.Goldbach.finiteGridStrongTau T) *
    norm ((x : Complex) ^ (finiteGridBottomHorizontalPoint T sigma)) *
    norm
      (TS257.Goldbach.triangleSplineMellinKernel
        (finiteGridBottomHorizontalPoint T sigma))

theorem finiteGridTopZeroLoadPointwise_le
    (x T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    finiteGridTopZeroLoadPointwise x T sigma <=
      TS298.Goldbach.rightLineScale x *
        (TS299.Goldbach.finiteGridClosedLoadEnvelope T / (T : Real) ^ 2) := by
  have hTau : (T : Real) <= TS299.Goldbach.finiteGridStrongTau T :=
    (TS299.Goldbach.finiteGridStrongTau_gt T).le
  have hTPos : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hInv :
      1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 <=
        1 / (T : Real) ^ 2 := by
    have hTauPos : 0 < TS299.Goldbach.finiteGridStrongTau T :=
      TS299.Goldbach.finiteGridStrongTau_pos hT
    have hSq :
        (T : Real) ^ 2 <= (TS299.Goldbach.finiteGridStrongTau T) ^ 2 :=
      by simpa [pow_two] using mul_self_le_mul_self hTPos.le hTau
    exact one_div_le_one_div_of_le (sq_pos_of_pos hTPos)
      hSq
  have hClosed0 := finiteGridClosedLoadEnvelope_nonnegative T hT
  have hScale0 := TS298.Goldbach.rightLineScale_nonnegative x
  unfold finiteGridTopZeroLoadPointwise
  calc
    TS295.Goldbach.reciprocalZeroLoad T (TS299.Goldbach.finiteGridStrongTau T) *
          norm ((x : Complex) ^ (finiteGridTopHorizontalPoint T sigma)) *
          norm (TS257.Goldbach.triangleSplineMellinKernel
            (finiteGridTopHorizontalPoint T sigma)) <=
        TS299.Goldbach.finiteGridClosedLoadEnvelope T *
          TS298.Goldbach.rightLineScale x *
          (1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2) := by
      have hFirst :
          TS295.Goldbach.reciprocalZeroLoad T
                (TS299.Goldbach.finiteGridStrongTau T) *
              norm ((x : Complex) ^ (finiteGridTopHorizontalPoint T sigma)) <=
            TS299.Goldbach.finiteGridClosedLoadEnvelope T *
              TS298.Goldbach.rightLineScale x :=
        mul_le_mul
          (TS299.Goldbach.finiteGridStrongLoad_le_closed T hT)
          (nat_cpow_finiteGridTop_norm_le_rightLineScale x T hT sigma hSigma)
          (norm_nonneg _)
          hClosed0
      exact mul_le_mul hFirst
        (triangleSplineMellinKernel_finiteGridTop_norm_le T hT sigma)
        (norm_nonneg _)
        (mul_nonneg hClosed0 hScale0)
    _ <= TS299.Goldbach.finiteGridClosedLoadEnvelope T *
          TS298.Goldbach.rightLineScale x * (1 / (T : Real) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hInv (mul_nonneg hClosed0 hScale0)
    _ = TS298.Goldbach.rightLineScale x *
          (TS299.Goldbach.finiteGridClosedLoadEnvelope T / (T : Real) ^ 2) := by
      ring

theorem finiteGridBottomZeroLoadPointwise_le
    (x T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    finiteGridBottomZeroLoadPointwise x T sigma <=
      TS298.Goldbach.rightLineScale x *
        (TS299.Goldbach.finiteGridClosedLoadEnvelope T / (T : Real) ^ 2) := by
  have hTau : (T : Real) <= TS299.Goldbach.finiteGridStrongTau T :=
    (TS299.Goldbach.finiteGridStrongTau_gt T).le
  have hTPos : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hInv :
      1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 <=
        1 / (T : Real) ^ 2 := by
    have hTauPos : 0 < TS299.Goldbach.finiteGridStrongTau T :=
      TS299.Goldbach.finiteGridStrongTau_pos hT
    have hSq :
        (T : Real) ^ 2 <= (TS299.Goldbach.finiteGridStrongTau T) ^ 2 :=
      by simpa [pow_two] using mul_self_le_mul_self hTPos.le hTau
    exact one_div_le_one_div_of_le (sq_pos_of_pos hTPos)
      hSq
  have hClosed0 := finiteGridClosedLoadEnvelope_nonnegative T hT
  have hScale0 := TS298.Goldbach.rightLineScale_nonnegative x
  unfold finiteGridBottomZeroLoadPointwise
  calc
    TS295.Goldbach.reciprocalZeroLoad T (TS299.Goldbach.finiteGridStrongTau T) *
          norm ((x : Complex) ^ (finiteGridBottomHorizontalPoint T sigma)) *
          norm (TS257.Goldbach.triangleSplineMellinKernel
            (finiteGridBottomHorizontalPoint T sigma)) <=
        TS299.Goldbach.finiteGridClosedLoadEnvelope T *
          TS298.Goldbach.rightLineScale x *
          (1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2) := by
      have hFirst :
          TS295.Goldbach.reciprocalZeroLoad T
                (TS299.Goldbach.finiteGridStrongTau T) *
              norm ((x : Complex) ^ (finiteGridBottomHorizontalPoint T sigma)) <=
            TS299.Goldbach.finiteGridClosedLoadEnvelope T *
              TS298.Goldbach.rightLineScale x :=
        mul_le_mul
          (TS299.Goldbach.finiteGridStrongLoad_le_closed T hT)
          (nat_cpow_finiteGridBottom_norm_le_rightLineScale x T hT sigma hSigma)
          (norm_nonneg _)
          hClosed0
      exact mul_le_mul hFirst
        (triangleSplineMellinKernel_finiteGridBottom_norm_le T hT sigma)
        (norm_nonneg _)
        (mul_nonneg hClosed0 hScale0)
    _ <= TS299.Goldbach.finiteGridClosedLoadEnvelope T *
          TS298.Goldbach.rightLineScale x * (1 / (T : Real) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hInv (mul_nonneg hClosed0 hScale0)
    _ = TS298.Goldbach.rightLineScale x *
          (TS299.Goldbach.finiteGridClosedLoadEnvelope T / (T : Real) ^ 2) := by
      ring

theorem finiteGridTopZeroLoad_integratedWidth_le
    (x T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    (7 / 2 : Real) * finiteGridTopZeroLoadPointwise x T sigma <=
      finiteGridHorizontalZeroLoadComponent x T := by
  unfold finiteGridHorizontalZeroLoadComponent
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left
    (finiteGridTopZeroLoadPointwise_le x T hT sigma hSigma)
    (by norm_num : (0 : Real) <= 7 / 2)

theorem finiteGridBottomZeroLoad_integratedWidth_le
    (x T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    (7 / 2 : Real) * finiteGridBottomZeroLoadPointwise x T sigma <=
      finiteGridHorizontalZeroLoadComponent x T := by
  unfold finiteGridHorizontalZeroLoadComponent
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left
    (finiteGridBottomZeroLoadPointwise_le x T hT sigma hSigma)
    (by norm_num : (0 : Real) <= 7 / 2)

/-- For every fixed arithmetic scale, the integrated zero-load component vanishes. -/
theorem finiteGridHorizontalZeroLoadComponent_tendsto_zero
    (x : Nat) :
    Tendsto (finiteGridHorizontalZeroLoadComponent x) atTop (nhds 0) := by
  unfold finiteGridHorizontalZeroLoadComponent
  simpa using finiteGridClosedLoad_div_sq_tendsto_zero.const_mul
    ((7 / 2 : Real) * TS298.Goldbach.rightLineScale x)

end ClosedLoadDecay

section ConcreteCenteredQuotientInterface

/--
Exact centered-log data for the TS296 finite xi quotient, now centered at the
quantitative TS299 grid height.  This structure is deliberately stronger than
bare nonvanishing: it carries the local logarithm and the real-part envelope
needed by Borel-Caratheodory.
-/
structure FiniteGridCenteredXiQuotientLogData
    (T : Nat) (hT : 1 <= T) (sigma : Real) where
  topLog :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      (TS296.Goldbach.heightXiQuotient T)
      (finiteGridTopHorizontalPoint T sigma)
  bottomLog :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      (TS296.Goldbach.heightXiQuotient T)
      (finiteGridBottomHorizontalPoint T sigma)
  topRealPart : CenteredLogRealPartEnvelopeData topLog
  bottomRealPart : CenteredLogRealPartEnvelopeData bottomLog

/-- Exact top quotient reduction to the centered real-part envelope. -/
theorem FiniteGridCenteredXiQuotientLogData.top_logDerivative_norm_le
    {T : Nat} {hT : 1 <= T} {sigma : Real}
    (D : FiniteGridCenteredXiQuotientLogData T hT sigma) :
    norm
        (deriv (TS296.Goldbach.heightXiQuotient T)
              (finiteGridTopHorizontalPoint T sigma) /
          TS296.Goldbach.heightXiQuotient T
              (finiteGridTopHorizontalPoint T sigma)) <=
      4 * D.topRealPart.bound / D.topLog.radius :=
  LocalHolomorphicLogCauchyData.logDerivative_norm_le_centered
    D.topLog D.topRealPart

/-- Exact bottom quotient reduction to the centered real-part envelope. -/
theorem FiniteGridCenteredXiQuotientLogData.bottom_logDerivative_norm_le
    {T : Nat} {hT : 1 <= T} {sigma : Real}
    (D : FiniteGridCenteredXiQuotientLogData T hT sigma) :
    norm
        (deriv (TS296.Goldbach.heightXiQuotient T)
              (finiteGridBottomHorizontalPoint T sigma) /
          TS296.Goldbach.heightXiQuotient T
              (finiteGridBottomHorizontalPoint T sigma)) <=
      4 * D.bottomRealPart.bound / D.bottomLog.radius :=
  LocalHolomorphicLogCauchyData.logDerivative_norm_le_centered
    D.bottomLog D.bottomRealPart

/--
Named remaining analytic statement.  It cannot follow from TS289 growth and
TS299 zero separation alone because it includes quantitative control of the
quotient value at the center.
-/
def FiniteGridCenteredXiQuotientRealPartEnvelopeStatement : Prop :=
  forall (T : Nat) (hT : 1 <= T) (sigma : Real),
    Membership.mem
        (Icc TS294.Goldbach.fixedPerronLeft
          TS294.Goldbach.fixedPerronRight) sigma ->
      Nonempty (FiniteGridCenteredXiQuotientLogData T hT sigma)

end ConcreteCenteredQuotientInterface

structure CenteredBorelCaratheodoryAndClosedLoadLedger where
  schwarz_transform_backport_proved : True
  centered_borel_caratheodory_proved : True
  centered_log_branch_invariance_proved : True
  centered_log_cauchy_reduction_proved : True
  ts299_closed_load_routed_to_horizontal_geometry : True
  closed_load_div_T_sq_tendsto_zero_proved : True
  fixed_scale_integrated_load_tendsto_zero_proved : True
  finite_grid_quotient_centered_interface_defined : True
  centered_real_part_envelope_not_proved : True
  quotient_minimum_modulus_not_proved : True
  completion_correction_rate_not_proved : True
  full_horizontal_decay_not_proved : True
  left_boundary_not_estimated : True
  exceptional_inventory_not_completed : True
  perron_inversion_not_proved : True
  meromorphic_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def centeredBorelCaratheodoryAndClosedLoadLedger :
    CenteredBorelCaratheodoryAndClosedLoadLedger where
  schwarz_transform_backport_proved := True.intro
  centered_borel_caratheodory_proved := True.intro
  centered_log_branch_invariance_proved := True.intro
  centered_log_cauchy_reduction_proved := True.intro
  ts299_closed_load_routed_to_horizontal_geometry := True.intro
  closed_load_div_T_sq_tendsto_zero_proved := True.intro
  fixed_scale_integrated_load_tendsto_zero_proved := True.intro
  finite_grid_quotient_centered_interface_defined := True.intro
  centered_real_part_envelope_not_proved := True.intro
  quotient_minimum_modulus_not_proved := True.intro
  completion_correction_rate_not_proved := True.intro
  full_horizontal_decay_not_proved := True.intro
  left_boundary_not_estimated := True.intro
  exceptional_inventory_not_completed := True.intro
  perron_inversion_not_proved := True.intro
  meromorphic_residue_theorem_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS300
