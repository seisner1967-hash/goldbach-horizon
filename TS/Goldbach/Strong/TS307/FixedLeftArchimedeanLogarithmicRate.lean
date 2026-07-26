import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import TS.Goldbach.Strong.TS306.ExceptionalResidueInventory

/-!
# TS307: Fixed-left archimedean logarithmic rate

This module closes the sole analytic input left open by TS305.  It derives a
logarithmic bound for the Gamma logarithmic derivative on `Re(s) = 5/2` from
Euler's finite `GammaSeq`, without Binet, Stirling, a digamma API, or an
infinite product.

The proof has four layers:

* a locally uniform Euler-integral proof of `GammaSeq -> Gamma` on `Re(s) > 0`;
* the exact finite logarithmic derivative and a harmonic cutoff at
  `ceil (|t| + 2)`;
* the exact unit norm of the tangent term on the reflected line;
* assembly into `TS305.FixedLeftArchimedeanBoundData` and unconditional routing
  of the fixed-left contour side.
-/

noncomputable section

namespace TS307
namespace Goldbach

open Complex Filter MeasureTheory Metric Set Topology

theorem gammaSeq_ne_zero
    {s : Complex} {n : Nat}
    (hs : 0 < s.re)
    (hn : Not (n = 0)) :
    Not (Complex.GammaSeq s n = 0) := by
  unfold Complex.GammaSeq
  exact div_ne_zero
    (mul_ne_zero
      (mt (Complex.cpow_eq_zero_iff _ _).mp (fun h =>
        (Nat.cast_ne_zero.mpr hn) h.1))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
    (Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      have hj0 : 0 <= (j : Real) := Nat.cast_nonneg j
      intro h
      have hRe := congrArg Complex.re h
      simp at hRe
      linarith))

theorem gammaSeq_differentiableAt
    {s : Complex} {n : Nat}
    (hs : 0 < s.re)
    (hn : Not (n = 0)) :
    DifferentiableAt Complex (fun z => Complex.GammaSeq z n) s := by
  letI : NeZero (n : Complex) := { out := Nat.cast_ne_zero.mpr hn }
  unfold Complex.GammaSeq
  exact DifferentiableAt.div
    ((differentiableAt_const_cpow_of_neZero (n : Complex) s).mul
      (differentiableAt_const (n.factorial : Complex)))
    (DifferentiableAt.finset_prod fun j _ =>
      differentiableAt_id.add (differentiableAt_const (j : Complex)))
    (Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      have hj0 : 0 <= (j : Real) := Nat.cast_nonneg j
      intro h
      have hRe := congrArg Complex.re h
      simp at hRe
      linarith))

theorem gammaSeq_logDeriv_eq
    {s : Complex} {n : Nat}
    (hs : 0 < s.re)
    (hn : Not (n = 0)) :
    logDeriv (fun z => Complex.GammaSeq z n) s =
      Complex.log (n : Complex) -
        Finset.sum (Finset.range (n + 1)) (fun j => 1 / (s + j)) := by
  let powPart : Complex -> Complex := fun z =>
    (n : Complex) ^ z * (n.factorial : Complex)
  let denominator : Complex -> Complex := fun z =>
    Finset.prod (Finset.range (n + 1)) (fun j => z + (j : Complex))
  have hPowNe : Not (powPart s = 0) := by
    dsimp [powPart]
    exact mul_ne_zero
      (mt (Complex.cpow_eq_zero_iff _ _).mp (fun h =>
        (Nat.cast_ne_zero.mpr hn) h.1))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hDenNe : Not (denominator s = 0) := by
    dsimp [denominator]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hj0 : 0 <= (j : Real) := Nat.cast_nonneg j
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hPowDiff : DifferentiableAt Complex powPart s := by
    dsimp [powPart]
    exact ((hasDerivAt_id s).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hn))).differentiableAt.mul
        (differentiableAt_const (n.factorial : Complex))
  have hDenDiff : DifferentiableAt Complex denominator s := by
    dsimp [denominator]
    exact DifferentiableAt.finset_prod fun j _ =>
      differentiableAt_id.add (differentiableAt_const (j : Complex))
  have hDiv := logDeriv_div s hPowNe hDenNe hPowDiff hDenDiff
  have hPow : logDeriv powPart s = Complex.log (n : Complex) := by
    have hDeriv : HasDerivAt powPart
        (((n : Complex) ^ s * Complex.log (n : Complex)) *
          (n.factorial : Complex)) s := by
      dsimp [powPart]
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id s).const_cpow
          (Or.inl (Nat.cast_ne_zero.mpr hn))).mul_const
            (n.factorial : Complex))
    unfold logDeriv
    change deriv powPart s / powPart s = _
    rw [hDeriv.deriv]
    dsimp [powPart]
    field_simp [mt (Complex.cpow_eq_zero_iff _ _).mp (fun h =>
      (Nat.cast_ne_zero.mpr hn) h.1),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
    ring
  have hDen : logDeriv denominator s =
      Finset.sum (Finset.range (n + 1)) (fun j => 1 / (s + j)) := by
    dsimp [denominator]
    rw [logDeriv_prod]
    next =>
      apply Finset.sum_congr rfl
      intro j hj
      simp only [logDeriv_apply, deriv_add_const, deriv_id'', one_div]
    next =>
      intro j hj
      have hj0 : 0 <= (j : Real) := Nat.cast_nonneg j
      intro h
      have hRe := congrArg Complex.re h
      simp at hRe
      linarith
    next =>
      intro j hj
      exact differentiableAt_id.add (differentiableAt_const (j : Complex))
  change logDeriv (fun z => powPart z / denominator z) s = _
  rw [hDiv, hPow, hDen]

/-! ## Uniform Euler-integral approximation -/

noncomputable def gammaEulerCoefficient (n : Nat) (x : Real) : Real :=
  Set.indicator (Set.Ioc (0 : Real) n) (fun y => (1 - y / n) ^ n) x

theorem gammaEulerCoefficient_tendsto
    {x : Real} (hx : 0 < x) :
    Tendsto (fun n : Nat => gammaEulerCoefficient n x) atTop
      (nhds (Real.exp (-x))) := by
  refine Tendsto.congr' ?_ (tendsto_one_plus_div_pow_exp (-x))
  next =>
    show Filter.EventuallyEq atTop
      (fun n : Nat => (1 + (-x) / n) ^ n)
      (fun n : Nat => gammaEulerCoefficient n x)
    filter_upwards [eventually_ge_atTop (Nat.ceil x),
      eventually_ne_atTop 0] with n hn hn0
    unfold gammaEulerCoefficient
    rw [Set.indicator_of_mem]
    rw [neg_div, <- sub_eq_add_neg]
    exact mem_Ioc.mpr <| And.intro hx <|
      (Nat.le_ceil x).trans (by exact_mod_cast hn)

noncomputable def gammaCompactPowerMajorant
    (delta upper x : Real) : Real :=
  x ^ (delta - 1) + x ^ (upper - 1)

theorem norm_real_cpow_le_gammaCompactPowerMajorant
    {delta upper x : Real} {s : Complex}
    (hBounds : delta <= s.re /\ s.re <= upper)
    (hx : 0 < x) :
    norm ((x : Complex) ^ (s - 1)) <=
      gammaCompactPowerMajorant delta upper x := by
  rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx]
  simp only [sub_re, one_re]
  unfold gammaCompactPowerMajorant
  by_cases hxOne : x <= 1
  case pos =>
    have hExp : delta - 1 <= s.re - 1 := sub_le_sub_right hBounds.1 1
    have hPower := Real.rpow_le_rpow_of_exponent_ge hx hxOne hExp
    exact hPower.trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  case neg =>
    have hxOne' : 1 <= x := le_of_not_ge hxOne
    have hExp : s.re - 1 <= upper - 1 := sub_le_sub_right hBounds.2 1
    have hPower := Real.rpow_le_rpow_of_exponent_le hxOne' hExp
    exact hPower.trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))

theorem gammaEulerCoefficient_nonnegative
    {n : Nat} {x : Real} :
    0 <= gammaEulerCoefficient n x := by
  unfold gammaEulerCoefficient
  by_cases hxn : Membership.mem (Set.Ioc (0 : Real) n) x
  case pos =>
    rw [Set.indicator_of_mem hxn]
    have hnPos : (0 : Real) < n := hxn.1.trans_le hxn.2
    exact pow_nonneg
      (sub_nonneg.mpr ((div_le_one hnPos).mpr hxn.2)) _
  case neg =>
    rw [Set.indicator_of_not_mem hxn]

theorem gammaEulerCoefficient_le_exp_neg
    {n : Nat} {x : Real} :
    gammaEulerCoefficient n x <= Real.exp (-x) := by
  unfold gammaEulerCoefficient
  by_cases hxn : Membership.mem (Set.Ioc (0 : Real) n) x
  case pos =>
    rw [Set.indicator_of_mem hxn]
    exact Real.one_sub_div_pow_le_exp_neg hxn.2
  case neg =>
    rw [Set.indicator_of_not_mem hxn]
    exact (Real.exp_pos _).le

noncomputable def gammaUniformErrorIntegrand
    (delta upper : Real) (n : Nat) (x : Real) : Real :=
  norm (gammaEulerCoefficient n x - Real.exp (-x)) *
    gammaCompactPowerMajorant delta upper x

noncomputable def gammaUniformDominatingIntegrand
    (delta upper x : Real) : Real :=
  2 * Real.exp (-x) * gammaCompactPowerMajorant delta upper x

theorem gammaUniformErrorIntegrand_le_dominating
    {delta upper x : Real} {n : Nat} (hx : 0 < x) :
    gammaUniformErrorIntegrand delta upper n x <=
      gammaUniformDominatingIntegrand delta upper x := by
  have hCoeff0 := gammaEulerCoefficient_nonnegative (n := n) (x := x)
  have hCoeff := gammaEulerCoefficient_le_exp_neg (n := n) (x := x)
  have hAbs : norm (gammaEulerCoefficient n x - Real.exp (-x)) <=
      2 * Real.exp (-x) := by
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hCoeff)]
    nlinarith [Real.exp_pos (-x)]
  unfold gammaUniformErrorIntegrand gammaUniformDominatingIntegrand
  exact mul_le_mul_of_nonneg_right hAbs
    (add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))

theorem gammaUniformDominatingIntegrand_integrableOn
    {delta upper : Real} (hdelta : 0 < delta) (hupper : 0 < upper) :
    IntegrableOn (gammaUniformDominatingIntegrand delta upper) (Set.Ioi 0) := by
  have hDelta := (Real.GammaIntegral_convergent hdelta).const_mul 2
  have hUpper := (Real.GammaIntegral_convergent hupper).const_mul 2
  have hAdd := hDelta.add hUpper
  unfold IntegrableOn at *
  apply hAdd.congr
  filter_upwards with x
  unfold gammaUniformDominatingIntegrand gammaCompactPowerMajorant
  change 2 * (Real.exp (-x) * x ^ (delta - 1)) +
      2 * (Real.exp (-x) * x ^ (upper - 1)) =
    2 * Real.exp (-x) * (x ^ (delta - 1) + x ^ (upper - 1))
  ring

theorem gammaUniformErrorIntegrand_tendsto_zero
    {delta upper x : Real} (hx : 0 < x) :
    Tendsto (fun n : Nat => gammaUniformErrorIntegrand delta upper n x)
      atTop (nhds 0) := by
  unfold gammaUniformErrorIntegrand
  have hCoeff := gammaEulerCoefficient_tendsto hx
  have hSub : Tendsto
      (fun n : Nat => gammaEulerCoefficient n x - Real.exp (-x))
      atTop (nhds 0) := by
    simpa using hCoeff.sub_const (Real.exp (-x))
  simpa using hSub.norm.mul_const
    (gammaCompactPowerMajorant delta upper x)

theorem gammaUniformErrorIntegrand_aestronglyMeasurable
    (delta upper : Real) (n : Nat) :
    AEStronglyMeasurable (gammaUniformErrorIntegrand delta upper n)
      (volume.restrict (Set.Ioi 0)) := by
  have hCoeff : Measurable (gammaEulerCoefficient n) := by
    unfold gammaEulerCoefficient
    exact (((continuous_const.sub
      (continuous_id.div_const (n : Real))).pow n).measurable.indicator
        measurableSet_Ioc)
  have hExp : Measurable (fun x : Real => Real.exp (-x)) :=
    (Real.continuous_exp.comp continuous_neg).measurable
  have hPower : AEStronglyMeasurable
      (gammaCompactPowerMajorant delta upper)
      (volume.restrict (Set.Ioi 0)) := by
    have hCont : ContinuousOn
        (gammaCompactPowerMajorant delta upper) (Set.Ioi 0) := by
      unfold gammaCompactPowerMajorant
      apply ContinuousOn.add
      next =>
        intro x hx
        exact (Real.continuousAt_rpow_const x (delta - 1)
          (Or.inl hx.ne')).continuousWithinAt
      next =>
        intro x hx
        exact (Real.continuousAt_rpow_const x (upper - 1)
          (Or.inl hx.ne')).continuousWithinAt
    exact hCont.aestronglyMeasurable measurableSet_Ioi
  unfold gammaUniformErrorIntegrand
  exact ((hCoeff.sub hExp).norm.aestronglyMeasurable.mul hPower)

theorem gammaUniformError_integral_tendsto_zero
    {delta upper : Real} (hdelta : 0 < delta) (hupper : 0 < upper) :
    Tendsto
      (fun n : Nat => integral (volume.restrict (Set.Ioi 0))
        (gammaUniformErrorIntegrand delta upper n))
      atTop (nhds 0) := by
  have hDom := gammaUniformDominatingIntegrand_integrableOn hdelta hupper
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (gammaUniformDominatingIntegrand delta upper)
    (fun n => gammaUniformErrorIntegrand_aestronglyMeasurable delta upper n)
    hDom
    (fun n => (ae_restrict_iff' measurableSet_Ioi).mpr <|
      ae_of_all _ fun x hx => by
        have hError0 : 0 <= gammaUniformErrorIntegrand delta upper n x := by
          unfold gammaUniformErrorIntegrand gammaCompactPowerMajorant
          exact mul_nonneg (norm_nonneg _) (add_nonneg
            (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))
        simpa only [Real.norm_eq_abs, _root_.abs_of_nonneg hError0] using
          gammaUniformErrorIntegrand_le_dominating (n := n) hx)
    ((ae_restrict_iff' measurableSet_Ioi).mpr <|
      ae_of_all _ fun x hx => gammaUniformErrorIntegrand_tendsto_zero hx)
  simpa using h

noncomputable def gammaApproxIntegrand
    (n : Nat) (s : Complex) (x : Real) : Complex :=
  Set.indicator (Set.Ioc (0 : Real) n)
    (fun y => ((1 - y / n) ^ n : Real) * (y : Complex) ^ (s - 1)) x

noncomputable def gammaLimitIntegrand (s : Complex) (x : Real) : Complex :=
  (Real.exp (-x) : Complex) * (x : Complex) ^ (s - 1)

theorem gammaSeq_eq_integral_gammaApproxIntegrand
    {s : Complex} {n : Nat}
    (hs : 0 < s.re)
    (hn : Not (n = 0)) :
    Complex.GammaSeq s n = integral (volume.restrict (Set.Ioi 0))
      (gammaApproxIntegrand n s) := by
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn]
  unfold gammaApproxIntegrand
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (Nat.cast_nonneg n),
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self]

theorem gamma_eq_integral_gammaLimitIntegrand
    {s : Complex} (hs : 0 < s.re) :
    Complex.Gamma s = integral (volume.restrict (Set.Ioi 0))
      (gammaLimitIntegrand s) := by
  rw [Complex.Gamma_eq_integral hs]
  rfl

theorem gammaApproxIntegrand_integrable
    {s : Complex} {n : Nat}
    (hs : 0 < s.re) :
    Integrable (gammaApproxIntegrand n s)
      (volume.restrict (Set.Ioi 0)) := by
  unfold gammaApproxIntegrand
  rw [integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self,
    <- IntegrableOn,
    <- intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)]
  apply IntervalIntegrable.continuousOn_mul
  next =>
    refine intervalIntegral.intervalIntegrable_cpow' ?_
    rwa [sub_re, one_re, <- zero_sub, sub_lt_sub_iff_right]
  next =>
    apply Continuous.continuousOn
    exact RCLike.continuous_ofReal.comp
      ((continuous_const.sub (continuous_id'.div_const (n : Real))).pow n)

theorem gammaLimitIntegrand_integrable
    {s : Complex} (hs : 0 < s.re) :
    Integrable (gammaLimitIntegrand s)
      (volume.restrict (Set.Ioi 0)) := by
  simpa only [gammaLimitIntegrand] using Complex.GammaIntegral_convergent hs

theorem gammaApprox_sub_limit_eq_integral_sub
    {s : Complex} {n : Nat}
    (hs : 0 < s.re)
    (hn : Not (n = 0)) :
    Complex.GammaSeq s n - Complex.Gamma s =
      integral (volume.restrict (Set.Ioi 0))
        (fun x => gammaApproxIntegrand n s x - gammaLimitIntegrand s x) := by
  rw [gammaSeq_eq_integral_gammaApproxIntegrand hs hn,
    gamma_eq_integral_gammaLimitIntegrand hs]
  exact (integral_sub (gammaApproxIntegrand_integrable hs)
    (gammaLimitIntegrand_integrable hs)).symm

theorem gammaApproxIntegrand_eq_coefficient_mul
    (n : Nat) (s : Complex) (x : Real) :
    gammaApproxIntegrand n s x =
      (gammaEulerCoefficient n x : Complex) * (x : Complex) ^ (s - 1) := by
  unfold gammaApproxIntegrand gammaEulerCoefficient
  by_cases hx : Membership.mem (Set.Ioc (0 : Real) n) x
  next => simp [hx]
  next => simp [hx]

theorem gammaApprox_sub_limit_norm_le_error
    {delta upper x : Real} {s : Complex} {n : Nat}
    (hBounds : delta <= s.re /\ s.re <= upper)
    (hx : 0 < x) :
    norm (gammaApproxIntegrand n s x - gammaLimitIntegrand s x) <=
      gammaUniformErrorIntegrand delta upper n x := by
  have hPower := norm_real_cpow_le_gammaCompactPowerMajorant hBounds hx
  rw [gammaApproxIntegrand_eq_coefficient_mul]
  unfold gammaLimitIntegrand gammaUniformErrorIntegrand
  change norm (((gammaEulerCoefficient n x : Real) : Complex) *
      (x : Complex) ^ (s - 1) -
      (Real.exp (-x) : Complex) * (x : Complex) ^ (s - 1)) <=
    norm (gammaEulerCoefficient n x - Real.exp (-x)) *
      gammaCompactPowerMajorant delta upper x
  rw [<- sub_mul, norm_mul, Real.norm_eq_abs]
  rw [<- ofReal_sub, norm_real]
  exact mul_le_mul_of_nonneg_left hPower (abs_nonneg _)

theorem gammaSeq_sub_gamma_norm_le_error_integral
    {delta upper : Real} {s : Complex} {n : Nat}
    (hdelta : 0 < delta)
    (hupper : 0 < upper)
    (hBounds : delta <= s.re /\ s.re <= upper)
    (hn : Not (n = 0)) :
    norm (Complex.GammaSeq s n - Complex.Gamma s) <=
      integral (volume.restrict (Set.Ioi 0))
        (gammaUniformErrorIntegrand delta upper n) := by
  rw [gammaApprox_sub_limit_eq_integral_sub
    (hdelta.trans_le hBounds.1) hn]
  apply norm_integral_le_of_norm_le
  case hg =>
    exact (gammaUniformDominatingIntegrand_integrableOn hdelta hupper).mono'
      (gammaUniformErrorIntegrand_aestronglyMeasurable delta upper n)
      ((ae_restrict_iff' measurableSet_Ioi).mpr <|
        ae_of_all _ fun x hx => by
          have hError0 : 0 <= gammaUniformErrorIntegrand delta upper n x := by
            unfold gammaUniformErrorIntegrand gammaCompactPowerMajorant
            exact mul_nonneg (norm_nonneg _) (add_nonneg
              (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))
          simpa only [Real.norm_eq_abs, _root_.abs_of_nonneg hError0] using
            gammaUniformErrorIntegrand_le_dominating (n := n) hx)
  case h =>
    exact (ae_restrict_iff' measurableSet_Ioi).mpr <|
      ae_of_all _ fun x hx =>
        gammaApprox_sub_limit_norm_le_error hBounds hx

theorem gammaSeq_tendstoUniformlyOn_Gamma_reIcc
    {delta upper : Real}
    (hdelta : 0 < delta)
    (hupper : 0 < upper) :
    TendstoUniformlyOn
      (fun n s => Complex.GammaSeq s n) Complex.Gamma atTop
      {s : Complex | delta <= s.re /\ s.re <= upper} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hError := gammaUniformError_integral_tendsto_zero hdelta hupper
  have hEventually : Filter.Eventually
      (fun n => integral (volume.restrict (Set.Ioi 0))
        (gammaUniformErrorIntegrand delta upper n) < epsilon) atTop :=
    hError.eventually (Iio_mem_nhds hepsilon)
  filter_upwards [hEventually, eventually_ne_atTop 0] with n hnError hn0
  intro s hs
  rw [dist_comm, dist_eq]
  exact (gammaSeq_sub_gamma_norm_le_error_integral
    hdelta hupper hs hn0).trans_lt hnError

theorem gammaSeq_tendstoLocallyUniformlyOn_Gamma :
    TendstoLocallyUniformlyOn
      (fun n s => Complex.GammaSeq s n) Complex.Gamma atTop
      {s : Complex | 0 < s.re} := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro epsilon hepsilon s hs
  change 0 < s.re at hs
  let delta : Real := s.re / 2
  let upper : Real := 3 * s.re / 2
  let strip : Set Complex := {z | delta <= z.re /\ z.re <= upper}
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hupper : 0 < upper := by
    dsimp [upper]
    linarith
  have hsLower : delta < s.re := by
    dsimp [delta]
    linarith
  have hsUpper : s.re < upper := by
    dsimp [upper]
    linarith
  have hStripNhd : Membership.mem
      (nhdsWithin s {z : Complex | 0 < z.re}) strip := by
    apply mem_nhdsWithin_of_mem_nhds
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
          (And.intro hsLower hsUpper))
    intro z hz
    exact And.intro hz.1.le hz.2.le
  refine Exists.intro strip (And.intro hStripNhd ?_)
  have hUniform := gammaSeq_tendstoUniformlyOn_Gamma_reIcc hdelta hupper
  rw [Metric.tendstoUniformlyOn_iff] at hUniform
  exact hUniform epsilon hepsilon

theorem gammaSeq_logDeriv_tendsto_Gamma_logDeriv
    {s : Complex} (hs : 0 < s.re) :
    Tendsto
      (fun n : Nat => logDeriv (fun z => Complex.GammaSeq z n) s)
      atTop (nhds (logDeriv Complex.Gamma s)) := by
  let rightHalfPlane : Set Complex := {z | 0 < z.re}
  have hOpen : IsOpen rightHalfPlane :=
    isOpen_lt continuous_const Complex.continuous_re
  have hDiff : Filter.Eventually
      (fun n => DifferentiableOn Complex
        (fun z => Complex.GammaSeq z n) rightHalfPlane) atTop := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    intro z hz
    exact (gammaSeq_differentiableAt hz hn).differentiableWithinAt
  exact Complex.logDeriv_tendsto
    (fun n z => Complex.GammaSeq z n) Complex.Gamma hOpen
    (show rightHalfPlane from { val := s, property := hs })
    gammaSeq_tendstoLocallyUniformlyOn_Gamma
    hDiff (Complex.Gamma_ne_zero_of_re_pos hs)

/-! ## Harmonic control of the finite logarithmic derivatives -/

noncomputable def gammaHarmonicCutoff (t : Real) : Nat :=
  Nat.ceil (norm t + 2)

theorem gammaHarmonicCutoff_pos (t : Real) :
    0 < gammaHarmonicCutoff t := by
  unfold gammaHarmonicCutoff
  exact Nat.ceil_pos.mpr (by nlinarith [norm_nonneg t])

theorem abs_add_two_le_gammaHarmonicCutoff (t : Real) :
    norm t + 2 <= (gammaHarmonicCutoff t : Real) := by
  exact Nat.le_ceil (norm t + 2)

noncomputable def gammaDifferenceTerm
    (s : Complex) (j : Nat) : Complex :=
  1 / ((j + 1 : Nat) : Complex) - 1 / (s + j)

theorem norm_add_nat_ge_nat_add_one
    (t : Real) (j : Nat) :
    ((j + 1 : Nat) : Real) <=
      norm (TS305.Goldbach.fixedLeftReflectedPoint t + (j : Complex)) := by
  calc
    ((j + 1 : Nat) : Real) <=
        (TS305.Goldbach.fixedLeftReflectedPoint t + (j : Complex)).re := by
      simp only [add_re, TS305.Goldbach.fixedLeftReflectedPoint_re,
        natCast_re, Nat.cast_add, Nat.cast_one]
      linarith
    _ <= norm (TS305.Goldbach.fixedLeftReflectedPoint t + (j : Complex)).re := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ <= norm (TS305.Goldbach.fixedLeftReflectedPoint t + (j : Complex)) :=
      Complex.abs_re_le_abs _

theorem gammaDifferenceTerm_norm_le_low
    (t : Real) (j : Nat) :
    norm (gammaDifferenceTerm
      (TS305.Goldbach.fixedLeftReflectedPoint t) j) <=
      2 / ((j + 1 : Nat) : Real) := by
  have hjPos : 0 < ((j + 1 : Nat) : Real) := by positivity
  have hDen := norm_add_nat_ge_nat_add_one t j
  have hInv : norm (1 /
      (TS305.Goldbach.fixedLeftReflectedPoint t + (j : Complex))) <=
      1 / ((j + 1 : Nat) : Real) := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hjPos hDen
  calc
    norm (gammaDifferenceTerm
        (TS305.Goldbach.fixedLeftReflectedPoint t) j) <=
        norm (1 / (((j + 1 : Nat) : Complex))) +
          norm (1 / (TS305.Goldbach.fixedLeftReflectedPoint t + j)) :=
      norm_sub_le _ _
    _ <= 1 / ((j + 1 : Nat) : Real) +
        1 / ((j + 1 : Nat) : Real) := by
      exact add_le_add (by rw [norm_div, norm_one, norm_natCast]) hInv
    _ = 2 / ((j + 1 : Nat) : Real) := by ring

theorem gammaDifferenceTerm_eq
    (s : Complex) (j : Nat)
    (hs : Not (s + (j : Complex) = 0)) :
    gammaDifferenceTerm s j =
      (s - 1) /
        ((((j + 1 : Nat) : Complex)) * (s + (j : Complex))) := by
  unfold gammaDifferenceTerm
  have hj : Not ((((j + 1 : Nat) : Complex)) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  rw [div_sub_div 1 1 hj hs]
  push_cast
  ring

theorem reflectedPoint_sub_one_norm_le_cutoff
    (t : Real) :
    norm (TS305.Goldbach.fixedLeftReflectedPoint t - 1) <=
      (gammaHarmonicCutoff t : Real) := by
  have hPoint : TS305.Goldbach.fixedLeftReflectedPoint t - 1 =
      (3 / 2 : Complex) - (t : Complex) * Complex.I := by
    apply Complex.ext
    next =>
      simp only [sub_re, TS305.Goldbach.fixedLeftReflectedPoint_re,
        one_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
      norm_num
    next =>
      simp only [sub_im, TS305.Goldbach.fixedLeftReflectedPoint_im,
        one_im, ofReal_re, mul_im, I_re, I_im, ofReal_im]
      norm_num
  rw [hPoint]
  calc
    norm ((3 / 2 : Complex) - (t : Complex) * Complex.I) <=
        norm (3 / 2 : Complex) + norm ((t : Complex) * Complex.I) :=
      norm_sub_le _ _
    _ = 3 / 2 + norm t := by
      norm_num [norm_mul, norm_div]
    _ <= norm t + 2 := by linarith
    _ <= (gammaHarmonicCutoff t : Real) :=
      abs_add_two_le_gammaHarmonicCutoff t

theorem gammaDifferenceTerm_norm_le_high
    (t : Real) (j : Nat) :
    norm (gammaDifferenceTerm
      (TS305.Goldbach.fixedLeftReflectedPoint t) j) <=
      (gammaHarmonicCutoff t : Real) /
        (((j + 1 : Nat) : Real) ^ 2) := by
  have hs : Not (TS305.Goldbach.fixedLeftReflectedPoint t +
      (j : Complex) = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hj0 : 0 <= (j : Real) := Nat.cast_nonneg j
    linarith
  rw [gammaDifferenceTerm_eq _ _ hs, norm_div, norm_mul, norm_natCast]
  have hjPos : 0 < ((j + 1 : Nat) : Real) := by positivity
  have hDen := norm_add_nat_ge_nat_add_one t j
  calc
    norm (TS305.Goldbach.fixedLeftReflectedPoint t - 1) /
          (((j + 1 : Nat) : Real) *
            norm (TS305.Goldbach.fixedLeftReflectedPoint t + j)) <=
        (gammaHarmonicCutoff t : Real) /
          (((j + 1 : Nat) : Real) *
            norm (TS305.Goldbach.fixedLeftReflectedPoint t + j)) := by
      apply div_le_div_of_nonneg_right
      exact reflectedPoint_sub_one_norm_le_cutoff t
      positivity
    _ <= (gammaHarmonicCutoff t : Real) /
          (((j + 1 : Nat) : Real) ^ 2) := by
      apply div_le_div_of_nonneg_left
      next => positivity
      next => positivity
      next => nlinarith

theorem harmonic_real_eq_sum_range (n : Nat) :
    (harmonic n : Real) =
      Finset.sum (Finset.range n)
        (fun j => 1 / ((j + 1 : Nat) : Real)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, harmonic_succ]
      push_cast
      rw [ih]
      simp only [Nat.cast_add, Nat.cast_one, one_div]

theorem log_sub_harmonic_norm_le_one
    {n : Nat} (hn : 0 < n) :
    norm (Real.log n - (harmonic n : Real)) <= 1 := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hLogMono : Real.log n <= Real.log (n + 1) := by
    change Real.log (n : Real) <= Real.log ((n : Real) + 1)
    exact Real.strictMonoOn_log.monotoneOn
      hnReal
      (by change 0 < (n : Real) + 1; linarith)
      (by change (n : Real) <= (n : Real) + 1; linarith)
  have hLower : Real.log n <= (harmonic n : Real) :=
    hLogMono.trans (by
      simpa only [Nat.cast_add, Nat.cast_one] using
        log_add_one_le_harmonic n)
  have hUpper : (harmonic n : Real) <= 1 + Real.log n :=
    harmonic_le_one_add_log n
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hLower)]
  linarith

theorem cutoffQuadraticTail_strong
    (J k : Nat) (hJ : 0 < J) :
    Finset.sum (Finset.Ico J (J + k))
        (fun j => (J : Real) / (((j + 1 : Nat) : Real) ^ 2)) <=
      1 - (J : Real) / (J + k : Nat) := by
  induction k with
  | zero =>
      simp [hJ.ne']
  | succ k ih =>
      have hJle : J <= J + k := Nat.le_add_right J k
      rw [Nat.add_succ, Finset.sum_Ico_succ_top hJle]
      have hPosJ : 0 < (J : Real) := by exact_mod_cast hJ
      have hPosN : 0 < ((J + k : Nat) : Real) := by positivity
      have hTerm :
          (J : Real) / (((J + k + 1 : Nat) : Real) ^ 2) <=
            (J : Real) / (J + k : Nat) -
              (J : Real) / (J + k + 1 : Nat) := by
        let N : Real := (J + k : Nat)
        have hN : 0 < N := hPosN
        have hNp : 0 < N + 1 := by linarith
        have hEq :
            (J : Real) / (J + k : Nat) -
                (J : Real) / (J + k + 1 : Nat) =
              (J : Real) / (N * (N + 1)) := by
          dsimp [N]
          push_cast
          field_simp
          ring
        rw [hEq]
        apply div_le_div_of_nonneg_left hPosJ.le
        next => positivity
        next =>
          dsimp [N]
          push_cast
          nlinarith
      calc
        Finset.sum (Finset.Ico J (J + k))
              (fun j => (J : Real) / (((j + 1 : Nat) : Real) ^ 2)) +
            (J : Real) / (((J + k + 1 : Nat) : Real) ^ 2) <=
            (1 - (J : Real) / (J + k : Nat)) +
              ((J : Real) / (J + k : Nat) -
                (J : Real) / (J + k + 1 : Nat)) :=
          add_le_add ih hTerm
        _ = 1 - (J : Real) / (J + (k + 1) : Nat) := by
          push_cast
          ring

theorem cutoffQuadraticTail_le_one
    (J n : Nat) (hJ : 0 < J) :
    Finset.sum (Finset.Ico J n)
        (fun j => (J : Real) / (((j + 1 : Nat) : Real) ^ 2)) <= 1 := by
  by_cases hn : J <= n
  next =>
    let k := n - J
    have hnEq : n = J + k := by
      dsimp [k]
      omega
    rw [hnEq]
    exact (cutoffQuadraticTail_strong J k hJ).trans (by
      have : 0 <= (J : Real) / (J + k : Nat) := by positivity
      linarith)
  next =>
    rw [Finset.Ico_eq_empty (not_lt_of_ge (Nat.le_of_not_ge hn))]
    simp

theorem gammaDifferencePartialSum_norm_le
    (t : Real) {n : Nat}
    (hn : gammaHarmonicCutoff t <= n) :
    norm (Finset.sum (Finset.range n) (fun j =>
      gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j)) <=
      3 + 2 * Real.log (gammaHarmonicCutoff t) := by
  let J := gammaHarmonicCutoff t
  have hJ : 0 < J := gammaHarmonicCutoff_pos t
  have hSplit :
      Finset.sum (Finset.range n) (fun j =>
        gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j) =
      Finset.sum (Finset.range J) (fun j =>
        gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j) +
      Finset.sum (Finset.Ico J n) (fun j =>
        gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j) := by
    exact (Finset.sum_range_add_sum_Ico _ hn).symm
  rw [hSplit]
  have hLow :
      norm (Finset.sum (Finset.range J) (fun j =>
        gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j)) <=
        2 * (1 + Real.log J) := by
    calc
      norm (Finset.sum (Finset.range J) (fun j =>
          gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j)) <=
          Finset.sum (Finset.range J) (fun j =>
            norm (gammaDifferenceTerm
              (TS305.Goldbach.fixedLeftReflectedPoint t) j)) :=
        norm_sum_le _ _
      _ <= Finset.sum (Finset.range J)
          (fun j => 2 / ((j + 1 : Nat) : Real)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact gammaDifferenceTerm_norm_le_low t j
      _ = 2 * (harmonic J : Real) := by
        rw [harmonic_real_eq_sum_range]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ <= 2 * (1 + Real.log J) := by
        gcongr
        exact harmonic_le_one_add_log J
  have hHigh :
      norm (Finset.sum (Finset.Ico J n) (fun j =>
        gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j)) <= 1 := by
    calc
      norm (Finset.sum (Finset.Ico J n) (fun j =>
          gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j)) <=
          Finset.sum (Finset.Ico J n) (fun j =>
            norm (gammaDifferenceTerm
              (TS305.Goldbach.fixedLeftReflectedPoint t) j)) :=
        norm_sum_le _ _
      _ <= Finset.sum (Finset.Ico J n)
          (fun j => (J : Real) / (((j + 1 : Nat) : Real) ^ 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact gammaDifferenceTerm_norm_le_high t j
      _ <= 1 := cutoffQuadraticTail_le_one J n hJ
  calc
    norm (Finset.sum (Finset.range J) (fun j =>
          gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j) +
        Finset.sum (Finset.Ico J n) (fun j =>
          gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j)) <=
        norm (Finset.sum (Finset.range J) (fun j =>
          gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j)) +
        norm (Finset.sum (Finset.Ico J n) (fun j =>
          gammaDifferenceTerm (TS305.Goldbach.fixedLeftReflectedPoint t) j)) :=
      norm_add_le _ _
    _ <= 2 * (1 + Real.log J) + 1 := add_le_add hLow hHigh
    _ = 3 + 2 * Real.log (gammaHarmonicCutoff t) := by
      dsimp [J]
      ring

theorem harmonic_complex_eq_sum_range (n : Nat) :
    (harmonic n : Complex) =
      Finset.sum (Finset.range n)
        (fun j => 1 / ((j + 1 : Nat) : Complex)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, harmonic_succ]
      push_cast
      rw [ih]
      simp only [Nat.cast_add, Nat.cast_one, one_div]

theorem gammaSeq_logDeriv_eq_harmonic_decomposition
    (t : Real) {n : Nat} (hn : Not (n = 0)) :
    logDeriv (fun z => Complex.GammaSeq z n)
        (TS305.Goldbach.fixedLeftReflectedPoint t) =
      ((Real.log n - (harmonic n : Real) : Real) : Complex) +
        Finset.sum (Finset.range n) (fun j =>
          gammaDifferenceTerm
            (TS305.Goldbach.fixedLeftReflectedPoint t) j) -
        1 / (TS305.Goldbach.fixedLeftReflectedPoint t + (n : Complex)) := by
  rw [gammaSeq_logDeriv_eq (by simp) hn, Finset.sum_range_succ]
  unfold gammaDifferenceTerm
  rw [Finset.sum_sub_distrib]
  rw [<- harmonic_complex_eq_sum_range]
  rw [<- Complex.natCast_log]
  push_cast
  ring

theorem gammaSeq_logDeriv_reflected_norm_le
    (t : Real) {n : Nat}
    (hn0 : Not (n = 0))
    (hn : gammaHarmonicCutoff t <= n) :
    norm (logDeriv (fun z => Complex.GammaSeq z n)
      (TS305.Goldbach.fixedLeftReflectedPoint t)) <=
      5 + 2 * Real.log (gammaHarmonicCutoff t) := by
  rw [gammaSeq_logDeriv_eq_harmonic_decomposition t hn0]
  have hLog := log_sub_harmonic_norm_le_one (Nat.pos_of_ne_zero hn0)
  have hSum := gammaDifferencePartialSum_norm_le t hn
  have hLastDen : 1 <=
      norm (TS305.Goldbach.fixedLeftReflectedPoint t + (n : Complex)) := by
    exact (show (1 : Real) <= (n + 1 : Nat) by norm_num).trans
      (norm_add_nat_ge_nat_add_one t n)
  have hLast : norm (1 /
      (TS305.Goldbach.fixedLeftReflectedPoint t + (n : Complex))) <= 1 := by
    rw [norm_div, norm_one]
    simpa only [one_div_one] using
      one_div_le_one_div_of_le zero_lt_one hLastDen
  calc
    norm (((Real.log n - (harmonic n : Real) : Real) : Complex) +
        Finset.sum (Finset.range n) (fun j =>
          gammaDifferenceTerm
            (TS305.Goldbach.fixedLeftReflectedPoint t) j) -
        1 / (TS305.Goldbach.fixedLeftReflectedPoint t + (n : Complex))) <=
      norm ((Real.log n - (harmonic n : Real) : Real) : Complex) +
        norm (Finset.sum (Finset.range n) (fun j =>
          gammaDifferenceTerm
            (TS305.Goldbach.fixedLeftReflectedPoint t) j)) +
        norm (1 / (TS305.Goldbach.fixedLeftReflectedPoint t + (n : Complex))) := by
      exact (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ <= 1 + (3 + 2 * Real.log (gammaHarmonicCutoff t)) + 1 := by
      gcongr
      simpa only [Complex.norm_real] using hLog
    _ = 5 + 2 * Real.log (gammaHarmonicCutoff t) := by ring

theorem Gamma_logDeriv_reflected_norm_le_cutoff
    (t : Real) :
    norm (logDeriv Complex.Gamma
      (TS305.Goldbach.fixedLeftReflectedPoint t)) <=
      5 + 2 * Real.log (gammaHarmonicCutoff t) := by
  have hTendsto := gammaSeq_logDeriv_tendsto_Gamma_logDeriv
    (s := TS305.Goldbach.fixedLeftReflectedPoint t) (by simp)
  have hJ : 0 < gammaHarmonicCutoff t := gammaHarmonicCutoff_pos t
  have hBound : Filter.Eventually (fun n =>
      Membership.mem
        (Metric.closedBall 0
          (5 + 2 * Real.log (gammaHarmonicCutoff t)))
        (logDeriv (fun z => Complex.GammaSeq z n)
          (TS305.Goldbach.fixedLeftReflectedPoint t))) atTop := by
    filter_upwards [eventually_ge_atTop (gammaHarmonicCutoff t),
      eventually_ne_atTop 0] with n hn hn0
    rw [Metric.mem_closedBall, dist_zero_right]
    exact gammaSeq_logDeriv_reflected_norm_le t hn0 hn
  have hLimit := Metric.isClosed_ball.mem_of_tendsto hTendsto hBound
  simpa only [Metric.mem_closedBall, dist_zero_right] using hLimit

theorem gammaHarmonicCutoff_le_two_mul (t : Real) :
    (gammaHarmonicCutoff t : Real) <= 2 * (norm t + 2) := by
  have hCeil : (gammaHarmonicCutoff t : Real) < norm t + 2 + 1 := by
    exact Nat.ceil_lt_add_one (by positivity : 0 <= norm t + 2)
  have ht : 0 <= norm t := norm_nonneg t
  linarith

theorem log_gammaHarmonicCutoff_le (t : Real) :
    Real.log (gammaHarmonicCutoff t) <=
      1 + Real.log (norm t + 2) := by
  have hJPos : 0 < (gammaHarmonicCutoff t : Real) := by
    exact_mod_cast gammaHarmonicCutoff_pos t
  have hYPos : 0 < norm t + 2 := by positivity
  have hMono : Real.log (gammaHarmonicCutoff t) <=
      Real.log (2 * (norm t + 2)) := by
    exact Real.strictMonoOn_log.monotoneOn hJPos (mul_pos two_pos hYPos)
      (gammaHarmonicCutoff_le_two_mul t)
  rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hYPos.ne'] at hMono
  have hLogTwo : Real.log 2 <= 1 := by
    convert Real.log_le_sub_one_of_pos
      (show (0 : Real) < 2 by norm_num) using 1
    all_goals norm_num
  linarith

theorem Gamma_logDeriv_reflected_norm_le_logWeight
    (t : Real) :
    norm (logDeriv Complex.Gamma
      (TS305.Goldbach.fixedLeftReflectedPoint t)) <=
      7 * TS305.Goldbach.fixedLeftLogWeight t := by
  have hCutoff := Gamma_logDeriv_reflected_norm_le_cutoff t
  have hLog := log_gammaHarmonicCutoff_le t
  have hWeightLog : 0 <= Real.log (norm t + 2) := by
    apply Real.log_nonneg
    exact (show (1 : Real) <= norm t + 2 by
      nlinarith [norm_nonneg t])
  unfold TS305.Goldbach.fixedLeftLogWeight
  rw [<- Real.norm_eq_abs]
  nlinarith

theorem norm_tan_pi_div_four_add_mul_I (y : Real) :
    norm (Complex.tan ((Real.pi / 4 : Complex) +
      (y : Complex) * Complex.I)) = 1 := by
  let z : Complex := (Real.pi / 4 : Complex) + (y : Complex) * Complex.I
  have hRe : z.re = Real.pi / 4 := by
    dsimp [z]
    simp
  have hIm : z.im = y := by
    dsimp [z]
    simp
  have hConj : Complex.cos z = star (Complex.sin z) := by
    have hCoshStar : star (Complex.cosh (y : Complex)) =
        Complex.cosh (y : Complex) := by
      rw [<- Complex.ofReal_cosh]
      exact Complex.conj_ofReal _
    have hSinhStar : star (Complex.sinh (y : Complex)) =
        Complex.sinh (y : Complex) := by
      rw [<- Complex.ofReal_sinh]
      exact Complex.conj_ofReal _
    rw [Complex.sin_eq, Complex.cos_eq, hRe, hIm]
    rw [<- Complex.ofReal_sin, <- Complex.ofReal_cos,
      <- Complex.ofReal_cosh, <- Complex.ofReal_sinh]
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    simp [hCoshStar, hSinhStar, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hNorm : norm (Complex.sin z) = norm (Complex.cos z) := by
    rw [hConj]
    simp
  have hCos : Not (Complex.cos z = 0) := by
    intro h
    have hSin : Complex.sin z = 0 := by
      apply norm_eq_zero.mp
      rw [hNorm, h, norm_zero]
    have hIdentity := Complex.sin_sq_add_cos_sq z
    rw [hSin, h] at hIdentity
    norm_num at hIdentity
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  rw [hNorm, div_self]
  exact norm_ne_zero_iff.mpr hCos

theorem norm_tan_reflected_argument (t : Real) :
    norm (Complex.tan (Real.pi *
      TS305.Goldbach.fixedLeftReflectedPoint t / 2)) = 1 := by
  let y : Real := -(Real.pi * t / 2)
  let z : Complex := (Real.pi / 4 : Complex) + (y : Complex) * Complex.I
  have hPoint : TS305.Goldbach.fixedLeftReflectedPoint t =
      (5 / 2 : Complex) - (t : Complex) * Complex.I := by
    apply Complex.ext
    next =>
      simp only [TS305.Goldbach.fixedLeftReflectedPoint_re,
        sub_re, div_re, ofReal_re, ofReal_im, mul_re, I_re, I_im]
      norm_num
    next =>
      simp only [TS305.Goldbach.fixedLeftReflectedPoint_im,
        sub_im, div_im, ofReal_re, ofReal_im, mul_im, I_re, I_im]
      norm_num
  have hArg : Real.pi * TS305.Goldbach.fixedLeftReflectedPoint t / 2 =
      z + Real.pi := by
    rw [hPoint]
    dsimp [z, y]
    push_cast
    ring
  rw [hArg, Complex.tan_add_pi]
  exact norm_tan_pi_div_four_add_mul_I y

theorem zetaLeftReflectionCorrection_eq
    (t : Real) :
    TS305.Goldbach.zetaLeftReflectionCorrection
        (TS305.Goldbach.fixedLeftReflectedPoint t) =
      -Complex.log (2 * Real.pi : Complex) +
        logDeriv Complex.Gamma
          (TS305.Goldbach.fixedLeftReflectedPoint t) -
        (Real.pi / 2 : Complex) *
          Complex.tan (Real.pi *
            TS305.Goldbach.fixedLeftReflectedPoint t / 2) := by
  let s := TS305.Goldbach.fixedLeftReflectedPoint t
  let base : Complex := 2 * (Real.pi : Complex)
  let power : Complex -> Complex := fun z => base ^ (-z)
  let prefactor : Complex -> Complex := fun z => 2 * power z
  let trig : Complex -> Complex := fun z => Complex.cos (Real.pi * z / 2)
  have hBase : Not (base = 0) := by
    dsimp [base]
    exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hPowerNe : Not (power s = 0) := by
    dsimp [power]
    exact mt (Complex.cpow_eq_zero_iff _ _).mp (fun h => hBase h.1)
  have hPrefactorNe : Not (prefactor s = 0) := by
    dsimp [prefactor]
    exact mul_ne_zero (by norm_num) hPowerNe
  have hGammaNe : Not (Complex.Gamma s = 0) :=
    Complex.Gamma_ne_zero_of_re_pos (by dsimp [s]; simp)
  have hTrigNe : Not (trig s = 0) := by
    intro h
    apply TS305.Goldbach.zetaLeftReflectionFactor_ne_zero_reflected t
    dsimp [trig, s] at h
    unfold TS305.Goldbach.zetaLeftReflectionFactor
    rw [h]
    ring
  have hPowerDiff : DifferentiableAt Complex power s := by
    dsimp [power]
    letI : NeZero base := { out := hBase }
    exact (differentiableAt_const_cpow_of_neZero base (-s)).comp s
      differentiableAt_id.neg
  have hPrefactorDiff : DifferentiableAt Complex prefactor s := by
    dsimp [prefactor]
    exact (differentiableAt_const (2 : Complex)).mul hPowerDiff
  have hGammaDiff : DifferentiableAt Complex Complex.Gamma s :=
    Complex.differentiableAt_Gamma s (fun n => by
      intro h
      have hRe := congrArg Complex.re h
      dsimp [s] at hRe
      simp at hRe
      have hn : (0 : Real) <= n := Nat.cast_nonneg n
      linarith)
  have hTrigDiff : DifferentiableAt Complex trig s := by
    dsimp [trig]
    exact Complex.differentiableAt_cos.comp s
      (((differentiableAt_const (Real.pi : Complex)).mul
        differentiableAt_id).div_const 2)
  have hPowerLog : logDeriv power s = -Complex.log base := by
    have hDeriv : HasDerivAt power
        (base ^ (-s) * Complex.log base * (-1)) s := by
      dsimp [power]
      simpa only [id_eq] using
        ((hasDerivAt_id s).neg.const_cpow (Or.inl hBase))
    unfold logDeriv
    change deriv power s / power s = _
    rw [hDeriv.deriv]
    dsimp [power]
    field_simp [hPowerNe]
    ring
  have hPrefactorLog : logDeriv prefactor s = -Complex.log base := by
    rw [show prefactor = fun z => (2 : Complex) * power z by rfl,
      logDeriv_const_mul s 2 (by norm_num)]
    exact hPowerLog
  have hTrigLog : logDeriv trig s =
      -(Real.pi / 2 : Complex) *
        Complex.tan (Real.pi * s / 2) := by
    let inner : Complex -> Complex := fun z => Real.pi * z / 2
    have hInnerDiff : DifferentiableAt Complex inner s := by
      dsimp [inner]
      exact ((differentiableAt_const (Real.pi : Complex)).mul
        differentiableAt_id).div_const 2
    have hComp := logDeriv_comp
      (f := Complex.cos) (g := inner) Complex.differentiableAt_cos hInnerDiff
    have hInnerDeriv : deriv inner s = (Real.pi / 2 : Complex) := by
      have hHas : HasDerivAt inner (Real.pi / 2 : Complex) s := by
        dsimp [inner]
        simpa using ((hasDerivAt_const s (Real.pi : Complex)).mul
          (hasDerivAt_id s)).div_const 2
      exact hHas.deriv
    rw [hInnerDeriv, Complex.logDeriv_cos] at hComp
    dsimp [trig, inner]
    rw [show -(Real.pi / 2 : Complex) *
        Complex.tan (Real.pi * s / 2) =
        (-Complex.tan (Real.pi * s / 2)) * (Real.pi / 2) by ring]
    simpa only [Function.comp_apply, Pi.neg_apply] using hComp
  have hPairNe : Not (prefactor s * Complex.Gamma s = 0) :=
    mul_ne_zero hPrefactorNe hGammaNe
  have hPairDiff : DifferentiableAt Complex
      (fun z => prefactor z * Complex.Gamma z) s :=
    hPrefactorDiff.mul hGammaDiff
  have hOuter := logDeriv_mul s hPairNe hTrigNe hPairDiff hTrigDiff
  have hInner := logDeriv_mul s hPrefactorNe hGammaNe
    hPrefactorDiff hGammaDiff
  unfold TS305.Goldbach.zetaLeftReflectionCorrection
  rw [show TS305.Goldbach.zetaLeftReflectionFactor =
      (fun z => (prefactor z * Complex.Gamma z) * trig z) by
    funext z
    rfl]
  rw [hOuter, hInner, hPrefactorLog, hTrigLog]
  dsimp [s, base]
  ring

/-! ## Closed archimedean input and TS305 routing -/

/-- A closed constant for the fixed-left archimedean correction. -/
noncomputable def fixedLeftArchimedeanConstant : Real :=
  norm (Complex.log (2 * Real.pi : Complex)) + 7 + Real.pi / 2

theorem fixedLeftArchimedeanConstant_nonnegative :
    0 <= fixedLeftArchimedeanConstant := by
  unfold fixedLeftArchimedeanConstant
  positivity

theorem zetaLeftReflectionCorrection_norm_le_logWeight
    (t : Real) :
    norm
        (TS305.Goldbach.zetaLeftReflectionCorrection
          (TS305.Goldbach.fixedLeftReflectedPoint t)) <=
      fixedLeftArchimedeanConstant *
        TS305.Goldbach.fixedLeftLogWeight t := by
  let s := TS305.Goldbach.fixedLeftReflectedPoint t
  let a : Complex := Complex.log (2 * Real.pi : Complex)
  let g : Complex := logDeriv Complex.Gamma s
  let q : Complex :=
    (Real.pi / 2 : Complex) * Complex.tan (Real.pi * s / 2)
  have hFormula :
      TS305.Goldbach.zetaLeftReflectionCorrection s = -a + g - q := by
    simpa [s, a, g, q] using zetaLeftReflectionCorrection_eq t
  have hGamma :
      norm g <= 7 * TS305.Goldbach.fixedLeftLogWeight t := by
    simpa [s, g] using Gamma_logDeriv_reflected_norm_le_logWeight t
  have hTan : norm q = Real.pi / 2 := by
    have hPi : norm (Real.pi / 2 : Complex) = Real.pi / 2 := by
      rw [norm_div, norm_real, Real.norm_eq_abs,
        _root_.abs_of_nonneg Real.pi_pos.le]
      norm_num
    rw [show q = (Real.pi / 2 : Complex) *
        Complex.tan (Real.pi * s / 2) by rfl,
      norm_mul, norm_tan_reflected_argument t, hPi, mul_one]
  have hWeight : 1 <= TS305.Goldbach.fixedLeftLogWeight t :=
    TS305.Goldbach.one_le_fixedLeftLogWeight t
  have hConstantPart :
      norm a + Real.pi / 2 <=
        (norm a + Real.pi / 2) *
          TS305.Goldbach.fixedLeftLogWeight t := by
    have h := mul_le_mul_of_nonneg_left hWeight
      (by positivity : 0 <= norm a + Real.pi / 2)
    simpa using h
  rw [hFormula]
  calc
    norm (-a + g - q) <= norm (-a + g) + norm q := norm_sub_le _ _
    _ <= (norm a + norm g) + norm q := by
      gcongr
      simpa using norm_add_le (-a) g
    _ <= (norm a + 7 * TS305.Goldbach.fixedLeftLogWeight t) +
        Real.pi / 2 := by
      rw [hTan]
      gcongr
    _ <= (norm a + Real.pi / 2) *
          TS305.Goldbach.fixedLeftLogWeight t +
        7 * TS305.Goldbach.fixedLeftLogWeight t := by
      linarith
    _ = fixedLeftArchimedeanConstant *
          TS305.Goldbach.fixedLeftLogWeight t := by
      unfold fixedLeftArchimedeanConstant
      dsimp [a]
      ring

/-- Unconditional discharge of the sole analytic input left open by TS305. -/
noncomputable def fixedLeftArchimedeanBoundData :
    TS305.Goldbach.FixedLeftArchimedeanBoundData where
  constant := fixedLeftArchimedeanConstant
  constant_nonnegative := fixedLeftArchimedeanConstant_nonnegative
  norm_le := zetaLeftReflectionCorrection_norm_le_logWeight

/-- Complete fixed-left logarithmic derivative data with no external input. -/
noncomputable def fixedLeftLogDerivativeBoundData :
    TS305.Goldbach.FixedLeftLogDerivativeBoundData :=
  fixedLeftArchimedeanBoundData.toLogDerivativeBoundData

/-- Unconditional fixed-left side bound routed into TS298. -/
noncomputable def fixedLeftSideBoundData
    (x T : Nat)
    (hT : 1 <= T) :
    TS298.Goldbach.FixedLeftSideBoundData x T hT :=
  TS305.Goldbach.fixedLeftSideBoundData_of_archimedean
    x T hT fixedLeftArchimedeanBoundData

/-- Absolute integrability of the concrete fixed-left Perron integrand. -/
theorem fixedLeftIntegrand_integrable
    (x : Nat)
    (hx : 0 < x) :
    Integrable (TS305.Goldbach.fixedLeftIntegrand x) :=
  TS305.Goldbach.fixedLeftIntegrand_integrable
    x hx fixedLeftLogDerivativeBoundData

/-- The symmetric left truncations converge unconditionally to the fixed
improper vertical integral. -/
theorem fixedLeftBoundaryTruncation_tendsto
    (x : Nat)
    (hx : 0 < x) :
    Tendsto (TS305.Goldbach.fixedLeftBoundaryTruncation x) atTop
      (nhds (TS305.Goldbach.fixedLeftBoundaryLimit x)) :=
  TS305.Goldbach.fixedLeftBoundaryTruncation_tendsto
    x hx fixedLeftLogDerivativeBoundData

/-- Closed height-independent bound for the fixed-left improper limit. -/
theorem fixedLeftBoundaryLimit_norm_le
    (x : Nat) :
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
      TS305.Goldbach.fixedLeftUniformBound
        x fixedLeftLogDerivativeBoundData :=
  TS305.Goldbach.fixedLeftBoundaryLimit_norm_le
    x fixedLeftLogDerivativeBoundData

/-- The strong-height truncation error on the fixed left side vanishes. -/
theorem fixedLeftBoundaryResidual_strongHeight_tendsto_zero
    (x : Nat)
    (hx : 0 < x) :
    Tendsto
      (fun T : Nat =>
        TS305.Goldbach.fixedLeftBoundaryResidual x
          (TS296.Goldbach.strongHeightTau T))
      atTop (nhds 0) :=
  TS305.Goldbach.fixedLeftBoundaryResidual_strongHeight_tendsto_zero_of_archimedean
    x hx fixedLeftArchimedeanBoundData

/-! ## Audit ledger -/

structure FixedLeftArchimedeanRateLedger where
  gammaSeq_finite_logDerivative_identity_proved : True
  gammaSeq_locally_uniform_convergence_proved : True
  gamma_logDerivative_limit_proved : True
  harmonic_cutoff_bound_proved : True
  gamma_logarithmic_rate_proved : True
  tangent_unit_norm_proved : True
  reflection_correction_identity_proved : True
  fixedLeft_archimedean_input_discharged : True
  fixedLeft_integrability_unconditional : True
  fixedLeft_truncation_convergence_unconditional : True
  ts298_fixedLeft_routing_unconditional : True
  binet_not_used : True
  stirling_not_used : True
  weierstrass_product_not_used : True
  sharp_left_tail_rate_not_proved : True
  exhaustive_singularity_classification_not_proved : True
  perron_inversion_not_proved : True
  meromorphic_rectangle_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def fixedLeftArchimedeanRateLedger : FixedLeftArchimedeanRateLedger where
  gammaSeq_finite_logDerivative_identity_proved := True.intro
  gammaSeq_locally_uniform_convergence_proved := True.intro
  gamma_logDerivative_limit_proved := True.intro
  harmonic_cutoff_bound_proved := True.intro
  gamma_logarithmic_rate_proved := True.intro
  tangent_unit_norm_proved := True.intro
  reflection_correction_identity_proved := True.intro
  fixedLeft_archimedean_input_discharged := True.intro
  fixedLeft_integrability_unconditional := True.intro
  fixedLeft_truncation_convergence_unconditional := True.intro
  ts298_fixedLeft_routing_unconditional := True.intro
  binet_not_used := True.intro
  stirling_not_used := True.intro
  weierstrass_product_not_used := True.intro
  sharp_left_tail_rate_not_proved := True.intro
  exhaustive_singularity_classification_not_proved := True.intro
  perron_inversion_not_proved := True.intro
  meromorphic_rectangle_residue_theorem_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS307
