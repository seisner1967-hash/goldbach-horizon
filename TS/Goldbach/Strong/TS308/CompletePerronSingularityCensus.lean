import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic
import TS.Goldbach.Strong.TS307.FixedLeftArchimedeanLogarithmicRate

noncomputable section

namespace TS308
namespace Goldbach

open Complex Filter Metric Set
open scoped BigOperators

/-!
# TS308: Complete Perron Singularity Census

This module closes the local and finite singularity accounting for the fixed
Perron rectangle.  It proves regularity away from `1`, zeta zeros, `0`, and
`-1`; constructs exact local residue data at the main pole and every concrete
nontrivial zero; reuses the exceptional inventory `{0, -1}` from TS306; and
packages the resulting finite census with exact residue accounting.

The main residue is `(x : Complex) / 2`.  A zero `rho` contributes exactly
`-TS292.Goldbach.infiniteZeroSpectralTerm x rho`, so the finite spectral sum
is definitionally aligned with `TS293.Goldbach.realHeightZeroContribution`.

No global meromorphic rectangle theorem, Perron inversion, infinite explicit
formula, Gallagher estimate, OTSA statement, or Goldbach claim is proved.
-/

/-! ## Regular points and exceptional completeness -/

theorem triangleSplinePerronIntegrand_analyticAt_of_regular
    (x : Nat)
    (hx : 0 < x)
    {p : Complex}
    (hpOne : Not (p = 1))
    (hpZeta : Not (riemannZeta p = 0))
    (hpZero : Not (p = 0))
    (hpNegOne : Not (p = -1)) :
    AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x) p := by
  have hLog : AnalyticAt Complex TS306.Goldbach.negZetaLogDerivative p :=
    TS306.Goldbach.negZetaLogDerivative_analyticAt hpOne hpZeta
  have hPow : AnalyticAt Complex (fun z : Complex => (x : Complex) ^ z) p :=
    TS306.Goldbach.natCpow_analyticAt hx p
  have hDen : Not (p * (p + 1) = 0) := by
    exact mul_ne_zero hpZero (by
      intro h
      apply hpNegOne
      linear_combination h)
  change AnalyticAt Complex
    (fun s => TS306.Goldbach.negZetaLogDerivative s *
      (x : Complex) ^ s *
        TS257.Goldbach.triangleSplineMellinKernel s) p
  unfold TS257.Goldbach.triangleSplineMellinKernel
  exact (hLog.mul hPow).mul
    (analyticAt_const.div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) hDen)

theorem concreteExceptionalResidueInventory_complete
    (x : Nat)
    (hx : 0 < x)
    (D : TS293.Goldbach.PerronRectangle) :
    TS306.Goldbach.ExceptionalInventoryCompletenessStatement x D
      (TS306.Goldbach.concreteExceptionalResidueInventory x hx D) := by
  intro p hpLeft hpRight hpBottom hpTop hpOne hpZeta hpNotAnalytic
  by_contra hpMem
  have hpCases : Not (p = 0) /\ Not (p = -1) := by
    simpa [TS306.Goldbach.concreteExceptionalResidueInventory,
      TS306.Goldbach.perronExceptionalPoles] using hpMem
  exact hpNotAnalytic
    (triangleSplinePerronIntegrand_analyticAt_of_regular
      x hx hpOne hpZeta hpCases.1 hpCases.2)

/-! ## Zeta zeros in the fixed rectangle -/

theorem zeta_zero_in_fixed_open_rectangle_is_concrete
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    {p : Complex}
    (hpLeft : D.left < p.re)
    (hpRight : p.re < D.right)
    (hpZero : riemannZeta p = 0) :
    TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet p := by
  have hFixedLeft : TS294.Goldbach.fixedPerronLeft < p.re := by
    rwa [D.left_eq_fixed] at hpLeft
  have hFixedRight : p.re < TS294.Goldbach.fixedPerronRight := by
    rwa [D.right_eq_fixed] at hpRight
  have hpNotNegNat : forall n : Nat, Not (p = -(n : Complex)) := by
    intro n hpEq
    have hpRe := congrArg Complex.re hpEq
    simp at hpRe
    have hnLt : (n : Real) < 3 / 2 := by
      norm_num [TS294.Goldbach.fixedPerronLeft] at hFixedLeft
      linarith
    have hnLtTwo : n < 2 := by
      exact_mod_cast (hnLt.trans (by norm_num : (3 / 2 : Real) < 2))
    interval_cases n
    next =>
      apply TS306.Goldbach.riemannZeta_zero_ne_zero
      simpa [hpEq] using hpZero
    next =>
      apply TS306.Goldbach.riemannZeta_neg_one_ne_zero
      simpa [hpEq] using hpZero
  have hpReLtOne : p.re < 1 := by
    by_contra h
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h)) hpZero
  have hpRePos : 0 < p.re := by
    by_contra h
    have hOneSubRe : 1 <= (1 - p).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hOneSubNe : Not (riemannZeta (1 - p) = 0) :=
      riemannZeta_ne_zero_of_one_le_re hOneSubRe
    have hpNeOne : Not (p = 1) := by
      intro hp
      subst p
      norm_num at hpReLtOne
    apply hOneSubNe
    rw [riemannZeta_one_sub hpNotNegNat hpNeOne, hpZero]
    simp
  exact And.intro
    (by
      simpa [TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet,
        TS185.Goldbach.nontrivialRiemannZetaZeroPredicate,
        TS185.Goldbach.riemannZetaZeroPredicate,
        TS185.Goldbach.mathlibRiemannZetaFunction] using hpZero)
    (by
      unfold TS185.Goldbach.criticalStripPredicate
      exact And.intro hpRePos hpReLtOne)

/-! ## Local certificate at the main pole -/

/-- The zeta pole at one with its removable singularity filled by its
residue. -/
noncomputable def zetaPoleRemoved (z : Complex) : Complex :=
  Function.update (fun w : Complex => (w - 1) * riemannZeta w) 1 1 z

theorem zetaPoleRemoved_apply_one : zetaPoleRemoved 1 = 1 := by
  simp [zetaPoleRemoved]

theorem zetaPoleRemoved_analyticAt_one :
    AnalyticAt Complex zetaPoleRemoved 1 := by
  change AnalyticAt Complex
    (Function.update (fun w : Complex => (w - 1) * riemannZeta w) 1 1) 1
  refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  next =>
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzNe : Not (z = 1) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    have hEventually :
        Filter.EventuallyEq (nhds z)
          (Function.update (fun w : Complex => (w - 1) * riemannZeta w) 1 1)
          (fun w => (w - 1) * riemannZeta w) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hzNe] with w hw
      rw [Function.update_of_ne]
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw
    exact hEventually.differentiableAt_iff.mpr
      ((differentiableAt_id.sub (differentiableAt_const 1)).mul
        (differentiableAt_riemannZeta hzNe))
  next =>
    simpa only [continuousAt_update_same] using
      riemannZeta_residue_one

theorem zetaPoleRemoved_ne_zero_at_one :
    Not (zetaPoleRemoved 1 = 0) := by
  rw [zetaPoleRemoved_apply_one]
  norm_num

theorem zetaPoleRemoved_eventuallyEq_mul
    {z : Complex}
    (hz : Not (z = 1)) :
    Filter.EventuallyEq (nhds z) zetaPoleRemoved
      (fun w => (w - 1) * riemannZeta w) := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
  rw [zetaPoleRemoved, Function.update_of_ne]
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw

theorem zetaPoleRemoved_logDeriv_eq
    {z : Complex}
    (hz : Not (z = 1))
    (hzeta : Not (riemannZeta z = 0)) :
    logDeriv zetaPoleRemoved z =
      1 / (z - 1) + logDeriv riemannZeta z := by
  have hEventually := zetaPoleRemoved_eventuallyEq_mul hz
  have hPoint := hEventually.eq_of_nhds
  have hDeriv := Filter.EventuallyEq.deriv_eq hEventually
  have hLinear : Not (z - 1 = 0) := sub_ne_zero.mpr hz
  have hLinearDiff : DifferentiableAt Complex (fun w : Complex => w - 1) z :=
    differentiableAt_id.sub (differentiableAt_const 1)
  have hZetaDiff : DifferentiableAt Complex riemannZeta z :=
    differentiableAt_riemannZeta hz
  have hMul := logDeriv_mul z hLinear hzeta hLinearDiff hZetaDiff
  have hLogEq :
      logDeriv zetaPoleRemoved z =
        logDeriv (fun w => (w - 1) * riemannZeta w) z := by
    simp only [logDeriv_apply]
    rw [hDeriv, hPoint]
  calc
    logDeriv zetaPoleRemoved z =
        logDeriv (fun w => (w - 1) * riemannZeta w) z := hLogEq
    _ = logDeriv (fun w : Complex => w - 1) z +
        logDeriv riemannZeta z := hMul
    _ = 1 / (z - 1) + logDeriv riemannZeta z := by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'']

/-- The analytic Mellin-scale factor multiplying the zeta logarithmic
derivative. -/
noncomputable def perronAnalyticFactor
    (x : Nat)
    (z : Complex) : Complex :=
  (x : Complex) ^ z * TS257.Goldbach.triangleSplineMellinKernel z

theorem perronAnalyticFactor_analyticAt
    (x : Nat)
    (hx : 0 < x)
    {p : Complex}
    (hpZero : Not (p = 0))
    (hpNegOne : Not (p = -1)) :
    AnalyticAt Complex (perronAnalyticFactor x) p := by
  have hDen : Not (p * (p + 1) = 0) := by
    exact mul_ne_zero hpZero (by
      intro h
      apply hpNegOne
      linear_combination h)
  unfold perronAnalyticFactor TS257.Goldbach.triangleSplineMellinKernel
  exact (TS306.Goldbach.natCpow_analyticAt hx p).mul
    (analyticAt_const.div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) hDen)

theorem perronAnalyticFactor_one
    (x : Nat) :
    perronAnalyticFactor x 1 = (x : Complex) / 2 := by
  unfold perronAnalyticFactor TS257.Goldbach.triangleSplineMellinKernel
  simp
  ring

/-- Analytic numerator after the zeta pole at one has been extracted. -/
noncomputable def mainPoleNumerator
    (x : Nat)
    (z : Complex) : Complex :=
  perronAnalyticFactor x z -
    (z - 1) * logDeriv zetaPoleRemoved z * perronAnalyticFactor x z

theorem logDeriv_zetaPoleRemoved_analyticAt_one :
    AnalyticAt Complex (logDeriv zetaPoleRemoved) 1 := by
  unfold logDeriv
  have hExists :=
    zetaPoleRemoved_analyticAt_one.exists_mem_nhds_analyticOnNhd
  let U := Classical.choose hExists
  have hUData := Classical.choose_spec hExists
  have hU := hUData.1
  have hAnalytic := hUData.2
  have hOneU : Membership.mem U (1 : Complex) := mem_of_mem_nhds hU
  exact (hAnalytic.deriv 1 hOneU).div
    (hAnalytic 1 hOneU) zetaPoleRemoved_ne_zero_at_one

theorem mainPoleNumerator_analyticAt
    (x : Nat)
    (hx : 0 < x) :
    AnalyticAt Complex (mainPoleNumerator x) 1 := by
  have hFactor := perronAnalyticFactor_analyticAt x hx
    (by norm_num : Not ((1 : Complex) = 0))
    (by norm_num : Not ((1 : Complex) = -1))
  unfold mainPoleNumerator
  exact hFactor.sub
    (((analyticAt_id.sub analyticAt_const).mul
      logDeriv_zetaPoleRemoved_analyticAt_one).mul hFactor)

theorem triangleSplinePerronIntegrand_eq_mainPoleNumerator_div
    (x : Nat) :
    Filter.Eventually
      (fun z =>
        TS293.Goldbach.triangleSplinePerronIntegrand x z =
          mainPoleNumerator x z / (z - 1))
      (nhdsWithin (1 : Complex) (Set.compl {1})) := by
  filter_upwards [self_mem_nhdsWithin,
    TS265.Goldbach.riemannZeta_eventually_ne_zero_nhdsWithin_one]
      with z hz hzeta
  have hzOne : Not (z = 1) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
  have hRemoved := zetaPoleRemoved_logDeriv_eq hzOne hzeta
  simp only [logDeriv_apply] at hRemoved
  change TS306.Goldbach.negZetaLogDerivative z *
      (x : Complex) ^ z *
        TS257.Goldbach.triangleSplineMellinKernel z =
    mainPoleNumerator x z / (z - 1)
  unfold TS306.Goldbach.negZetaLogDerivative mainPoleNumerator
    perronAnalyticFactor
  simp only [logDeriv_apply]
  rw [hRemoved]
  field_simp [sub_ne_zero.mpr hzOne]
  ring

/-- Certified principal part at the main pole, with residue `x/2`. -/
noncomputable def mainPerronLocalResidueData
    (x : Nat)
    (hx : 0 < x) :
    TS293.Goldbach.PerronLocalResidueData x 1 :=
  TS306.Goldbach.localSimplePoleData_of_analytic
    x 1 (mainPoleNumerator x) (mainPoleNumerator_analyticAt x hx)
    (triangleSplinePerronIntegrand_eq_mainPoleNumerator_div x)

theorem mainPerronLocalResidueData_residue
    (x : Nat)
    (hx : 0 < x) :
    (mainPerronLocalResidueData x hx).residue = (x : Complex) / 2 := by
  simp [mainPerronLocalResidueData,
    TS306.Goldbach.localSimplePoleData_of_analytic,
    mainPoleNumerator, perronAnalyticFactor_one]

/-! ## Local certificates at concrete nontrivial zeros -/

theorem concreteZeroMultiplicity_eq_zeta_order
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    TS260.Goldbach.riemannZetaVanishingOrderAt rho.1
        (TS264.Goldbach.concreteZero_ne_one rho.property) =
      (TS295.Goldbach.concreteZeroMultiplicity rho : ENat) := by
  symm
  simpa [TS295.Goldbach.concreteZeroMultiplicity,
    TS264.Goldbach.concreteRiemannZetaZeroFamilyContract,
    TS260.Goldbach.riemannZetaVanishingOrderAt] using
      TS264.Goldbach.concreteRiemannZetaMultiplicity_coe_eq_order
        rho.property

theorem zetaZeroRegularFactor_exists
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Exists fun g : Complex -> Complex =>
      AnalyticAt Complex g rho.1 /\
        Not (g rho.1 = 0) /\
          Filter.Eventually
            (fun z => riemannZeta z =
              (z - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho *
                g z)
            (nhds rho.1) := by
  exact
    (TS260.Goldbach.riemannZetaVanishingOrderAt_eq_nat_iff
      rho.1 (TS264.Goldbach.concreteZero_ne_one rho.property)
      (TS295.Goldbach.concreteZeroMultiplicity rho)).mp
        (concreteZeroMultiplicity_eq_zeta_order rho)

/-- The nonzero analytic factor after removing the exact finite-order zeta
zero at `rho`. -/
noncomputable def zetaZeroRegularFactor
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Complex -> Complex :=
  Classical.choose (zetaZeroRegularFactor_exists rho)

theorem zetaZeroRegularFactor_analyticAt
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    AnalyticAt Complex (zetaZeroRegularFactor rho) rho.1 :=
  (Classical.choose_spec (zetaZeroRegularFactor_exists rho)).1

theorem zetaZeroRegularFactor_ne_zero
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Not (zetaZeroRegularFactor rho rho.1 = 0) :=
  (Classical.choose_spec (zetaZeroRegularFactor_exists rho)).2.1

theorem zetaZeroRegularFactor_eventually_factorization
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Filter.Eventually
      (fun z => riemannZeta z =
        (z - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho *
          zetaZeroRegularFactor rho z)
      (nhds rho.1) :=
  (Classical.choose_spec (zetaZeroRegularFactor_exists rho)).2.2

theorem logDeriv_analyticAt_of_analyticAt_ne_zero
    {f : Complex -> Complex}
    {p : Complex}
    (hf : AnalyticAt Complex f p)
    (hfp : Not (f p = 0)) :
    AnalyticAt Complex (logDeriv f) p := by
  unfold logDeriv
  have hExists := hf.exists_mem_nhds_analyticOnNhd
  let U := Classical.choose hExists
  have hUData := Classical.choose_spec hExists
  have hU := hUData.1
  have hAnalytic := hUData.2
  have hpU : Membership.mem U p := mem_of_mem_nhds hU
  exact (hAnalytic.deriv p hpU).div (hAnalytic p hpU) hfp

theorem zetaZeroRegularFactor_logDeriv_analyticAt
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    AnalyticAt Complex (logDeriv (zetaZeroRegularFactor rho)) rho.1 :=
  logDeriv_analyticAt_of_analyticAt_ne_zero
    (zetaZeroRegularFactor_analyticAt rho)
    (zetaZeroRegularFactor_ne_zero rho)

theorem riemannZeta_logDeriv_eventually_eq_zero_principal_part
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Filter.Eventually
      (fun z =>
        logDeriv riemannZeta z =
          (TS295.Goldbach.concreteZeroMultiplicity rho : Complex) /
              (z - rho.1) +
            logDeriv (zetaZeroRegularFactor rho) z)
      (nhdsWithin rho.1 (Set.compl {rho.1})) := by
  have hFactor := zetaZeroRegularFactor_eventually_factorization rho
  have hExists := _root_.mem_nhds_iff.mp hFactor
  let U := Classical.choose hExists
  have hUData := Classical.choose_spec hExists
  have hUSub := hUData.1
  have hUOpen := hUData.2.1
  have hRhoU := hUData.2.2
  have hUMem : Membership.mem
      (nhdsWithin rho.1 (Set.compl {rho.1})) U :=
    mem_nhdsWithin_of_mem_nhds (hUOpen.mem_nhds hRhoU)
  have hAnalyticMem : Filter.Eventually
      (fun z => AnalyticAt Complex (zetaZeroRegularFactor rho) z)
      (nhdsWithin rho.1 (Set.compl {rho.1})) :=
    Filter.Eventually.filter_mono
      (show nhdsWithin rho.1 (Set.compl {rho.1}) <= nhds rho.1 from
        nhdsWithin_le_nhds)
      (zetaZeroRegularFactor_analyticAt rho).eventually_analyticAt
  have hNonzeroMem : Filter.Eventually
      (fun z => Not (zetaZeroRegularFactor rho z = 0))
      (nhdsWithin rho.1 (Set.compl {rho.1})) :=
    Filter.Eventually.filter_mono
      (show nhdsWithin rho.1 (Set.compl {rho.1}) <= nhds rho.1 from
        nhdsWithin_le_nhds)
      ((zetaZeroRegularFactor_analyticAt rho).continuousAt.eventually_ne
        (zetaZeroRegularFactor_ne_zero rho))
  filter_upwards [hUMem, hAnalyticMem, hNonzeroMem,
    self_mem_nhdsWithin] with z hzU hzAnalytic hzGNe hzComp
  have hzNe : Not (z = rho.1) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzComp
  have hEqNhd :
      Filter.EventuallyEq (nhds z) riemannZeta
        (fun w =>
          (w - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho *
            zetaZeroRegularFactor rho w) := by
    filter_upwards [hUOpen.mem_nhds hzU] with w hw
    exact hUSub hw
  have hPoint := hEqNhd.eq_of_nhds
  have hDeriv := Filter.EventuallyEq.deriv_eq hEqNhd
  have hLinearNe : Not (z - rho.1 = 0) := sub_ne_zero.mpr hzNe
  have hPowNe : Not
      ((z - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho = 0) :=
    pow_ne_zero _ hLinearNe
  have hLinearDiff :
      DifferentiableAt Complex (fun w : Complex => w - rho.1) z :=
    differentiableAt_id.sub (differentiableAt_const rho.1)
  have hPowDiff : DifferentiableAt Complex
      (fun w : Complex =>
        (w - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho) z :=
    hLinearDiff.pow _
  have hLogEq :
      logDeriv riemannZeta z =
        logDeriv
          (fun w =>
            (w - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho *
              zetaZeroRegularFactor rho w) z := by
    simp only [logDeriv_apply]
    rw [hDeriv, hPoint]
  calc
    logDeriv riemannZeta z =
        logDeriv
          (fun w =>
            (w - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho *
              zetaZeroRegularFactor rho w) z := hLogEq
    _ = logDeriv
          (fun w : Complex =>
            (w - rho.1) ^ TS295.Goldbach.concreteZeroMultiplicity rho) z +
        logDeriv (zetaZeroRegularFactor rho) z :=
      logDeriv_mul z hPowNe hzGNe hPowDiff hzAnalytic.differentiableAt
    _ = (TS295.Goldbach.concreteZeroMultiplicity rho : Complex) /
          (z - rho.1) + logDeriv (zetaZeroRegularFactor rho) z := by
      rw [logDeriv_fun_pow hLinearDiff]
      simp only [logDeriv_apply, deriv_sub_const, deriv_id'']
      ring

/-- Analytic numerator after the exact principal part at `rho` has been
extracted from the zeta logarithmic derivative. -/
noncomputable def zeroPoleNumerator
    (x : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (z : Complex) : Complex :=
  -(TS295.Goldbach.concreteZeroMultiplicity rho : Complex) *
      perronAnalyticFactor x z -
    (z - rho.1) * logDeriv (zetaZeroRegularFactor rho) z *
      perronAnalyticFactor x z

theorem concreteZero_ne_zero
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Not (rho.1 = 0) := by
  intro h
  have hPos := rho.property.2.1
  rw [h] at hPos
  norm_num at hPos

theorem concreteZero_ne_neg_one
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Not (rho.1 = -1) := by
  intro h
  have hPos := rho.property.2.1
  rw [h] at hPos
  norm_num at hPos

theorem zeroPoleNumerator_analyticAt
    (x : Nat)
    (hx : 0 < x)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    AnalyticAt Complex (zeroPoleNumerator x rho) rho.1 := by
  have hFactor := perronAnalyticFactor_analyticAt x hx
    (concreteZero_ne_zero rho) (concreteZero_ne_neg_one rho)
  unfold zeroPoleNumerator
  exact (analyticAt_const.mul hFactor).sub
    (((analyticAt_id.sub analyticAt_const).mul
      (zetaZeroRegularFactor_logDeriv_analyticAt rho)).mul hFactor)

theorem triangleSplinePerronIntegrand_eq_zeroPoleNumerator_div
    (x : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Filter.Eventually
      (fun z =>
        TS293.Goldbach.triangleSplinePerronIntegrand x z =
          zeroPoleNumerator x rho z / (z - rho.1))
      (nhdsWithin rho.1 (Set.compl {rho.1})) := by
  filter_upwards
    [riemannZeta_logDeriv_eventually_eq_zero_principal_part rho,
      self_mem_nhdsWithin] with z hLog hzComp
  have hzNe : Not (z = rho.1) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzComp
  change TS306.Goldbach.negZetaLogDerivative z *
      (x : Complex) ^ z *
        TS257.Goldbach.triangleSplineMellinKernel z =
    zeroPoleNumerator x rho z / (z - rho.1)
  unfold TS306.Goldbach.negZetaLogDerivative zeroPoleNumerator
    perronAnalyticFactor
  simp only [logDeriv_apply] at hLog
  simp only [logDeriv_apply]
  rw [neg_div, hLog]
  field_simp [sub_ne_zero.mpr hzNe]
  ring

/-- Certified principal part at one concrete nontrivial zero. -/
noncomputable def zeroPerronLocalResidueData
    (x : Nat)
    (hx : 0 < x)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    TS293.Goldbach.PerronLocalResidueData x rho.1 :=
  TS306.Goldbach.localSimplePoleData_of_analytic
    x rho.1 (zeroPoleNumerator x rho)
      (zeroPoleNumerator_analyticAt x hx rho)
      (triangleSplinePerronIntegrand_eq_zeroPoleNumerator_div x rho)

theorem zeroPerronLocalResidueData_residue
    (x : Nat)
    (hx : 0 < x)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    (zeroPerronLocalResidueData x hx rho).residue =
      -TS292.Goldbach.infiniteZeroSpectralTerm x rho := by
  change zeroPoleNumerator x rho rho.1 =
    -TS292.Goldbach.infiniteZeroSpectralTerm x rho
  unfold zeroPoleNumerator
  simp only [sub_self, zero_mul, sub_zero]
  unfold perronAnalyticFactor
    TS257.Goldbach.triangleSplineMellinKernel
    TS292.Goldbach.infiniteZeroSpectralTerm
    TS266.Goldbach.concreteFiniteHeightZeroTerm
    TS257.Goldbach.triangleSplineZeroSpectralSummand
    TS295.Goldbach.concreteZeroMultiplicity
  simp only [div_eq_mul_inv]
  ring

/-! ## Finite census geometry -/

/-- Complex values underlying the real-height zero truncation. -/
noncomputable def realHeightZeroValues
    (tau : Real) : Finset Complex :=
  (TS293.Goldbach.concreteZerosUpToRealHeight tau).image Subtype.val

theorem mem_realHeightZeroValues_iff
    (tau : Real)
    (p : Complex) :
    Membership.mem (realHeightZeroValues tau) p <->
      Exists fun rho : TS292.Goldbach.ConcreteNontrivialZero =>
        Membership.mem (TS293.Goldbach.concreteZerosUpToRealHeight tau) rho /\
          rho.1 = p := by
  classical
  simp [realHeightZeroValues]

/-- The complete finite candidate set for the Perron rectangle. -/
noncomputable def completePerronPoleValues
    (tau : Real) : Finset Complex :=
  insert 1 (insert 0 (insert (-1) (realHeightZeroValues tau)))

def StrictlyInsidePerronRectangle
    (D : TS293.Goldbach.PerronRectangle)
    (p : Complex) : Prop :=
  D.left < p.re /\ p.re < D.right /\
    -D.tau < p.im /\ p.im < D.tau

theorem one_not_mem_realHeightZeroValues
    (tau : Real) :
    Not (Membership.mem (realHeightZeroValues tau) (1 : Complex)) := by
  intro h
  have hExists := (mem_realHeightZeroValues_iff tau 1).mp h
  let rho := Classical.choose hExists
  have hRhoData := Classical.choose_spec hExists
  have hrho := hRhoData.1
  have hValue := hRhoData.2
  have hLt := rho.property.2.2
  rw [hValue] at hLt
  norm_num at hLt

theorem exceptionalPoles_disjoint_realHeightZeroValues
    (tau : Real) :
    Disjoint TS306.Goldbach.perronExceptionalPoles
      (realHeightZeroValues tau) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpExceptional hpZero
  have hExists := (mem_realHeightZeroValues_iff tau p).mp hpZero
  let rho := Classical.choose hExists
  have hRhoData := Classical.choose_spec hExists
  have hrho := hRhoData.1
  have hValue := hRhoData.2
  have hPos := rho.property.2.1
  simp only [TS306.Goldbach.perronExceptionalPoles,
    Finset.mem_insert, Finset.mem_singleton] at hpExceptional
  rcases hpExceptional with hpZeroValue | hpNegOneValue
  next =>
    rw [hValue, hpZeroValue] at hPos
    norm_num at hPos
  next =>
    rw [hValue, hpNegOneValue] at hPos
    norm_num at hPos

theorem mainPole_strictlyInside
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) :
    StrictlyInsidePerronRectangle D.toPerronRectangle 1 := by
  unfold StrictlyInsidePerronRectangle
  constructor
  next => exact lt_trans D.left_lt_neg_one (by norm_num)
  constructor
  next => exact D.one_lt_right
  constructor <;> simp [D.tau_pos]

theorem concreteZero_strictlyInside
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hrho : Membership.mem
      (TS293.Goldbach.concreteZerosUpToRealHeight D.tau) rho) :
    StrictlyInsidePerronRectangle D.toPerronRectangle rho.1 := by
  have hAbs :=
    (TS293.Goldbach.mem_concreteZerosUpToRealHeight_iff D.tau rho).mp hrho
  have hLeft : D.left < rho.1.re := by
    rw [D.left_eq_fixed]
    norm_num [TS294.Goldbach.fixedPerronLeft]
    linarith [rho.property.2.1]
  have hRight : rho.1.re < D.right := by
    rw [D.right_eq_fixed]
    norm_num [TS294.Goldbach.fixedPerronRight]
    linarith [rho.property.2.2]
  have hLowerLe : -D.tau <= rho.1.im := neg_le_of_abs_le hAbs
  have hUpperLe : rho.1.im <= D.tau := le_of_abs_le hAbs
  have hLowerNe : Not (-D.tau = rho.1.im) := by
    intro hEq
    have hPoint :
        ((rho.1.re : Complex) - (D.tau : Complex) * I) = rho.1 := by
      apply Complex.ext
      next => simp
      next => simp [hEq]
    exact D.zeta_nonzero_on_bottom rho.1.re
      (le_of_lt hLeft) (le_of_lt hRight) (by
        rw [hPoint]
        exact rho.property.1)
  have hUpperNe : Not (rho.1.im = D.tau) := by
    intro hEq
    have hPoint :
        ((rho.1.re : Complex) + (D.tau : Complex) * I) = rho.1 := by
      apply Complex.ext
      next => simp
      next => simp [hEq]
    exact D.zeta_nonzero_on_top rho.1.re
      (le_of_lt hLeft) (le_of_lt hRight) (by
        rw [hPoint]
        exact rho.property.1)
  unfold StrictlyInsidePerronRectangle
  exact And.intro hLeft (And.intro hRight
    (And.intro (lt_of_le_of_ne hLowerLe hLowerNe)
      (lt_of_le_of_ne hUpperLe hUpperNe)))

theorem exceptionalPole_strictlyInside
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    {p : Complex}
    (hp : Membership.mem TS306.Goldbach.perronExceptionalPoles p) :
    StrictlyInsidePerronRectangle D.toPerronRectangle p := by
  simp only [TS306.Goldbach.perronExceptionalPoles,
    Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  next =>
    unfold StrictlyInsidePerronRectangle
    constructor
    next => norm_num; linarith [D.left_lt_neg_one]
    constructor
    next => norm_num; linarith [D.one_lt_right]
    constructor <;> simp [D.tau_pos]
  next =>
    unfold StrictlyInsidePerronRectangle
    constructor
    next => exact D.left_lt_neg_one
    constructor
    next => norm_num; linarith [D.one_lt_right]
    constructor <;> simp [D.tau_pos]

theorem completePerronPoleValues_strictlyInside
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    {p : Complex}
    (hp : Membership.mem (completePerronPoleValues D.tau) p) :
    StrictlyInsidePerronRectangle D.toPerronRectangle p := by
  classical
  simp only [completePerronPoleValues, Finset.mem_insert] at hp
  rcases hp with hpOne | hpZero | hpNegOne | hpSpectral
  next =>
    rw [hpOne]
    exact mainPole_strictlyInside D
  next =>
    exact exceptionalPole_strictlyInside D (by
      simp [TS306.Goldbach.perronExceptionalPoles, hpZero])
  next =>
    exact exceptionalPole_strictlyInside D (by
      simp [TS306.Goldbach.perronExceptionalPoles, hpNegOne])
  next =>
    have hExists :=
      (mem_realHeightZeroValues_iff D.tau p).mp hpSpectral
    let rho := Classical.choose hExists
    have hRhoData := Classical.choose_spec hExists
    have hrho := hRhoData.1
    have hValue := hRhoData.2
    rw [hValue.symm]
    exact concreteZero_strictlyInside D rho hrho

/-- Every point strictly inside the clean rectangle and outside the finite
census is regular for the Perron integrand. -/
theorem triangleSplinePerronIntegrand_analyticAt_of_not_mem_census
    {T : Nat}
    (x : Nat)
    (hx : 0 < x)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    {p : Complex}
    (hpInside : StrictlyInsidePerronRectangle D.toPerronRectangle p)
    (hpNotMem : Not
      (Membership.mem (completePerronPoleValues D.tau) p)) :
    AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x) p := by
  have hpOne : Not (p = 1) := by
    intro h
    apply hpNotMem
    simp [completePerronPoleValues, h]
  have hpZero : Not (p = 0) := by
    intro h
    apply hpNotMem
    simp [completePerronPoleValues, h]
  have hpNegOne : Not (p = -1) := by
    intro h
    apply hpNotMem
    simp [completePerronPoleValues, h]
  have hpZeta : Not (riemannZeta p = 0) := by
    intro hZeta
    let rho : TS292.Goldbach.ConcreteNontrivialZero :=
      Subtype.mk p
        (zeta_zero_in_fixed_open_rectangle_is_concrete D
          hpInside.1 hpInside.2.1 hZeta)
    have hHeight : _root_.abs rho.1.im <= D.tau := by
      apply abs_le.mpr
      exact And.intro (le_of_lt hpInside.2.2.1)
        (le_of_lt hpInside.2.2.2)
    have hRhoMem : Membership.mem
        (TS293.Goldbach.concreteZerosUpToRealHeight D.tau) rho :=
      (TS293.Goldbach.mem_concreteZerosUpToRealHeight_iff D.tau rho).mpr
        hHeight
    have hValueMem : Membership.mem (realHeightZeroValues D.tau) p :=
      (mem_realHeightZeroValues_iff D.tau p).mpr
        (Exists.intro rho (And.intro hRhoMem rfl))
    apply hpNotMem
    simp [completePerronPoleValues, hValueMem]
  exact triangleSplinePerronIntegrand_analyticAt_of_regular
    x hx hpOne hpZeta hpZero hpNegOne

structure PerronBoundaryAnalyticData
    (x T : Nat)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) where
  bottom : forall sigma : Real, D.left <= sigma -> sigma <= D.right ->
    AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x)
      ((sigma : Complex) - (D.tau : Complex) * I)
  top : forall sigma : Real, D.left <= sigma -> sigma <= D.right ->
    AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x)
      ((sigma : Complex) + (D.tau : Complex) * I)
  left : forall t : Real, -D.tau <= t -> t <= D.tau ->
    AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x)
      ((D.left : Complex) + (t : Complex) * I)
  right : forall t : Real, -D.tau <= t -> t <= D.tau ->
    AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x)
      ((D.right : Complex) + (t : Complex) * I)

theorem nonreal_point_ne_zero_one_neg_one
    {p : Complex}
    (hpIm : Not (p.im = 0)) :
    Not (p = 0) /\ Not (p = 1) /\ Not (p = -1) := by
  constructor
  next =>
    intro h
    apply hpIm
    rw [h]
    simp
  constructor
  next =>
    intro h
    apply hpIm
    rw [h]
    simp
  next =>
    intro h
    apply hpIm
    rw [h]
    simp

noncomputable def canonicalPerronBoundaryAnalyticData
    (x T : Nat)
    (hx : 0 < x)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) :
    PerronBoundaryAnalyticData x T D where
  bottom := by
    intro sigma hLeft hRight
    let p : Complex :=
      (sigma : Complex) - (D.tau : Complex) * I
    have hpIm : Not (p.im = 0) := by
      unfold p
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one,
        mul_zero, sub_zero]
      linarith [D.tau_pos]
    have hpCases := nonreal_point_ne_zero_one_neg_one hpIm
    exact triangleSplinePerronIntegrand_analyticAt_of_regular x hx
      hpCases.2.1
      (D.zeta_nonzero_on_bottom sigma hLeft hRight)
      hpCases.1 hpCases.2.2
  top := by
    intro sigma hLeft hRight
    let p : Complex :=
      (sigma : Complex) + (D.tau : Complex) * I
    have hpIm : Not (p.im = 0) := by
      unfold p
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one,
        mul_zero, zero_add]
      simpa using (ne_of_gt D.tau_pos)
    have hpCases := nonreal_point_ne_zero_one_neg_one hpIm
    exact triangleSplinePerronIntegrand_analyticAt_of_regular x hx
      hpCases.2.1
      (D.zeta_nonzero_on_top sigma hLeft hRight)
      hpCases.1 hpCases.2.2
  left := by
    intro t hBottom hTop
    let p : Complex := (D.left : Complex) + (t : Complex) * I
    have hpRe : p.re = D.left := by
      unfold p
      simp
    have hpZero : Not (p = 0) := by
      intro h
      have := congrArg Complex.re h
      rw [hpRe] at this
      norm_num at this
      linarith [D.left_lt_neg_one]
    have hpOne : Not (p = 1) := by
      intro h
      have := congrArg Complex.re h
      rw [hpRe] at this
      norm_num at this
      linarith [D.left_lt_neg_one]
    have hpNegOne : Not (p = -1) := by
      intro h
      have := congrArg Complex.re h
      rw [hpRe] at this
      norm_num at this
      linarith [D.left_lt_neg_one]
    exact triangleSplinePerronIntegrand_analyticAt_of_regular x hx hpOne
      (D.zeta_nonzero_on_left t hBottom hTop) hpZero hpNegOne
  right := by
    intro t hBottom hTop
    let p : Complex := (D.right : Complex) + (t : Complex) * I
    have hpRe : p.re = D.right := by
      unfold p
      simp
    have hpZero : Not (p = 0) := by
      intro h
      have := congrArg Complex.re h
      rw [hpRe] at this
      norm_num at this
      linarith [D.one_lt_right]
    have hpOne : Not (p = 1) := by
      intro h
      have := congrArg Complex.re h
      rw [hpRe] at this
      norm_num at this
      linarith [D.one_lt_right]
    have hpNegOne : Not (p = -1) := by
      intro h
      have := congrArg Complex.re h
      rw [hpRe] at this
      norm_num at this
      linarith [D.one_lt_right]
    exact triangleSplinePerronIntegrand_analyticAt_of_regular x hx hpOne
      (TS293.Goldbach.riemannZeta_ne_zero_on_perron_right_line
        D.one_lt_right)
      hpZero hpNegOne

/-! ## Complete local residue census -/

theorem zeroResidueSum_eq_neg_realHeightZeroContribution
    (x : Nat)
    (hx : 0 < x)
    (tau : Real) :
    Finset.sum (TS293.Goldbach.concreteZerosUpToRealHeight tau)
        (fun rho => (zeroPerronLocalResidueData x hx rho).residue) =
      -TS293.Goldbach.realHeightZeroContribution x tau := by
  unfold TS293.Goldbach.realHeightZeroContribution
  calc
    Finset.sum (TS293.Goldbach.concreteZerosUpToRealHeight tau)
        (fun rho => (zeroPerronLocalResidueData x hx rho).residue) =
        Finset.sum (TS293.Goldbach.concreteZerosUpToRealHeight tau)
          (fun rho => -TS292.Goldbach.infiniteZeroSpectralTerm x rho) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact zeroPerronLocalResidueData_residue x hx rho
    _ = -Finset.sum (TS293.Goldbach.concreteZerosUpToRealHeight tau)
          (TS292.Goldbach.infiniteZeroSpectralTerm x) := by
      exact Finset.sum_neg_distrib

/-- All local data and all regularity facts needed by the future global
rectangle residue theorem.  This structure does not contain that theorem. -/
structure CompletePerronResidueCensus
    (x T : Nat)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) where
  poles : Finset Complex
  poles_eq : poles = completePerronPoleValues D.tau
  mainPole : TS293.Goldbach.PerronLocalResidueData x 1
  mainPole_residue : mainPole.residue = (x : Complex) / 2
  zeroPole : forall rho : TS292.Goldbach.ConcreteNontrivialZero,
    Membership.mem (TS293.Goldbach.concreteZerosUpToRealHeight D.tau) rho ->
      TS293.Goldbach.PerronLocalResidueData x rho.1
  zeroPole_residue : forall
      (rho : TS292.Goldbach.ConcreteNontrivialZero)
      (hrho : Membership.mem
        (TS293.Goldbach.concreteZerosUpToRealHeight D.tau) rho),
    (zeroPole rho hrho).residue =
      -TS292.Goldbach.infiniteZeroSpectralTerm x rho
  exceptional : TS306.Goldbach.MainTermSeparatedExceptionalInventory
    x D.toPerronRectangle
  exceptional_complete :
    TS306.Goldbach.ExceptionalInventoryCompletenessStatement x
      D.toPerronRectangle exceptional.inventory
  main_inside : StrictlyInsidePerronRectangle D.toPerronRectangle 1
  zeros_inside : forall
      (rho : TS292.Goldbach.ConcreteNontrivialZero)
      (_hrho : Membership.mem
        (TS293.Goldbach.concreteZerosUpToRealHeight D.tau) rho),
    StrictlyInsidePerronRectangle D.toPerronRectangle rho.1
  exceptional_inside : forall p : Complex,
    Membership.mem exceptional.inventory.poles p ->
      StrictlyInsidePerronRectangle D.toPerronRectangle p
  one_not_mem_zero_values :
    Not (Membership.mem (realHeightZeroValues D.tau) (1 : Complex))
  exceptional_disjoint_zero_values :
    Disjoint exceptional.inventory.poles (realHeightZeroValues D.tau)
  all_poles_inside : forall p : Complex,
    Membership.mem poles p ->
      StrictlyInsidePerronRectangle D.toPerronRectangle p
  regular_off_census : forall p : Complex,
    StrictlyInsidePerronRectangle D.toPerronRectangle p ->
      Not (Membership.mem poles p) ->
        AnalyticAt Complex
          (TS293.Goldbach.triangleSplinePerronIntegrand x) p
  boundary_analytic : PerronBoundaryAnalyticData x T D
  residue_accounting :
    mainPole.residue +
        Finset.sum
          (TS293.Goldbach.concreteZerosUpToRealHeight D.tau).attach
          (fun rho =>
            (zeroPole rho.1 rho.2).residue) +
        TS293.Goldbach.exceptionalResidueContribution exceptional.inventory =
      (x : Complex) / 2 -
        TS293.Goldbach.realHeightZeroContribution x D.tau +
          TS293.Goldbach.exceptionalResidueContribution exceptional.inventory

noncomputable def completePerronResidueCensus
    (x T : Nat)
    (hx : 0 < x)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) :
    CompletePerronResidueCensus x T D where
  poles := completePerronPoleValues D.tau
  poles_eq := rfl
  mainPole := mainPerronLocalResidueData x hx
  mainPole_residue := mainPerronLocalResidueData_residue x hx
  zeroPole := fun rho _hrho => zeroPerronLocalResidueData x hx rho
  zeroPole_residue := fun rho hrho =>
    zeroPerronLocalResidueData_residue x hx rho
  exceptional :=
    TS306.Goldbach.mainTermSeparatedExceptionalInventory
      x hx D.toPerronRectangle
  exceptional_complete :=
    concreteExceptionalResidueInventory_complete x hx D.toPerronRectangle
  main_inside := mainPole_strictlyInside D
  zeros_inside := fun rho hrho => concreteZero_strictlyInside D rho hrho
  exceptional_inside := by
    intro p hp
    exact exceptionalPole_strictlyInside D hp
  one_not_mem_zero_values := one_not_mem_realHeightZeroValues D.tau
  exceptional_disjoint_zero_values :=
    exceptionalPoles_disjoint_realHeightZeroValues D.tau
  all_poles_inside := by
    intro p hp
    exact completePerronPoleValues_strictlyInside D hp
  regular_off_census := by
    intro p hpInside hpNot
    exact triangleSplinePerronIntegrand_analyticAt_of_not_mem_census
      x hx D hpInside hpNot
  boundary_analytic := canonicalPerronBoundaryAnalyticData x T hx D
  residue_accounting := by
    rw [mainPerronLocalResidueData_residue x hx]
    have hZeroSum := zeroResidueSum_eq_neg_realHeightZeroContribution
      x hx D.tau
    have hAttach :
        Finset.sum
            (TS293.Goldbach.concreteZerosUpToRealHeight D.tau).attach
            (fun rho => (zeroPerronLocalResidueData x hx rho.1).residue) =
          Finset.sum
            (TS293.Goldbach.concreteZerosUpToRealHeight D.tau)
            (fun rho => (zeroPerronLocalResidueData x hx rho).residue) :=
      Finset.sum_attach
        (TS293.Goldbach.concreteZerosUpToRealHeight D.tau)
        (fun rho => (zeroPerronLocalResidueData x hx rho).residue)
    change (x : Complex) / 2 +
        Finset.sum
          (TS293.Goldbach.concreteZerosUpToRealHeight D.tau).attach
          (fun rho => (zeroPerronLocalResidueData x hx rho.1).residue) +
        TS293.Goldbach.exceptionalResidueContribution
          (TS306.Goldbach.concreteExceptionalResidueInventory
            x hx D.toPerronRectangle) = _
    rw [hAttach]
    rw [hZeroSum]
    simp only [TS306.Goldbach.mainTermSeparatedExceptionalInventory]
    ring

/-- Exact normalized residue sum exposed to the next sprint. -/
theorem completePerronResidueCensus_residue_accounting
    (x T : Nat)
    (hx : 0 < x)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) :
    let C := completePerronResidueCensus x T hx D
    C.mainPole.residue +
        Finset.sum
          (TS293.Goldbach.concreteZerosUpToRealHeight D.tau).attach
          (fun rho => (C.zeroPole rho.1 rho.2).residue) +
        TS293.Goldbach.exceptionalResidueContribution C.exceptional.inventory =
      (x : Complex) / 2 -
        TS293.Goldbach.realHeightZeroContribution x D.tau +
          TS293.Goldbach.exceptionalResidueContribution
            C.exceptional.inventory := by
  exact (completePerronResidueCensus x T hx D).residue_accounting

structure CompletePerronSingularityCensusLedger where
  regular_points_classified : True
  exceptional_inventory_complete : True
  main_pole_residue_certified : True
  nontrivial_zero_residues_certified : True
  finite_total_pole_set_constructed : True
  pole_families_disjoint : True
  all_poles_strictly_inside : True
  boundary_zero_free_and_analytic : True
  exact_residue_accounting : True
  global_rectangle_residue_theorem_not_proved : True
  perron_inversion_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def completePerronSingularityCensusLedger :
    CompletePerronSingularityCensusLedger where
  regular_points_classified := True.intro
  exceptional_inventory_complete := True.intro
  main_pole_residue_certified := True.intro
  nontrivial_zero_residues_certified := True.intro
  finite_total_pole_set_constructed := True.intro
  pole_families_disjoint := True.intro
  all_poles_strictly_inside := True.intro
  boundary_zero_free_and_analytic := True.intro
  exact_residue_accounting := True.intro
  global_rectangle_residue_theorem_not_proved := True.intro
  perron_inversion_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS308
