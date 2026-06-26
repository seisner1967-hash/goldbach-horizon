import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae
import TS.Goldbach.Strong.TS203.TruncatedHaarTransport
import TS.Goldbach.Strong.TS206.ExplicitFormulaEffectiveStatement

namespace TS207
namespace Goldbach

open MeasureTheory

/-!
# TS207 - Naive Haar Energy Divergence Obstruction

TS203 proved the truncated Haar transport identity `dx / x = du` on positive
finite intervals.  A tempting next step would be to send the lower endpoint to
`0+` for the squared triangle spline and hope to recover the TS198 Lebesgue
energy value `X / 3`.

This sprint proves that this naive Haar-energy path is obstructed.  Near zero,
the triangle spline satisfies `F(x / X) = 1 - x / X`, hence it is bounded below
by `1 / 2` on `0 < x <= X / 2`.  Therefore the Haar-weighted square
`F(x / X)^2 / x` dominates `1 / (4 * x)`, whose truncated integral grows like
`(1 / 4) * (log (X / 2) - log epsilon)`.

This does not contradict TS198: TS198 concerns the `dx` energy after the
critical-line Jacobian cancellation, while TS207 concerns the naive Haar
quantity with the additional singular factor `1 / x`.
-/

/-- Naive Haar-weighted square density for the triangle spline at scale `X`. -/
noncomputable def naiveTriangleSplineHaarEnergyDensity
    (X : Nat)
    (x : Real) :
    Real :=
  (TS42.MellinJackson.triangleSpline (x / (X : Real))) ^ 2 / x

/-- Naive truncated Haar energy over `[epsilon, X / 2]`. -/
noncomputable def naiveTriangleSplineHaarEnergyTruncated
    (X : Nat)
    (epsilon : Real) :
    Real :=
  intervalIntegral
    (fun x : Real => naiveTriangleSplineHaarEnergyDensity X x)
    epsilon
    ((X : Real) / 2)
    volume

/-- On the lower half of the positive scale, the scaled triangle spline is affine. -/
theorem triangleSpline_scaled_eq_one_sub_of_le_half
    (X : Nat)
    (hX : 0 < X)
    {x : Real}
    (hx0 : 0 <= x)
    (hx_half : x <= (X : Real) / 2) :
    TS42.MellinJackson.triangleSpline (x / (X : Real)) =
      1 - x / (X : Real) := by
  have hX_real : 0 < (X : Real) := by
    exact_mod_cast hX
  have hx_scaled_nonneg : 0 <= x / (X : Real) := by
    exact div_nonneg hx0 hX_real.le
  have hx_scaled_le_one : x / (X : Real) <= 1 := by
    have hx_le_X : x <= (X : Real) := by
      linarith [hX_real]
    exact (div_le_one hX_real).mpr hx_le_X
  exact
    TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
      hx_scaled_nonneg
      hx_scaled_le_one

/-- On the lower half of the positive scale, the scaled triangle spline is at least `1 / 2`. -/
theorem half_le_triangleSpline_scaled_of_le_half
    (X : Nat)
    (hX : 0 < X)
    {x : Real}
    (hx0 : 0 <= x)
    (hx_half : x <= (X : Real) / 2) :
    (1 / 2 : Real) <=
      TS42.MellinJackson.triangleSpline (x / (X : Real)) := by
  have hX_real : 0 < (X : Real) := by
    exact_mod_cast hX
  have hbranch :=
    triangleSpline_scaled_eq_one_sub_of_le_half X hX hx0 hx_half
  rw [hbranch]
  have hx_scaled_le_half : x / (X : Real) <= 1 / 2 := by
    have hdiv :
        x / (X : Real) <= ((X : Real) / 2) / (X : Real) := by
      exact div_le_div_of_nonneg_right hx_half hX_real.le
    have hsimp : ((X : Real) / 2) / (X : Real) = 1 / 2 := by
      field_simp [ne_of_gt hX_real]
      ring
    linarith
  linarith

/-- Pointwise logarithmic obstruction: the naive Haar square dominates `1 / (4*x)`. -/
theorem naiveTriangleSplineHaarEnergyDensity_lower_bound_on_half
    (X : Nat)
    (hX : 0 < X)
    {x : Real}
    (hx_pos : 0 < x)
    (hx_half : x <= (X : Real) / 2) :
    (1 / 4 : Real) * (1 / x) <=
      naiveTriangleSplineHaarEnergyDensity X x := by
  have hx_nonneg : 0 <= x := hx_pos.le
  have hhalf :
      (1 / 2 : Real) <=
        TS42.MellinJackson.triangleSpline (x / (X : Real)) :=
    half_le_triangleSpline_scaled_of_le_half X hX hx_nonneg hx_half
  have hsquare :
      (1 / 4 : Real) <=
        (TS42.MellinJackson.triangleSpline (x / (X : Real))) ^ 2 := by
    nlinarith [sq_nonneg
      (TS42.MellinJackson.triangleSpline (x / (X : Real)) - (1 / 2 : Real))]
  have hinv_nonneg : 0 <= (1 / x : Real) := by
    exact one_div_nonneg.mpr hx_pos.le
  have hmul :
      (1 / 4 : Real) * (1 / x) <=
        (TS42.MellinJackson.triangleSpline (x / (X : Real))) ^ 2 * (1 / x) :=
    mul_le_mul_of_nonneg_right hsquare hinv_nonneg
  simpa [naiveTriangleSplineHaarEnergyDensity, div_eq_mul_inv] using hmul

/-- The elementary positive-interval integral of `1/x`. -/
theorem integral_one_div_eq_log_sub
    (epsilon B : Real)
    (hepsilon : 0 < epsilon)
    (hepsilonB : epsilon <= B) :
    intervalIntegral
      (fun x : Real => (1 : Real) / x)
      epsilon
      B
      volume =
        Real.log B - Real.log epsilon := by
  have hcont :
      ContinuousOn
        (fun x : Real => (1 : Real) / x)
        (Set.Icc epsilon B) := by
    exact
      continuousOn_const.div
        continuousOn_id
        (by
          intro x hx
          exact ne_of_gt (lt_of_lt_of_le hepsilon hx.1))
  have hint :
      IntervalIntegrable
        (fun x : Real => (1 : Real) / x)
        volume
        epsilon
        B :=
    hcont.intervalIntegrable_of_Icc hepsilonB
  have hderiv :
      forall x,
        (Set.uIcc epsilon B) x ->
          HasDerivAt Real.log ((fun x : Real => (1 : Real) / x) x) x := by
    intro x hx
    have hxIcc : (Set.Icc epsilon B) x := by
      simpa [Set.uIcc_of_le hepsilonB] using hx
    have hx_ne : Not (x = 0) := by
      exact ne_of_gt (lt_of_lt_of_le hepsilon hxIcc.1)
    simpa [one_div] using Real.hasDerivAt_log hx_ne
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/--
Integral lower bound showing the logarithmic obstruction of the naive Haar
square energy.
-/
theorem naiveTriangleSplineHaarEnergy_lower_bound
    (X : Nat)
    (hX : 0 < X)
    (epsilon : Real)
    (hepsilon : 0 < epsilon)
    (hepsilonX : epsilon <= (X : Real) / 2) :
    naiveTriangleSplineHaarEnergyTruncated X epsilon >=
      (1 / 4 : Real) *
        (Real.log ((X : Real) / 2) - Real.log epsilon) := by
  have hbase_cont :
      ContinuousOn
        (fun x : Real => (1 / 4 : Real) * (1 / x))
        (Set.Icc epsilon ((X : Real) / 2)) := by
    exact
      continuousOn_const.mul
        (continuousOn_const.div
          continuousOn_id
          (by
            intro x hx
            exact ne_of_gt (lt_of_lt_of_le hepsilon hx.1)))
  have hdensity_cont :
      ContinuousOn
        (fun x : Real => naiveTriangleSplineHaarEnergyDensity X x)
        (Set.Icc epsilon ((X : Real) / 2)) := by
    have htri :
        ContinuousOn
          (fun x : Real => TS42.MellinJackson.triangleSpline (x / (X : Real)))
          (Set.Icc epsilon ((X : Real) / 2)) := by
      have haff :
          ContinuousOn
            (fun x : Real => 1 - x / (X : Real))
            (Set.Icc epsilon ((X : Real) / 2)) :=
        (continuous_const.sub
          (continuous_id.div_const (X : Real))).continuousOn
      exact
        haff.congr
          (by
            intro x hx
            exact
              triangleSpline_scaled_eq_one_sub_of_le_half
                X
                hX
                (le_trans hepsilon.le hx.1)
                hx.2)
    exact
      (htri.pow 2).div
        continuousOn_id
        (by
          intro x hx
          exact ne_of_gt (lt_of_lt_of_le hepsilon hx.1))
  have hbase_int :
      IntervalIntegrable
        (fun x : Real => (1 / 4 : Real) * (1 / x))
        volume
        epsilon
        ((X : Real) / 2) :=
    hbase_cont.intervalIntegrable_of_Icc hepsilonX
  have hdensity_int :
      IntervalIntegrable
        (fun x : Real => naiveTriangleSplineHaarEnergyDensity X x)
        volume
        epsilon
        ((X : Real) / 2) :=
    hdensity_cont.intervalIntegrable_of_Icc hepsilonX
  have hmono :
      intervalIntegral
        (fun x : Real => (1 / 4 : Real) * (1 / x))
        epsilon
        ((X : Real) / 2)
        volume <=
      naiveTriangleSplineHaarEnergyTruncated X epsilon := by
    dsimp [naiveTriangleSplineHaarEnergyTruncated]
    exact
      intervalIntegral.integral_mono_on
        hepsilonX
        hbase_int
        hdensity_int
        (by
          intro x hx
          exact
            naiveTriangleSplineHaarEnergyDensity_lower_bound_on_half
              X
              hX
              (lt_of_lt_of_le hepsilon hx.1)
              hx.2)
  have hconst :
      intervalIntegral
        (fun x : Real => (1 / 4 : Real) * (1 / x))
        epsilon
        ((X : Real) / 2)
        volume =
      (1 / 4 : Real) *
        intervalIntegral
          (fun x : Real => (1 : Real) / x)
          epsilon
          ((X : Real) / 2)
          volume := by
    rw [intervalIntegral.integral_const_mul]
  have hone_div :
      intervalIntegral
        (fun x : Real => (1 : Real) / x)
        epsilon
        ((X : Real) / 2)
        volume =
      Real.log ((X : Real) / 2) - Real.log epsilon :=
    integral_one_div_eq_log_sub
      epsilon
      ((X : Real) / 2)
      hepsilon
      hepsilonX
  linarith

/--
Logarithmic lower-bound proposition for the naive Haar obstruction.

This is intentionally finite-endpoint and signed-real.  It records the
growth mechanism without pretending to construct a global improper integral.
-/
def NaiveTriangleSplineHaarEnergyLogLowerBoundStatement : Prop :=
  forall (X : Nat) (epsilon : Real),
    0 < X ->
      0 < epsilon ->
        epsilon <= (X : Real) / 2 ->
          naiveTriangleSplineHaarEnergyTruncated X epsilon >=
            (1 / 4 : Real) *
              (Real.log ((X : Real) / 2) - Real.log epsilon)

/-- TS207 proves the logarithmic lower-bound obstruction. -/
theorem naiveTriangleSplineHaarEnergyLogLowerBoundStatement :
    NaiveTriangleSplineHaarEnergyLogLowerBoundStatement := by
  intro X epsilon hX hepsilon hepsilonX
  exact naiveTriangleSplineHaarEnergy_lower_bound X hX epsilon hepsilon hepsilonX

/-- Ledger recording the TS207 naive Haar-energy divergence obstruction. -/
structure NaiveHaarEnergyDivergenceObstructionLedger where
  ts203_truncated_haar_transport :
    TS203.Goldbach.TruncatedHaarTransportEvidenceLedger

  ts206_explicit_formula_statement :
    TS206.Goldbach.ExplicitFormulaEffectiveStatementLedger

  naive_haar_density_defined :
    True

  logarithmic_lower_bound_statement :
    Prop

  logarithmic_lower_bound_proved :
    logarithmic_lower_bound_statement

  ts198_dx_energy_not_contradicted :
    True

  improper_haar_energy_not_constructed :
    True

  mellin_fourier_kernel_not_proved :
    True

  plancherel_not_proved :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS207 obstruction ledger. -/
noncomputable def naiveHaarEnergyDivergenceObstructionLedger :
    NaiveHaarEnergyDivergenceObstructionLedger where
  ts203_truncated_haar_transport :=
    TS203.Goldbach.truncatedHaarTransportEvidenceLedger
  ts206_explicit_formula_statement :=
    TS206.Goldbach.explicitFormulaEffectiveStatementLedger
  naive_haar_density_defined := True.intro
  logarithmic_lower_bound_statement :=
    NaiveTriangleSplineHaarEnergyLogLowerBoundStatement
  logarithmic_lower_bound_proved :=
    naiveTriangleSplineHaarEnergyLogLowerBoundStatement
  ts198_dx_energy_not_contradicted := True.intro
  improper_haar_energy_not_constructed := True.intro
  mellin_fourier_kernel_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS207. -/
def NaiveHaarEnergyDivergenceObstructionTarget : Prop :=
  Nonempty NaiveHaarEnergyDivergenceObstructionLedger

/-- The TS207 naive Haar-energy obstruction target is populated. -/
theorem naiveHaarEnergyDivergenceObstructionTarget :
    NaiveHaarEnergyDivergenceObstructionTarget :=
  Nonempty.intro naiveHaarEnergyDivergenceObstructionLedger

end Goldbach
end TS207
