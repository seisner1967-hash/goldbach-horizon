import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic
import TS.Goldbach.Strong.TS289.CompletedZetaThetaIntegralClosedBound

/-!
# TS290 - Riemann Xi Log-Linear Zero Counting

TS289 gives a closed radial growth bound for the entire xi candidate.  The
original TS283 buffer used an ambient radius `r + 3`; its Jensen logarithmic
gap therefore shrinks like `1 / r` and only yields a quadratic count.  This
sprint rebuilds the same finite-zero geometry with ambient radius `4 * r`.
The resulting averaging radius is at least `2 * r`, so the Jensen denominator
is uniformly bounded below by `log 2`.

The module also proves the missing local bridge from nontrivial zeta zeros to
xi zeros.  The reciprocal archimedean Gamma factor is analytic and nonzero in
the critical strip, hence multiplication by it preserves analytic order.
This identifies the TS264 zeta multiplicity with the TS284 xi multiplicity.

Combining the constant-ratio geometry, the TS289 closed growth estimate, and
the multiplicity bridge produces an unconditional estimate

`N_mult(T) <= C * T * log (T + 2)`

and a concrete TS270 global multiplicity-counting contract.  No
Riemann-von-Mangoldt asymptotic, explicit formula, Gallagher estimate, OTSA
bridge, or Goldbach statement is proved.
-/

noncomputable section

namespace TS290
namespace Goldbach

open Complex Metric Set Topology Filter

/-- The local nonvanishing multiplier relating xi and zeta in the critical
strip. -/
noncomputable def xiZetaLocalMultiplier (s : Complex) : Complex :=
  (s * (s - 1) / 2) /
    TS282.Goldbach.completedRiemannZetaGammaInv s

theorem riemannXiCandidate_eq_localMultiplier_mul_riemannZeta
    {s : Complex}
    (hsRe : 0 < s.re)
    (hsReOne : s.re < 1) :
    TS282.Goldbach.riemannXiCandidate s =
      xiZetaLocalMultiplier s * riemannZeta s := by
  have hs0 : Not (s = 0) := by
    intro hs
    subst s
    norm_num at hsRe
  have hs1 : Not (s = 1) := by
    intro hs
    subst s
    norm_num at hsReOne
  have hGamma :
      Not (TS282.Goldbach.completedRiemannZetaGammaInv s = 0) :=
    TS282.Goldbach.completedRiemannZetaGammaInv_ne_zero_of_re_pos hsRe
  rw [TS282.Goldbach.riemannXiCandidate_eq_completedRiemannZeta_mul
    hs0 hs1]
  rw [TS282.Goldbach.riemannZeta_eq_completed_mul_gammaInv hs0]
  unfold xiZetaLocalMultiplier
  field_simp [hGamma]
  ring

theorem xiZetaLocalMultiplier_analyticAt
    {rho : Complex}
    (hRe : 0 < rho.re) :
    AnalyticAt Complex xiZetaLocalMultiplier rho := by
  unfold xiZetaLocalMultiplier
  have hGammaAnalytic :
      AnalyticAt Complex
        TS282.Goldbach.completedRiemannZetaGammaInv rho :=
    (TS282.Goldbach.differentiable_completedRiemannZetaGammaInv).differentiableOn.analyticAt
      univ_mem
  exact
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div
      analyticAt_const (by norm_num)).div hGammaAnalytic
      (TS282.Goldbach.completedRiemannZetaGammaInv_ne_zero_of_re_pos hRe)

theorem xiZetaLocalMultiplier_ne_zero
    {rho : Complex}
    (hRe : 0 < rho.re)
    (hReOne : rho.re < 1) :
    Not (xiZetaLocalMultiplier rho = 0) := by
  have hrho0 : Not (rho = 0) := by
    intro h
    subst rho
    norm_num at hRe
  have hrho1 : Not (rho = 1) := by
    intro h
    subst rho
    norm_num at hReOne
  unfold xiZetaLocalMultiplier
  exact div_ne_zero
    (div_ne_zero
      (mul_ne_zero hrho0 (sub_ne_zero.mpr hrho1)) (by norm_num))
    (TS282.Goldbach.completedRiemannZetaGammaInv_ne_zero_of_re_pos hRe)

theorem riemannXiCandidate_eventuallyEq_localMultiplier_mul_riemannZeta
    {rho : Complex}
    (hRe : 0 < rho.re)
    (hReOne : rho.re < 1) :
    Filter.Eventually
      (fun s =>
        TS282.Goldbach.riemannXiCandidate s =
          xiZetaLocalMultiplier s * riemannZeta s)
      (nhds rho) := by
  have hRight : Membership.mem (nhds rho) {s : Complex | 0 < s.re} :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hRe
  have hLeft : Membership.mem (nhds rho) {s : Complex | s.re < 1} :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hReOne
  filter_upwards [hRight, hLeft] with s hsRight hsLeft
  exact riemannXiCandidate_eq_localMultiplier_mul_riemannZeta
    hsRight hsLeft

/-- Every concrete nontrivial zeta zero is an xi zero. -/
theorem concreteNontrivialRiemannZetaZero_is_xi_zero
    {rho : Complex}
    (hZero : TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho) :
    TS282.Goldbach.riemannXiCandidate rho = 0 := by
  have hStrip := TS264.Goldbach.concreteZero_in_critical_strip hZero
  rw [riemannXiCandidate_eq_localMultiplier_mul_riemannZeta
    hStrip.1 hStrip.2]
  rw [TS264.Goldbach.concreteZero_is_zeta_zero hZero]
  simp

/-- The TS264 zeta multiplicity agrees exactly with the TS284 xi
multiplicity at every selected nontrivial zero. -/
theorem concreteRiemannZetaMultiplicity_eq_riemannXiCandidateMultiplicity
    {rho : Complex}
    (hZero : TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho) :
    TS264.Goldbach.concreteRiemannZetaMultiplicity rho =
      TS284.Goldbach.riemannXiCandidateMultiplicity rho := by
  let hzeta := TS260.Goldbach.riemannZeta_analyticAt_of_ne_one
    rho (TS264.Goldbach.concreteZero_ne_one hZero)
  let m := TS264.Goldbach.concreteRiemannZetaMultiplicity rho
  have hOrder : hzeta.order = (m : ENat) := by
    exact (TS264.Goldbach.concreteRiemannZetaMultiplicity_coe_eq_order
      hZero).symm
  have hFactorExists :=
    (AnalyticAt.order_eq_nat_iff hzeta m).mp hOrder
  let h : Complex -> Complex := Classical.choose hFactorExists
  have hhSpec := Classical.choose_spec hFactorExists
  have hhAnalytic : AnalyticAt Complex h rho := hhSpec.1
  have hhNonzero : Not (h rho = 0) := hhSpec.2.1
  have hhFactor := hhSpec.2.2
  have hStrip := TS264.Goldbach.concreteZero_in_critical_strip hZero
  let H : Complex -> Complex := fun z => xiZetaLocalMultiplier z * h z
  have hHAnalytic : AnalyticAt Complex H rho :=
    (xiZetaLocalMultiplier_analyticAt hStrip.1).mul hhAnalytic
  have hHNonzero : Not (H rho = 0) :=
    mul_ne_zero
      (xiZetaLocalMultiplier_ne_zero hStrip.1 hStrip.2)
      hhNonzero
  have hHFactor :
      Filter.Eventually
        (fun z =>
          TS282.Goldbach.riemannXiCandidate z =
            (z - rho) ^ m * H z)
        (nhds rho) := by
    filter_upwards
      [riemannXiCandidate_eventuallyEq_localMultiplier_mul_riemannZeta
        hStrip.1 hStrip.2, hhFactor]
      with z hXi hZeta
    rw [hXi, hZeta]
    simp only [H, smul_eq_mul]
    ring
  have hXiOrder :
      (TS282.Goldbach.riemannXiCandidate_analyticAt rho).order =
        (m : ENat) := by
    apply (AnalyticAt.order_eq_nat_iff
      (TS282.Goldbach.riemannXiCandidate_analyticAt rho) m).mpr
    exact Exists.intro H
      (And.intro hHAnalytic (And.intro hHNonzero hHFactor))
  have hCoe :
      (TS284.Goldbach.riemannXiCandidateMultiplicity rho : ENat) =
        (m : ENat) := by
    rw [TS284.Goldbach.riemannXiCandidateMultiplicity_coe_eq_order]
    exact hXiOrder
  exact (ENat.coe_inj.mp hCoe).symm

/-- Constant-ratio finite-zero geometry.  The ambient radius is `4 * r`, so
the averaging radius is at least `2 * r`. -/
noncomputable def xiDyadicFiniteZeroGeometryData
    (r : Real)
    (hr : 0 < r) : TS283.Goldbach.XiFiniteZeroGeometryData := by
  let T : Real := 4 * r
  let L : Real := TS283.Goldbach.xiZeroRadiusBarrier r T
  let R : Real := (2 * L + T) / 3
  let S : Real := (L + 2 * T) / 3
  have hrT : r < T := by
    dsimp [T]
    linarith
  have hrL : r <= L :=
    TS283.Goldbach.innerRadius_le_xiZeroRadiusBarrier r T
  have hLT : L < T := TS283.Goldbach.xiZeroRadiusBarrier_lt hrT
  have hGapPos : 0 < (T - L) / 3 :=
    div_pos (sub_pos.mpr hLT) (by norm_num)
  have hLR : L < R := by
    apply sub_pos.mp
    have hEq : R - L = (T - L) / 3 := by
      dsimp only [R]
      ring
    rw [hEq]
    exact hGapPos
  have hrR : r < R := lt_of_le_of_lt hrL hLR
  have hRS : R < S := by
    apply sub_pos.mp
    have hEq : S - R = (T - L) / 3 := by
      dsimp only [R, S]
      ring
    rw [hEq]
    exact hGapPos
  have hST : S < T := by
    rw [sub_pos.symm]
    have hEq : T - S = (T - L) / 3 := by
      dsimp only [S]
      ring
    rw [hEq]
    exact hGapPos
  let C : TS275.Goldbach.JensenDiskConfiguration :=
    { center := 0
      innerRadius := r
      averagingRadius := R
      analyticRadius := S
      innerRadius_positive := hr
      innerRadius_lt_averagingRadius := hrR
      averagingRadius_lt_analyticRadius := hRS }
  exact
    { config := C
      innerZeros := TS283.Goldbach.riemannXiCandidateZerosInClosedBall r
      factorZeros := TS283.Goldbach.riemannXiCandidateZerosInClosedBall S
      center_eq_zero := rfl
      innerZeros_subset_factorZeros := by
        intro z hz
        rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff] at hz
        rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff]
        exact And.intro (hz.1.trans (le_of_lt (hrR.trans hRS))) hz.2
      inner_zero_mem_disk := by
        intro z hz
        rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff] at hz
        simpa [C] using hz.1
      factor_zero_mem_open_disk := by
        intro z hz
        rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff] at hz
        have hzT : Complex.abs z < T := hz.1.trans_lt hST
        have hzMemT :
            Membership.mem
              (TS283.Goldbach.riemannXiCandidateZerosInClosedBall T) z := by
          rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff]
          exact And.intro (hz.1.trans hST.le) hz.2
        have hzL : Complex.abs z <= L :=
          TS283.Goldbach.xiZeroRadius_le_barrier hzMemT hzT
        simpa [C] using hzL.trans_lt hLR
      factor_zero_iff := by
        intro z hzBall
        rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff]
        have hzAbs : Complex.abs z <= S := by
          simpa [C, Metric.mem_closedBall, dist_zero_right] using hzBall
        constructor
        case mp =>
          intro hzZero
          exact And.intro hzAbs hzZero
        case mpr => exact fun hz => hz.2
      zero_free_collar := by
        intro z hzR hzS hzZero
        have hzAbsS : Complex.abs z <= S := by simpa [C] using hzS
        have hzT : Complex.abs z < T := hzAbsS.trans_lt hST
        have hzMemT :
            Membership.mem
              (TS283.Goldbach.riemannXiCandidateZerosInClosedBall T) z := by
          rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff]
          exact And.intro (hzAbsS.trans hST.le) hzZero
        have hzL : Complex.abs z <= L :=
          TS283.Goldbach.xiZeroRadius_le_barrier hzMemT hzT
        have hzR' : R <= Complex.abs z := by simpa [C] using hzR
        exact (not_lt_of_ge hzR') (hzL.trans_lt hLR) }

@[simp]
theorem xiDyadicFiniteZeroGeometryData_innerRadius
    (r : Real)
    (hr : 0 < r) :
    (xiDyadicFiniteZeroGeometryData r hr).config.innerRadius = r := rfl

theorem xiDyadicFiniteZeroGeometryData_two_mul_inner_le_averaging
    (r : Real)
    (hr : 0 < r) :
    2 * r <=
      (xiDyadicFiniteZeroGeometryData r hr).config.averagingRadius := by
  change 2 * r <=
    (2 * TS283.Goldbach.xiZeroRadiusBarrier r (4 * r) + 4 * r) / 3
  have hBarrier :=
    TS283.Goldbach.innerRadius_le_xiZeroRadiusBarrier r (4 * r)
  linarith

theorem xiDyadicFiniteZeroGeometryData_averaging_lt_four_mul
    (r : Real)
    (hr : 0 < r) :
    (xiDyadicFiniteZeroGeometryData r hr).config.averagingRadius < 4 * r := by
  change
    (2 * TS283.Goldbach.xiZeroRadiusBarrier r (4 * r) + 4 * r) / 3 <
      4 * r
  have hrT : r < 4 * r := by linarith
  have hBarrier := TS283.Goldbach.xiZeroRadiusBarrier_lt hrT
  linarith

/-- Enrich arbitrary TS283 geometry with the canonical TS284 local data. -/
noncomputable def xiFiniteZeroFactorizationSpecOfGeometry
    (G : TS283.Goldbach.XiFiniteZeroGeometryData) :
    TS282.Goldbach.XiFiniteZeroFactorizationSpec where
  config := G.config
  innerZeros := G.innerZeros
  factorZeros := G.factorZeros
  multiplicity := TS284.Goldbach.riemannXiCandidateMultiplicity
  center_eq_zero := G.center_eq_zero
  innerZeros_subset_factorZeros := G.innerZeros_subset_factorZeros
  inner_zero_mem_disk := G.inner_zero_mem_disk
  factor_zero_mem_open_disk := G.factor_zero_mem_open_disk
  multiplicity_positive := by
    intro rho hRho
    exact TS284.Goldbach.riemannXiCandidateMultiplicity_positive
      (TS284.Goldbach.XiFiniteZeroGeometryData.factor_zero_is_xi_zero
        G rho hRho)
  factor_zero_iff := G.factor_zero_iff
  local_normal_form := by
    intro rho _
    exact TS284.Goldbach.riemannXiCandidate_local_normal_form rho

noncomputable def xiDyadicFiniteZeroFactorizationSpec
    (r : Real)
    (hr : 0 < r) : TS282.Goldbach.XiFiniteZeroFactorizationSpec :=
  xiFiniteZeroFactorizationSpecOfGeometry
    (xiDyadicFiniteZeroGeometryData r hr)

noncomputable def xiDyadicBufferedQuotientAssembly
    (r : Real)
    (hr : 0 < r) :
    TS282.Goldbach.XiBufferedQuotientAssembly
      (xiDyadicFiniteZeroFactorizationSpec r hr) where
  quotient := TS285.Goldbach.riemannXiFiniteQuotient
    (xiDyadicFiniteZeroFactorizationSpec r hr)
  quotient_analytic :=
    TS285.Goldbach.riemannXiFiniteQuotient_analyticOnNhd _ _
  factorization := by
    intro z _
    exact TS285.Goldbach.riemannXiFiniteQuotient_factorization _ z
  quotient_nonzero := by
    intro z hz
    exact
      TS285.Goldbach.riemannXiFiniteQuotient_nonzero_on_analyticClosedBall
        _ z hz

noncomputable def xiDyadicBufferedConstruction
    (r : Real)
    (hr : 0 < r) : TS282.Goldbach.XiBufferedFactorizationConstruction where
  spec := xiDyadicFiniteZeroFactorizationSpec r hr
  assembly := xiDyadicBufferedQuotientAssembly r hr

noncomputable def xiDyadicBufferedData
    (r : Real)
    (hr : 0 < r) : TS275.Goldbach.BufferedJensenFactorizationData :=
  (xiDyadicBufferedConstruction r hr).toBufferedJensenFactorizationData

noncomputable def xiDyadicDiskData
    (r : Real)
    (hr : 0 < r) : TS274.Goldbach.FiniteJensenDiskData :=
  TS275.Goldbach.JensenInnerZeroData.toFiniteJensenDiskData
    (TS275.Goldbach.JensenFactorZeroData.toJensenInnerZeroData
      (TS282.Goldbach.XiFiniteZeroFactorizationSpec.toJensenFactorZeroData
        (xiDyadicBufferedConstruction r hr).spec))

@[simp]
theorem xiDyadicDiskData_center
    (r : Real)
    (hr : 0 < r) :
    (xiDyadicDiskData r hr).center = 0 := rfl

@[simp]
theorem xiDyadicDiskData_zeros
    (r : Real)
    (hr : 0 < r) :
    (xiDyadicDiskData r hr).zeros =
      TS283.Goldbach.riemannXiCandidateZerosInClosedBall r := rfl

@[simp]
theorem xiDyadicDiskData_multiplicity
    (r : Real)
    (hr : 0 < r) :
    (xiDyadicDiskData r hr).multiplicity =
      TS284.Goldbach.riemannXiCandidateMultiplicity := rfl

@[simp]
theorem xiDyadicBufferedData_function
    (r : Real)
    (hr : 0 < r) :
    (xiDyadicBufferedData r hr).f =
      TS282.Goldbach.riemannXiCandidate := rfl

@[simp]
theorem xiDyadicBufferedData_center
    (r : Real)
    (hr : 0 < r) :
    (xiDyadicBufferedData r hr).zeroData.config.center = 0 := rfl

noncomputable def xiDyadicBoundaryMajorant
    (r : Real)
    (hr : 0 < r) : Real :=
  TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
    TS289.Goldbach.completedZetaThetaClosedMajorant
    (xiDyadicBufferedData r hr).zeroData.config.averagingRadius

noncomputable def xiDyadicBoundaryNormStatement
    (r : Real)
    (hr : 0 < r)
    (hrOne : 1 <= r) :
    TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
      (xiDyadicBufferedData r hr) (xiDyadicBoundaryMajorant r hr) where
  M_positive := TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta_positive _ _
  norm_le := by
    intro z hz
    have hLarge :
        2 <= (xiDyadicBufferedData r hr).zeroData.config.averagingRadius := by
      have hRatio :=
        xiDyadicFiniteZeroGeometryData_two_mul_inner_le_averaging r hr
      change 2 <=
        (xiDyadicFiniteZeroGeometryData r hr).config.averagingRadius
      linarith
    have hzCircle :
        Complex.abs z =
          (xiDyadicBufferedData r hr).zeroData.config.averagingRadius := by
      simpa using hz
    simpa [xiDyadicBoundaryMajorant] using
      (TS287.Goldbach.xi_abs_le_boundaryMajorantFromCompletedZeta
        TS289.Goldbach.completedZetaThetaClosedCircleGrowth
        (xiDyadicBufferedData r hr).zeroData.config.averagingRadius
        hLarge z hzCircle)

theorem xiDyadicFiniteJensenBoundaryEstimate
    (r : Real)
    (hr : 0 < r)
    (hrOne : 1 <= r) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      (xiDyadicDiskData r hr)
      TS282.Goldbach.riemannXiCandidate
      (xiDyadicBoundaryMajorant r hr) := by
  simpa [xiDyadicDiskData, xiDyadicBufferedData] using
    TS279.Goldbach.finiteJensenBoundaryEstimate_of_boundaryNorm
      (xiDyadicBufferedData r hr)
      (xiDyadicBoundaryMajorant r hr)
      (xiDyadicBoundaryNormStatement r hr hrOne)

theorem xiDyadicMultiplicityCount_le_boundaryLogQuotient
    (r : Real)
    (hr : 0 < r)
    (hrOne : 1 <= r) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        (xiDyadicDiskData r hr) : Real) <=
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (xiDyadicBoundaryMajorant r hr)
          (TS282.Goldbach.riemannXiCandidate 0) /
        Real.log
          ((xiDyadicDiskData r hr).outerRadius /
            (xiDyadicDiskData r hr).innerRadius) := by
  simpa using
    (TS274.Goldbach.finiteJensenMultiplicityCount_le_boundaryLogQuotient
      (xiDyadicDiskData r hr)
      TS282.Goldbach.riemannXiCandidate
      (xiDyadicBoundaryMajorant r hr)
      (xiDyadicFiniteJensenBoundaryEstimate r hr hrOne))

theorem two_le_completedZetaThetaTailConstant :
    2 <= TS289.Goldbach.completedZetaThetaTailConstant := by
  have hExpPos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  have hExpLtOne : Real.exp (-Real.pi) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos Real.pi_pos
  have hDenPos : 0 < 1 - Real.exp (-Real.pi) := sub_pos.mpr hExpLtOne
  have hDenLeOne : 1 - Real.exp (-Real.pi) <= 1 := by linarith
  have hInvOne : 1 <= (1 - Real.exp (-Real.pi)) ^ (-1 : Int) := by
    have hMul := mul_le_mul_of_nonneg_right hDenLeOne
      (inv_pos.mpr hDenPos).le
    simpa [zpow_neg_one, hDenPos.ne'] using hMul
  have hInvOneDiv : 1 <= 1 / (1 - Real.exp (-Real.pi)) := by
    simpa [one_div, zpow_neg_one] using hInvOne
  unfold TS289.Goldbach.completedZetaThetaTailConstant
  calc
    (2 : Real) = 2 * 1 := by ring
    _ <= 2 * (1 / (1 - Real.exp (-Real.pi))) :=
      mul_le_mul_of_nonneg_left hInvOneDiv (by norm_num)
    _ = 2 / (1 - Real.exp (-Real.pi)) := by ring

theorem xiDyadicBoundaryLogBudget_le
    (r : Real)
    (hr : 0 < r)
    (hrOne : 1 <= r) :
    TS274.Goldbach.finiteJensenBoundaryLogBudget
        (xiDyadicBoundaryMajorant r hr)
        (TS282.Goldbach.riemannXiCandidate 0) <=
      ((xiDyadicDiskData r hr).outerRadius + 3) *
          Real.log ((xiDyadicDiskData r hr).outerRadius + 2) +
        TS289.Goldbach.completedZetaThetaTailConstant := by
  let a : Real :=
    (xiDyadicBufferedData r hr).zeroData.config.averagingRadius
  let C : Real := TS289.Goldbach.completedZetaThetaTailConstant
  let E : Real := a * Real.log (a + 2)
  let X : Real := a * (a + 1) * (C * Real.exp E)
  have ha2 : 2 <= a := by
    have hRatio :=
      xiDyadicFiniteZeroGeometryData_two_mul_inner_le_averaging r hr
    change 2 <= (xiDyadicFiniteZeroGeometryData r hr).config.averagingRadius
    linarith
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha2
  have hC2 : 2 <= C := two_le_completedZetaThetaTailConstant
  have hCPos : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  have hLogNonnegative : 0 <= Real.log (a + 2) := by
    apply Real.log_nonneg
    linarith
  have hENonnegative : 0 <= E := mul_nonneg haPos.le hLogNonnegative
  have hExpOne : 1 <= Real.exp E := Real.one_le_exp hENonnegative
  have hProdOne : 6 <= a * (a + 1) := by
    have hNonnegative : 0 <= (a - 2) * (a + 3) :=
      mul_nonneg (sub_nonneg.mpr ha2) (by linarith)
    nlinarith
  have hProdTwo : 12 <= a * (a + 1) * C := by
    have h := mul_le_mul hProdOne hC2
      (by norm_num : (0 : Real) <= 2)
      (by linarith : 0 <= a * (a + 1))
    norm_num at h
    exact h
  have hX12 : 12 <= X := by
    have h := mul_le_mul hProdTwo hExpOne
      (by norm_num : (0 : Real) <= 1)
      (by linarith : 0 <= a * (a + 1) * C)
    norm_num at h
    simpa [X, mul_assoc] using h
  have hXOne : 1 <= X := by linarith
  have hXPos : 0 < X := lt_of_lt_of_le zero_lt_one hXOne
  have hMax : max 1 ((X + 1) / 2) = (X + 1) / 2 := by
    rw [max_eq_right]
    linarith
  have hBudgetEq :
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (xiDyadicBoundaryMajorant r hr)
          (TS282.Goldbach.riemannXiCandidate 0) =
        Real.log (X + 1) := by
    rw [TS282.Goldbach.riemannXiCandidate_zero]
    unfold TS274.Goldbach.finiteJensenBoundaryLogBudget
      xiDyadicBoundaryMajorant
      TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
      TS289.Goldbach.completedZetaThetaClosedMajorant
    change Real.log
      (max 1 ((X + 1) / 2) / Complex.abs ((1 : Complex) / 2)) =
        Real.log (X + 1)
    rw [hMax]
    norm_num
    congr 1
    ring
  have hLogX :
      Real.log X =
        Real.log a + Real.log (a + 1) + Real.log C + E := by
    dsimp [X]
    rw [Real.log_mul (mul_ne_zero haPos.ne' (by linarith))
      (mul_ne_zero hCPos.ne' (Real.exp_pos E).ne')]
    rw [Real.log_mul haPos.ne' (by linarith)]
    rw [Real.log_mul hCPos.ne' (Real.exp_pos E).ne']
    rw [Real.log_exp]
    ring
  have hLogC : Real.log C <= C := by
    exact (Real.log_le_sub_one_of_pos hCPos).trans (by linarith)
  have hLogTwo : Real.log 2 <= Real.log (a + 2) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num)
      (by show 0 < a + 2; linarith)
      (by show (2 : Real) <= a + 2; linarith)
  have hLogA : Real.log a <= Real.log (a + 2) := by
    exact Real.strictMonoOn_log.monotoneOn
      haPos
      (by show 0 < a + 2; linarith)
      (by show a <= a + 2; linarith)
  have hLogASucc : Real.log (a + 1) <= Real.log (a + 2) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by show 0 < a + 1; linarith)
      (by show 0 < a + 2; linarith)
      (by show a + 1 <= a + 2; linarith)
  rw [hBudgetEq]
  calc
    Real.log (X + 1) <= Real.log (2 * X) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by show 0 < X + 1; linarith)
        (mul_pos (by norm_num) hXPos)
        (by show X + 1 <= 2 * X; linarith)
    _ = Real.log 2 + Real.log X := by
      rw [Real.log_mul (by norm_num) hXPos.ne']
    _ = Real.log 2 +
        (Real.log a + Real.log (a + 1) + Real.log C + E) := by
      rw [hLogX]
    _ <= (a + 3) * Real.log (a + 2) + C := by
      dsimp [E]
      nlinarith
    _ = ((xiDyadicDiskData r hr).outerRadius + 3) *
          Real.log ((xiDyadicDiskData r hr).outerRadius + 2) +
        TS289.Goldbach.completedZetaThetaTailConstant := by
      rfl

theorem log_two_le_xiDyadicLogRadiusGap
    (r : Real)
    (hr : 0 < r) :
    Real.log 2 <=
      Real.log
        ((xiDyadicDiskData r hr).outerRadius /
          (xiDyadicDiskData r hr).innerRadius) := by
  have hOuter :
      2 * r <= (xiDyadicDiskData r hr).outerRadius := by
    exact xiDyadicFiniteZeroGeometryData_two_mul_inner_le_averaging r hr
  have hInner : (xiDyadicDiskData r hr).innerRadius = r := rfl
  rw [hInner]
  have hRatio : 2 <= (xiDyadicDiskData r hr).outerRadius / r := by
    calc
      (2 : Real) = (2 * r) / r := by field_simp
      _ <= (xiDyadicDiskData r hr).outerRadius / r :=
        div_le_div_of_nonneg_right hOuter hr.le
  exact Real.strictMonoOn_log.monotoneOn
    (by norm_num)
    (div_pos (lt_of_lt_of_le (mul_pos (by norm_num) hr) hOuter) hr)
    hRatio

theorem one_half_le_xiDyadicLogRadiusGap
    (r : Real)
    (hr : 0 < r) :
    (1 : Real) / 2 <=
      Real.log
        ((xiDyadicDiskData r hr).outerRadius /
          (xiDyadicDiskData r hr).innerRadius) := by
  have hHalfLogTwo : (1 : Real) / 2 <= Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  exact hHalfLogTwo.trans (log_two_le_xiDyadicLogRadiusGap r hr)

noncomputable def xiDyadicLogLinearConstant : Real :=
  28 + 4 * TS289.Goldbach.completedZetaThetaTailConstant

theorem xiDyadicLogLinearConstant_nonnegative :
    0 <= xiDyadicLogLinearConstant := by
  unfold xiDyadicLogLinearConstant
  nlinarith [TS289.Goldbach.completedZetaThetaTailConstant_pos]

theorem xiDyadicBoundaryLogBudget_nonnegative
    (r : Real)
    (hr : 0 < r) :
    0 <= TS274.Goldbach.finiteJensenBoundaryLogBudget
      (xiDyadicBoundaryMajorant r hr)
      (TS282.Goldbach.riemannXiCandidate 0) := by
  have hCenter :
      0 < Complex.abs (TS282.Goldbach.riemannXiCandidate 0) := by
    rw [TS282.Goldbach.riemannXiCandidate_zero]
    norm_num
  have hBound :
      Complex.abs (TS282.Goldbach.riemannXiCandidate 0) <=
        xiDyadicBoundaryMajorant r hr := by
    rw [TS282.Goldbach.riemannXiCandidate_zero]
    have hOne : 1 <= xiDyadicBoundaryMajorant r hr := by
      unfold xiDyadicBoundaryMajorant
        TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
      exact le_max_left _ _
    norm_num
    linarith
  exact TS274.Goldbach.finiteJensenBoundaryLogBudget_nonnegative
    (xiDyadicBoundaryMajorant r hr)
    (TS282.Goldbach.riemannXiCandidate 0) hCenter hBound

/-- Closed log-linear xi count for the constant-ratio Jensen geometry. -/
theorem xiDyadicMultiplicityCount_le_logLinear
    (r : Real)
    (hr : 0 < r)
    (hrOne : 1 <= r) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        (xiDyadicDiskData r hr) : Real) <=
      xiDyadicLogLinearConstant * r * Real.log (r + 2) := by
  let a : Real := (xiDyadicDiskData r hr).outerRadius
  let C : Real := TS289.Goldbach.completedZetaThetaTailConstant
  let B : Real := TS274.Goldbach.finiteJensenBoundaryLogBudget
    (xiDyadicBoundaryMajorant r hr)
    (TS282.Goldbach.riemannXiCandidate 0)
  let d : Real := Real.log
    ((xiDyadicDiskData r hr).outerRadius /
      (xiDyadicDiskData r hr).innerRadius)
  have haUpper : a < 4 * r :=
    xiDyadicFiniteZeroGeometryData_averaging_lt_four_mul r hr
  have haPos : 0 < a := by
    have hOuter := TS274.Goldbach.finiteJensen_outerRadius_positive
      (xiDyadicDiskData r hr)
    exact hOuter
  have hLogRNonnegative : 0 <= Real.log (r + 2) := by
    apply Real.log_nonneg
    linarith
  have hArgUpper : a + 2 <= (r + 2) ^ 2 := by
    have hSquare : 0 <= r ^ 2 := sq_nonneg r
    nlinarith
  have hArgPositive : 0 < a + 2 := by linarith
  have hSquarePositive : 0 < (r + 2) ^ 2 :=
    pow_pos (by linarith) 2
  have hLogUpper : Real.log (a + 2) <= 2 * Real.log (r + 2) := by
    calc
      Real.log (a + 2) <= Real.log ((r + 2) ^ 2) :=
        Real.strictMonoOn_log.monotoneOn hArgPositive hSquarePositive hArgUpper
      _ = 2 * Real.log (r + 2) := by
        rw [Real.log_pow]
        norm_num
  have hLinearUpper : a + 3 <= 7 * r := by linarith
  have hMainNonnegative : 0 <= a + 3 := by linarith
  have hLogA2Nonnegative : 0 <= Real.log (a + 2) :=
    Real.log_nonneg (by linarith)
  have hBudgetUpper :
      B <= (14 + 2 * C) * r * Real.log (r + 2) := by
    have hBase := xiDyadicBoundaryLogBudget_le r hr hrOne
    have hProduct :
        (a + 3) * Real.log (a + 2) <=
          14 * r * Real.log (r + 2) := by
      calc
        (a + 3) * Real.log (a + 2) <=
            (7 * r) * (2 * Real.log (r + 2)) :=
          mul_le_mul hLinearUpper hLogUpper
            hLogA2Nonnegative (mul_nonneg (by norm_num) hr.le)
        _ = 14 * r * Real.log (r + 2) := by ring
    have hHalfLog : (1 : Real) / 2 <= Real.log (r + 2) := by
      have hLogTwo : Real.log 2 <= Real.log (r + 2) :=
        Real.strictMonoOn_log.monotoneOn
          (by norm_num)
          (by show 0 < r + 2; linarith)
          (by show (2 : Real) <= r + 2; linarith)
      exact (by linarith [Real.log_two_gt_d9] :
        (1 : Real) / 2 <= Real.log 2).trans hLogTwo
    have hCAbsorb : C <= 2 * C * r * Real.log (r + 2) := by
      have hCNonnegative : 0 <= C :=
        TS289.Goldbach.completedZetaThetaTailConstant_pos.le
      have hScale : 1 <= 2 * r * Real.log (r + 2) := by
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hScale hCNonnegative]
    change B <= (14 + 2 * C) * r * Real.log (r + 2)
    calc
      B <= (a + 3) * Real.log (a + 2) + C := hBase
      _ <= 14 * r * Real.log (r + 2) +
          2 * C * r * Real.log (r + 2) := add_le_add hProduct hCAbsorb
      _ = (14 + 2 * C) * r * Real.log (r + 2) := by ring
  have hdHalf : (1 : Real) / 2 <= d :=
    one_half_le_xiDyadicLogRadiusGap r hr
  have hdPos : 0 < d := lt_of_lt_of_le (by norm_num) hdHalf
  have hBNonnegative : 0 <= B := xiDyadicBoundaryLogBudget_nonnegative r hr
  have hDivide : B / d <= 2 * B := by
    calc
      B / d <= B / ((1 : Real) / 2) :=
        div_le_div_of_nonneg_left hBNonnegative (by norm_num) hdHalf
      _ = 2 * B := by ring
  have hCount := xiDyadicMultiplicityCount_le_boundaryLogQuotient
    r hr hrOne
  change
    (TS274.Goldbach.finiteJensenMultiplicityCount
        (xiDyadicDiskData r hr) : Real) <=
      xiDyadicLogLinearConstant * r * Real.log (r + 2)
  calc
    (TS274.Goldbach.finiteJensenMultiplicityCount
        (xiDyadicDiskData r hr) : Real) <= B / d := hCount
    _ <= 2 * B := hDivide
    _ <= 2 * ((14 + 2 * C) * r * Real.log (r + 2)) :=
      mul_le_mul_of_nonneg_left hBudgetUpper (by norm_num)
    _ = xiDyadicLogLinearConstant * r * Real.log (r + 2) := by
      unfold xiDyadicLogLinearConstant
      dsimp [C]
      ring

theorem zerosUpToHeight_subset_xiDyadicZeros
    (T : Real)
    (hT : 0 <= T) :
    TS265.Goldbach.zerosUpToHeight T <=
      (xiDyadicDiskData (T + 1) (by linarith)).zeros := by
  intro rho hRho
  have hSelected := (TS265.Goldbach.mem_zerosUpToHeight_iff T rho).mp hRho
  have hHeightSet : TS265.Goldbach.heightTruncatedZeroSet T rho := hSelected
  have hCompact := TS265.Goldbach.heightTruncatedZeroSet_subset_compact_inter
    T hHeightSet
  rw [xiDyadicDiskData_zeros]
  rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff]
  exact And.intro
    (by simpa [Metric.mem_closedBall, dist_zero_right] using hCompact.1)
    (concreteNontrivialRiemannZetaZero_is_xi_zero hSelected.1)

/-- The concrete TS270 height count is bounded by the corresponding xi disk
count, with exact multiplicity transport. -/
theorem concreteMultiplicityCountUpToHeight_le_xiDyadicCount
    (T : Real)
    (hT : 0 <= T) :
    TS270.Goldbach.concreteMultiplicityCountUpToHeight T <=
      TS274.Goldbach.finiteJensenMultiplicityCount
        (xiDyadicDiskData (T + 1) (by linarith)) := by
  let hPos : 0 < T + 1 := by linarith
  have hSubset := zerosUpToHeight_subset_xiDyadicZeros T hT
  unfold TS270.Goldbach.concreteMultiplicityCountUpToHeight
    TS274.Goldbach.finiteJensenMultiplicityCount
  rw [xiDyadicDiskData_multiplicity]
  calc
    Finset.sum (TS265.Goldbach.zerosUpToHeight T)
        (fun rho =>
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho) =
      Finset.sum (TS265.Goldbach.zerosUpToHeight T)
        TS284.Goldbach.riemannXiCandidateMultiplicity := by
          apply Finset.sum_congr rfl
          intro rho hRho
          have hZero := (TS265.Goldbach.mem_zerosUpToHeight_iff T rho).mp hRho |>.1
          exact
            concreteRiemannZetaMultiplicity_eq_riemannXiCandidateMultiplicity
              hZero
    _ <= Finset.sum (xiDyadicDiskData (T + 1) hPos).zeros
        TS284.Goldbach.riemannXiCandidateMultiplicity := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
          intro rho _ _
          exact Nat.zero_le _

noncomputable def xiGlobalLogLinearConstant : Real :=
  4 * xiDyadicLogLinearConstant

theorem xiGlobalLogLinearConstant_nonnegative :
    0 <= xiGlobalLogLinearConstant := by
  unfold xiGlobalLogLinearConstant
  exact mul_nonneg (by norm_num) xiDyadicLogLinearConstant_nonnegative

/-- Unconditional large-height log-linear count for the concrete TS264 zeta
zeros, including analytic multiplicity. -/
theorem concreteMultiplicityCountUpToHeight_le_logLinear
    (T : Real)
    (hT : 1 <= T) :
    (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
      xiGlobalLogLinearConstant * T * Real.log (T + 2) := by
  let hPos : 0 < T + 1 := by linarith
  have hNat := concreteMultiplicityCountUpToHeight_le_xiDyadicCount T (by linarith)
  have hNatReal :
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
        (TS274.Goldbach.finiteJensenMultiplicityCount
          (xiDyadicDiskData (T + 1) hPos) : Real) := by
    exact_mod_cast hNat
  have hXi := xiDyadicMultiplicityCount_le_logLinear
    (T + 1) hPos (by linarith)
  have hLogNonnegative : 0 <= Real.log (T + 2) := by
    apply Real.log_nonneg
    linarith
  have hArgument : T + 3 <= (T + 2) ^ 2 := by
    nlinarith [sq_nonneg T]
  have hLogArgument : Real.log (T + 3) <= 2 * Real.log (T + 2) := by
    calc
      Real.log (T + 3) <= Real.log ((T + 2) ^ 2) :=
        Real.strictMonoOn_log.monotoneOn
          (by show 0 < T + 3; linarith)
          (pow_pos (show 0 < T + 2 by linarith) 2) hArgument
      _ = 2 * Real.log (T + 2) := by
        rw [Real.log_pow]
        norm_num
  have hScale :
      xiDyadicLogLinearConstant * (T + 1) * Real.log (T + 3) <=
        4 * xiDyadicLogLinearConstant * T * Real.log (T + 2) := by
    have hCNonnegative := xiDyadicLogLinearConstant_nonnegative
    calc
      xiDyadicLogLinearConstant * (T + 1) * Real.log (T + 3) <=
          xiDyadicLogLinearConstant * (2 * T) *
            (2 * Real.log (T + 2)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (by linarith) hCNonnegative)
          hLogArgument
          (Real.log_nonneg (by linarith))
          (mul_nonneg hCNonnegative (by linarith))
      _ = 4 * xiDyadicLogLinearConstant * T * Real.log (T + 2) := by
        ring
  calc
    (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
        (TS274.Goldbach.finiteJensenMultiplicityCount
          (xiDyadicDiskData (T + 1) hPos) : Real) := hNatReal
    _ <= xiDyadicLogLinearConstant * (T + 1) * Real.log (T + 3) := by
      simpa [show T + 1 + 2 = T + 3 by ring] using hXi
    _ <= 4 * xiDyadicLogLinearConstant * T * Real.log (T + 2) := hScale
    _ = xiGlobalLogLinearConstant * T * Real.log (T + 2) := by
      rfl

noncomputable def xiLargeHeightLogLinearMultiplicityCountEstimate :
    TS273.Goldbach.LargeHeightLogLinearMultiplicityCountEstimate where
  C := xiGlobalLogLinearConstant
  C_nonnegative := xiGlobalLogLinearConstant_nonnegative
  multiplicity_count_le := concreteMultiplicityCountUpToHeight_le_logLinear

/-- The first unconditional log-linear realization of the TS270 global
multiplicity-counting contract. -/
noncomputable def xiGlobalMultiplicityCountingBoundContract :
    TS270.Goldbach.GlobalMultiplicityCountingBoundContract
      (TS273.Goldbach.logLinearMultiplicityCountEnvelope
        xiGlobalLogLinearConstant) :=
  TS273.Goldbach.largeHeightLogLinearEstimate_implies_globalContract
    xiLargeHeightLogLinearMultiplicityCountEstimate

structure RiemannXiLogLinearZeroCountingLedger where
  ts289_closed_growth : TS289.Goldbach.CompletedZetaThetaIntegralClosedBoundLedger
  zeta_xi_zero_bridge :
    forall rho : Complex,
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho ->
        TS282.Goldbach.riemannXiCandidate rho = 0
  zeta_xi_multiplicity_bridge :
    forall rho : Complex,
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho ->
        TS264.Goldbach.concreteRiemannZetaMultiplicity rho =
          TS284.Goldbach.riemannXiCandidateMultiplicity rho
  global_log_linear_contract :
    TS270.Goldbach.GlobalMultiplicityCountingBoundContract
      (TS273.Goldbach.logLinearMultiplicityCountEnvelope
        xiGlobalLogLinearConstant)
  riemann_von_mangoldt_asymptotic_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def riemannXiLogLinearZeroCountingLedger :
    RiemannXiLogLinearZeroCountingLedger where
  ts289_closed_growth :=
    TS289.Goldbach.completedZetaThetaIntegralClosedBoundLedger
  zeta_xi_zero_bridge := fun _ hZero =>
    concreteNontrivialRiemannZetaZero_is_xi_zero hZero
  zeta_xi_multiplicity_bridge := fun _ hZero =>
    concreteRiemannZetaMultiplicity_eq_riemannXiCandidateMultiplicity hZero
  global_log_linear_contract := xiGlobalMultiplicityCountingBoundContract
  riemann_von_mangoldt_asymptotic_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def RiemannXiLogLinearZeroCountingTarget : Prop :=
  Nonempty RiemannXiLogLinearZeroCountingLedger

theorem riemannXiLogLinearZeroCountingTarget :
    RiemannXiLogLinearZeroCountingTarget :=
  Nonempty.intro riemannXiLogLinearZeroCountingLedger

end Goldbach
end TS290
