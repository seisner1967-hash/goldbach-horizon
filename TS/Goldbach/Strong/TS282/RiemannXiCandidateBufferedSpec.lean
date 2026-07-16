import Mathlib.Tactic
import TS.Goldbach.Strong.TS281.PolynomialBufferedJensenRealization
import TS.Goldbach.Strong.TS282.CompletedRiemannZetaZeroBridge

/-!
# TS282 - Riemann Xi Candidate and Buffered Specification

Mathlib's entire `completedRiemannZetaZero` is an additive regularization of
the completed zeta function; it is not Riemann xi and does not have the zeta
zeros.  The affine twist

`(s * (s - 1) * completedRiemannZetaZero s + 1) / 2`

is entire and agrees away from `0` and `1` with
`s * (s - 1) * completedRiemannZeta s / 2`, the standard xi normalization.

This sprint proves entirety, the values at `0` and `1`, and the functional
equation.  It also gives a geometrically exact finite-zero specification and
an exact quotient-assembly interface.  Any supplied assembly becomes a real
TS275 buffered factorization and therefore receives the complete canonical
TS280 Jensen estimate.

Finiteness of xi zeros on compact disks, local normal forms, quotient
assembly, the xi/zeta zero correspondence, effective xi growth, zero
counting, the explicit formula, Gallagher, OTSA, and Goldbach remain open.
-/

noncomputable section

namespace TS282
namespace Goldbach

open Complex Metric Set Topology Filter

/-- Entire affine twist of Mathlib's regularized completed zeta function. -/
noncomputable def riemannXiCandidate (s : Complex) : Complex :=
  (s * (s - 1) * completedRiemannZetaZero s + 1) / 2

theorem riemannXiCandidate_entire :
    Differentiable Complex riemannXiCandidate := by
  show Differentiable Complex fun s =>
    (s * (s - 1) * completedRiemannZetaZero s + 1) / 2
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedRiemannZetaZero).add_const 1).div_const 2

theorem riemannXiCandidate_analyticAt (s : Complex) :
    AnalyticAt Complex riemannXiCandidate s := by
  apply riemannXiCandidate_entire.differentiableOn.analyticAt
  exact univ_mem

theorem riemannXiCandidate_analyticOnNhd (u : Set Complex) :
    AnalyticOnNhd Complex riemannXiCandidate u := by
  intro s _
  exact riemannXiCandidate_analyticAt s

/-- The value at zero proves in particular that xi is not identically zero. -/
theorem riemannXiCandidate_zero :
    riemannXiCandidate 0 = (1 : Complex) / 2 := by
  simp [riemannXiCandidate]

theorem riemannXiCandidate_one :
    riemannXiCandidate 1 = (1 : Complex) / 2 := by
  simp [riemannXiCandidate]

theorem riemannXiCandidate_zero_ne_zero :
    Not (riemannXiCandidate 0 = 0) := by
  rw [riemannXiCandidate_zero]
  norm_num

theorem riemannXiCandidate_one_sub (s : Complex) :
    riemannXiCandidate (1 - s) = riemannXiCandidate s := by
  unfold riemannXiCandidate
  rw [completedRiemannZetaZero_one_sub]
  congr 1
  ring

/-- Away from the removable endpoints, the candidate is standard xi. -/
theorem riemannXiCandidate_eq_completedRiemannZeta_mul
    {s : Complex}
    (hs0 : Not (s = 0))
    (hs1 : Not (s = 1)) :
    riemannXiCandidate s =
      s * (s - 1) / 2 * completedRiemannZeta s := by
  have hOneSub : Not (1 - s = 0) := sub_ne_zero.mpr (Ne.symm hs1)
  rw [riemannXiCandidate, completedRiemannZeta_eq_zero_regularization]
  field_simp [hs0, hOneSub]
  ring

/-- Exact finite zero and local-order data required before quotient assembly. -/
structure XiFiniteZeroFactorizationSpec where
  config : TS275.Goldbach.JensenDiskConfiguration
  innerZeros : Finset Complex
  factorZeros : Finset Complex
  multiplicity : Complex -> Nat

  center_eq_zero : config.center = 0

  innerZeros_subset_factorZeros : innerZeros <= factorZeros

  inner_zero_mem_disk :
    forall rho : Complex,
      Membership.mem innerZeros rho ->
        Complex.abs (rho - config.center) <= config.innerRadius

  factor_zero_mem_open_disk :
    forall rho : Complex,
      Membership.mem factorZeros rho ->
        Complex.abs (rho - config.center) < config.averagingRadius

  multiplicity_positive :
    forall rho : Complex,
      Membership.mem factorZeros rho ->
        0 < multiplicity rho

  factor_zero_iff :
    forall z : Complex,
      Membership.mem
          (Metric.closedBall config.center config.analyticRadius) z ->
        (riemannXiCandidate z = 0 <-> Membership.mem factorZeros z)

  local_normal_form :
    forall rho : Complex,
      Membership.mem factorZeros rho ->
        Exists fun h : Complex -> Complex =>
          AnalyticAt Complex h rho /\
          Not (h rho = 0) /\
          Filter.Eventually
            (fun z =>
              riemannXiCandidate z =
                (z - rho) ^ multiplicity rho * h z)
            (nhds rho)

namespace XiFiniteZeroFactorizationSpec

theorem factor_zero_mem_analyticClosedBall
    (S : XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    Membership.mem
      (Metric.closedBall S.config.center S.config.analyticRadius) rho := by
  rw [S.config.mem_closedBall_iff_abs_sub]
  exact (S.factor_zero_mem_open_disk rho hRho).le.trans
    S.config.averagingRadius_lt_analyticRadius.le

theorem factor_zero_is_xi_zero
    (S : XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    riemannXiCandidate rho = 0 :=
  (S.factor_zero_iff rho
    (S.factor_zero_mem_analyticClosedBall rho hRho)).mpr hRho

theorem factor_zero_ne_center
    (S : XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    Not (rho = S.config.center) := by
  intro hEq
  have hZero := S.factor_zero_is_xi_zero rho hRho
  rw [hEq, S.center_eq_zero, riemannXiCandidate_zero] at hZero
  norm_num at hZero

/-- Exact conversion of the xi zero specification to TS275 zero data. -/
noncomputable def toJensenFactorZeroData
    (S : XiFiniteZeroFactorizationSpec) :
    TS275.Goldbach.JensenFactorZeroData where
  config := S.config
  innerZeros := S.innerZeros
  innerMultiplicity := S.multiplicity
  inner_zero_ne_center := by
    intro rho hRho
    exact S.factor_zero_ne_center rho
      (S.innerZeros_subset_factorZeros hRho)
  inner_zero_mem_disk := S.inner_zero_mem_disk
  factorZeros := S.factorZeros
  factorMultiplicity := S.multiplicity
  factor_zero_ne_center := S.factor_zero_ne_center
  factor_zero_mem_open_disk := S.factor_zero_mem_open_disk
  innerZeros_subset_factorZeros := S.innerZeros_subset_factorZeros
  multiplicity_agrees := by
    intro rho _
    rfl
  factorMultiplicity_positive := S.multiplicity_positive

end XiFiniteZeroFactorizationSpec

/-- The one remaining assembly object: an analytic nonvanishing quotient. -/
structure XiBufferedQuotientAssembly
    (S : XiFiniteZeroFactorizationSpec) where
  quotient : Complex -> Complex

  quotient_analytic :
    AnalyticOnNhd Complex quotient
      (Metric.closedBall S.config.center S.config.analyticRadius)

  factorization :
    forall z : Complex,
      Membership.mem
          (Metric.closedBall S.config.center S.config.analyticRadius) z ->
        riemannXiCandidate z =
          TS275.Goldbach.finiteJensenZeroPolynomial
            S.toJensenFactorZeroData z * quotient z

  quotient_nonzero :
    forall z : Complex,
      Membership.mem
          (Metric.closedBall S.config.center S.config.analyticRadius) z ->
        Not (quotient z = 0)

namespace XiBufferedQuotientAssembly

/-- A supplied quotient assembly is a genuine TS275 buffered datum. -/
noncomputable def toBufferedJensenFactorizationData
    {S : XiFiniteZeroFactorizationSpec}
    (A : XiBufferedQuotientAssembly S) :
    TS275.Goldbach.BufferedJensenFactorizationData where
  zeroData := S.toJensenFactorZeroData
  f := riemannXiCandidate
  g := A.quotient
  f_analytic := riemannXiCandidate_analyticOnNhd _
  g_analytic := A.quotient_analytic
  factorization := A.factorization
  g_nonzero := A.quotient_nonzero

end XiBufferedQuotientAssembly

/-- Complete finite buffered construction package for the xi candidate. -/
structure XiBufferedFactorizationConstruction where
  spec : XiFiniteZeroFactorizationSpec
  assembly : XiBufferedQuotientAssembly spec

namespace XiBufferedFactorizationConstruction

noncomputable def toBufferedJensenFactorizationData
    (C : XiBufferedFactorizationConstruction) :
    TS275.Goldbach.BufferedJensenFactorizationData :=
  C.assembly.toBufferedJensenFactorizationData

/-- Any completed xi assembly receives the full TS280 Jensen estimate. -/
theorem finiteJensenBoundaryEstimate_canonical
    (C : XiBufferedFactorizationConstruction) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      C.spec.toJensenFactorZeroData.toJensenInnerZeroData.toFiniteJensenDiskData
      riemannXiCandidate
      (TS280.Goldbach.canonicalBoundaryNorm
        C.toBufferedJensenFactorizationData) := by
  simpa [toBufferedJensenFactorizationData,
    XiBufferedQuotientAssembly.toBufferedJensenFactorizationData] using
    TS280.Goldbach.finiteJensenBoundaryEstimate_canonical
      C.toBufferedJensenFactorizationData

/-- Direct multiplicity-count facade for every completed xi assembly. -/
theorem finiteJensenMultiplicityCount_le_canonical
    (C : XiBufferedFactorizationConstruction) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        C.spec.toJensenFactorZeroData.toJensenInnerZeroData.toFiniteJensenDiskData :
      Real) <=
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (TS280.Goldbach.canonicalBoundaryNorm
            C.toBufferedJensenFactorizationData)
          (riemannXiCandidate C.spec.config.center) /
        Real.log
          (C.spec.config.averagingRadius / C.spec.config.innerRadius) := by
  simpa [toBufferedJensenFactorizationData,
    XiBufferedQuotientAssembly.toBufferedJensenFactorizationData] using
    TS280.Goldbach.finiteJensenMultiplicityCount_le_canonical
      C.toBufferedJensenFactorizationData

end XiBufferedFactorizationConstruction

structure RiemannXiCandidateBufferedSpecLedger where
  ts281_polynomial_realization :
    TS281.Goldbach.PolynomialBufferedJensenRealizationLedger

  xi_candidate : Complex -> Complex
  xi_candidate_eq : xi_candidate = riemannXiCandidate
  xi_entire : Differentiable Complex xi_candidate
  xi_zero_value : xi_candidate 0 = (1 : Complex) / 2
  xi_one_value : xi_candidate 1 = (1 : Complex) / 2
  xi_functional_equation :
    forall s : Complex, xi_candidate (1 - s) = xi_candidate s

  zero_spec_to_ts275 :
    XiFiniteZeroFactorizationSpec ->
      TS275.Goldbach.JensenFactorZeroData

  quotient_assembly_to_ts275 :
    forall S : XiFiniteZeroFactorizationSpec,
      XiBufferedQuotientAssembly S ->
        TS275.Goldbach.BufferedJensenFactorizationData

  xi_finite_zeros_not_constructed : True
  xi_local_normal_forms_not_constructed : True
  xi_zero_free_collar_not_constructed : True
  xi_quotient_assembly_not_constructed : True
  xi_zeta_zero_bridge_not_proved : True
  effective_xi_growth_not_proved : True
  zero_counting_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def riemannXiCandidateBufferedSpecLedger :
    RiemannXiCandidateBufferedSpecLedger where
  ts281_polynomial_realization :=
    TS281.Goldbach.polynomialBufferedJensenRealizationLedger
  xi_candidate := riemannXiCandidate
  xi_candidate_eq := rfl
  xi_entire := riemannXiCandidate_entire
  xi_zero_value := riemannXiCandidate_zero
  xi_one_value := riemannXiCandidate_one
  xi_functional_equation := riemannXiCandidate_one_sub
  zero_spec_to_ts275 := XiFiniteZeroFactorizationSpec.toJensenFactorZeroData
  quotient_assembly_to_ts275 :=
    fun _ A => A.toBufferedJensenFactorizationData
  xi_finite_zeros_not_constructed := True.intro
  xi_local_normal_forms_not_constructed := True.intro
  xi_zero_free_collar_not_constructed := True.intro
  xi_quotient_assembly_not_constructed := True.intro
  xi_zeta_zero_bridge_not_proved := True.intro
  effective_xi_growth_not_proved := True.intro
  zero_counting_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def RiemannXiCandidateBufferedSpecTarget : Prop :=
  Nonempty RiemannXiCandidateBufferedSpecLedger

theorem riemannXiCandidateBufferedSpecTarget :
    RiemannXiCandidateBufferedSpecTarget :=
  Nonempty.intro riemannXiCandidateBufferedSpecLedger

end Goldbach
end TS282
