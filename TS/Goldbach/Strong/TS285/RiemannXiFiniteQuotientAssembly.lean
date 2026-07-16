import Mathlib.Tactic
import TS.Goldbach.Strong.TS284.RiemannXiMultiplicityAndLocalNormalForm

/-!
# TS285 - Riemann Xi Finite Quotient Assembly

TS284 constructed the complete finite xi-zero specification, including exact
analytic multiplicities and local normal forms.  This sprint constructs the
global finite quotient needed by TS282.

Away from the finite root set, the quotient is `xi / P`.  At a selected root
`rho`, it is defined by the chosen local analytic factor divided by the product
of all factors other than `rho`.  The complementary product is nonzero near
`rho`, and the local normal form proves that the two quotient expressions
agree in a neighborhood.  This gives an analytic quotient on the whole
buffered disk, the exact factorization `xi = P * quotient`, and nonvanishing
throughout that disk.

The resulting TS282 buffered construction receives the canonical TS280 Jensen
boundary estimate and multiplicity-count bound.  This module does not prove an
effective xi growth bound, a quantitative zero-counting estimate, the explicit
formula, Gallagher, an OTSA bridge, or Goldbach.
-/

noncomputable section

namespace TS285
namespace Goldbach

open Complex Metric Set Topology Filter

/-- Chosen local factor supplied by a TS282 specification at each root. -/
noncomputable def xiSpecLocalFactor
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho : Complex) : Complex -> Complex :=
  if hRho : Membership.mem S.factorZeros rho then
    Classical.choose (S.local_normal_form rho hRho)
  else
    fun _ => 1

theorem xiSpecLocalFactor_analyticAt
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    AnalyticAt Complex (xiSpecLocalFactor S rho) rho := by
  unfold xiSpecLocalFactor
  rw [dif_pos hRho]
  exact (Classical.choose_spec (S.local_normal_form rho hRho)).1

theorem xiSpecLocalFactor_ne_zero
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    Not (xiSpecLocalFactor S rho rho = 0) := by
  unfold xiSpecLocalFactor
  rw [dif_pos hRho]
  exact (Classical.choose_spec (S.local_normal_form rho hRho)).2.1

theorem riemannXiCandidate_eventuallyEq_specLocalFactor
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    Filter.Eventually
      (fun z =>
        TS282.Goldbach.riemannXiCandidate z =
          (z - rho) ^ S.multiplicity rho * xiSpecLocalFactor S rho z)
      (nhds rho) := by
  unfold xiSpecLocalFactor
  rw [dif_pos hRho]
  exact (Classical.choose_spec (S.local_normal_form rho hRho)).2.2

/-- Product of all selected xi factors except the one at `rho`. -/
noncomputable def xiComplementaryZeroPolynomial
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho z : Complex) : Complex :=
  Finset.prod (S.factorZeros.erase rho)
    (fun a => (z - a) ^ S.multiplicity a)

theorem xiComplementaryZeroPolynomial_analyticAt
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho z : Complex) :
    AnalyticAt Complex (xiComplementaryZeroPolynomial S rho) z := by
  classical
  unfold xiComplementaryZeroPolynomial
  apply Finset.analyticAt_prod
  intro a _
  exact (analyticAt_id.sub analyticAt_const).pow _

theorem xiComplementaryZeroPolynomial_ne_zero_of_avoids
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho z : Complex)
    (hAvoid :
      forall a : Complex,
        Membership.mem (S.factorZeros.erase rho) a -> Not (z = a)) :
    Not (xiComplementaryZeroPolynomial S rho z = 0) := by
  classical
  unfold xiComplementaryZeroPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  exact pow_ne_zero _ (sub_ne_zero.mpr (hAvoid a ha))

theorem xiComplementaryZeroPolynomial_ne_zero_at_root
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho : Complex) :
    Not (xiComplementaryZeroPolynomial S rho rho = 0) := by
  apply xiComplementaryZeroPolynomial_ne_zero_of_avoids
  intro a ha hEq
  have haNe : Not (a = rho) := (Finset.mem_erase.mp ha).1
  exact haNe hEq.symm

theorem finiteJensenZeroPolynomial_eq_factor_mul_complement
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho z : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    TS275.Goldbach.finiteJensenZeroPolynomial
        S.toJensenFactorZeroData z =
      (z - rho) ^ S.multiplicity rho *
        xiComplementaryZeroPolynomial S rho z := by
  classical
  unfold TS275.Goldbach.finiteJensenZeroPolynomial
  unfold xiComplementaryZeroPolynomial
  exact (Finset.mul_prod_erase S.factorZeros
    (fun a => (z - a) ^ S.multiplicity a) hRho).symm

/-- Analytic local model for the quotient at a selected root. -/
noncomputable def xiRootLocalQuotient
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho z : Complex) : Complex :=
  xiSpecLocalFactor S rho z /
    xiComplementaryZeroPolynomial S rho z

theorem xiRootLocalQuotient_analyticAt
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    AnalyticAt Complex (xiRootLocalQuotient S rho) rho := by
  exact (xiSpecLocalFactor_analyticAt S rho hRho).div
    (xiComplementaryZeroPolynomial_analyticAt S rho rho)
    (xiComplementaryZeroPolynomial_ne_zero_at_root S rho)

theorem xiRootLocalQuotient_ne_zero
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    Not (xiRootLocalQuotient S rho rho = 0) := by
  unfold xiRootLocalQuotient
  exact div_ne_zero
    (xiSpecLocalFactor_ne_zero S rho hRho)
    (xiComplementaryZeroPolynomial_ne_zero_at_root S rho)

/-- Global finite quotient, with removable values filled at selected roots. -/
noncomputable def riemannXiFiniteQuotient
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (z : Complex) : Complex :=
  if Membership.mem S.factorZeros z then
    xiRootLocalQuotient S z z
  else
    TS282.Goldbach.riemannXiCandidate z /
      TS275.Goldbach.finiteJensenZeroPolynomial S.toJensenFactorZeroData z

theorem xiRootLocalQuotient_eventuallyEq_finiteQuotient
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (rho : Complex)
    (hRho : Membership.mem S.factorZeros rho) :
    Filter.EventuallyEq
      (nhds rho)
      (xiRootLocalQuotient S rho)
      (riemannXiFiniteQuotient S) := by
  have hAvoidOther :
      Membership.mem
        (nhds rho)
        ((S.factorZeros.erase rho : Set Complex).compl) :=
    (S.factorZeros.erase rho).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards
    [riemannXiCandidate_eventuallyEq_specLocalFactor S rho hRho, hAvoidOther]
      with z hFactor hAvoid
  by_cases hzEq : z = rho
  case pos =>
    subst z
    simp [riemannXiFiniteQuotient, xiRootLocalQuotient, hRho]
  case neg =>
    have hzNotRoot : Not (Membership.mem S.factorZeros z) := by
      intro hzRoot
      apply hAvoid
      exact Finset.mem_erase.mpr (And.intro hzEq hzRoot)
    have hComplementNe :
        Not (xiComplementaryZeroPolynomial S rho z = 0) := by
      apply xiComplementaryZeroPolynomial_ne_zero_of_avoids
      intro a ha hza
      apply hAvoid
      rw [hza]
      exact ha
    have hPowerNe :
        Not ((z - rho) ^ S.multiplicity rho = 0) :=
      pow_ne_zero _ (sub_ne_zero.mpr hzEq)
    rw [riemannXiFiniteQuotient, if_neg hzNotRoot]
    rw [xiRootLocalQuotient, hFactor]
    rw [finiteJensenZeroPolynomial_eq_factor_mul_complement
      S rho z hRho]
    field_simp [hPowerNe, hComplementNe]
    ring

theorem riemannXiFiniteQuotient_analyticAt
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (z : Complex) :
    AnalyticAt Complex (riemannXiFiniteQuotient S) z := by
  by_cases hRoot : Membership.mem S.factorZeros z
  case pos =>
    exact (xiRootLocalQuotient_analyticAt S z hRoot).congr
      (xiRootLocalQuotient_eventuallyEq_finiteQuotient S z hRoot)
  case neg =>
    have hPolynomialNe :
        Not (TS275.Goldbach.finiteJensenZeroPolynomial
          S.toJensenFactorZeroData z = 0) := by
      intro hZero
      exact hRoot
        ((TS275.Goldbach.finiteJensenZeroPolynomial_eq_zero_iff
          S.toJensenFactorZeroData z).mp hZero)
    have hBase :
        AnalyticAt Complex
          (fun w =>
            TS282.Goldbach.riemannXiCandidate w /
              TS275.Goldbach.finiteJensenZeroPolynomial
                S.toJensenFactorZeroData w) z :=
      (TS282.Goldbach.riemannXiCandidate_analyticAt z).div
        (TS275.Goldbach.finiteJensenZeroPolynomial_analyticAt
          S.toJensenFactorZeroData z)
        hPolynomialNe
    have hAvoidRoots :
        Membership.mem (nhds z) ((S.factorZeros : Set Complex).compl) :=
      S.factorZeros.isClosed.isOpen_compl.mem_nhds (by simpa using hRoot)
    apply hBase.congr
    filter_upwards [hAvoidRoots] with w hw
    have hwNotRoot : Not (Membership.mem S.factorZeros w) := by
      simpa using hw
    simp [riemannXiFiniteQuotient, hwNotRoot]

theorem riemannXiFiniteQuotient_analyticOnNhd
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (u : Set Complex) :
    AnalyticOnNhd Complex (riemannXiFiniteQuotient S) u := by
  intro z _
  exact riemannXiFiniteQuotient_analyticAt S z

theorem riemannXiFiniteQuotient_factorization
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (z : Complex) :
    TS282.Goldbach.riemannXiCandidate z =
      TS275.Goldbach.finiteJensenZeroPolynomial
        S.toJensenFactorZeroData z * riemannXiFiniteQuotient S z := by
  by_cases hRoot : Membership.mem S.factorZeros z
  case pos =>
    have hXiZero : TS282.Goldbach.riemannXiCandidate z = 0 :=
      S.factor_zero_is_xi_zero z hRoot
    have hPolynomialZero :
        TS275.Goldbach.finiteJensenZeroPolynomial
          S.toJensenFactorZeroData z = 0 :=
      (TS275.Goldbach.finiteJensenZeroPolynomial_eq_zero_iff
        S.toJensenFactorZeroData z).mpr hRoot
    simp [hXiZero, hPolynomialZero]
  case neg =>
    have hPolynomialNe :
        Not (TS275.Goldbach.finiteJensenZeroPolynomial
          S.toJensenFactorZeroData z = 0) := by
      intro hZero
      exact hRoot
        ((TS275.Goldbach.finiteJensenZeroPolynomial_eq_zero_iff
          S.toJensenFactorZeroData z).mp hZero)
    rw [riemannXiFiniteQuotient, if_neg hRoot]
    field_simp

theorem riemannXiFiniteQuotient_nonzero_on_analyticClosedBall
    (S : TS282.Goldbach.XiFiniteZeroFactorizationSpec)
    (z : Complex)
    (hzBall : Membership.mem
      (Metric.closedBall S.config.center S.config.analyticRadius) z) :
    Not (riemannXiFiniteQuotient S z = 0) := by
  by_cases hRoot : Membership.mem S.factorZeros z
  case pos =>
    rw [riemannXiFiniteQuotient, if_pos hRoot]
    exact xiRootLocalQuotient_ne_zero S z hRoot
  case neg =>
    have hXiNe : Not (TS282.Goldbach.riemannXiCandidate z = 0) := by
      intro hXiZero
      exact hRoot ((S.factor_zero_iff z hzBall).mp hXiZero)
    have hPolynomialNe :
        Not (TS275.Goldbach.finiteJensenZeroPolynomial
          S.toJensenFactorZeroData z = 0) := by
      intro hZero
      exact hRoot
        ((TS275.Goldbach.finiteJensenZeroPolynomial_eq_zero_iff
          S.toJensenFactorZeroData z).mp hZero)
    rw [riemannXiFiniteQuotient, if_neg hRoot]
    exact div_ne_zero hXiNe hPolynomialNe

/-- Concrete TS282 quotient assembly for every positive inner radius. -/
noncomputable def xiBufferedQuotientAssembly
    (r : Real)
    (hr : 0 < r) :
    TS282.Goldbach.XiBufferedQuotientAssembly
      (TS284.Goldbach.xiFiniteZeroFactorizationSpec r hr) where
  quotient := riemannXiFiniteQuotient
    (TS284.Goldbach.xiFiniteZeroFactorizationSpec r hr)
  quotient_analytic := riemannXiFiniteQuotient_analyticOnNhd _ _
  factorization := by
    intro z _
    exact riemannXiFiniteQuotient_factorization _ z
  quotient_nonzero := by
    intro z hz
    exact riemannXiFiniteQuotient_nonzero_on_analyticClosedBall _ z hz

/-- First complete buffered Jensen construction for the xi candidate. -/
noncomputable def xiBufferedFactorizationConstruction
    (r : Real)
    (hr : 0 < r) :
    TS282.Goldbach.XiBufferedFactorizationConstruction where
  spec := TS284.Goldbach.xiFiniteZeroFactorizationSpec r hr
  assembly := xiBufferedQuotientAssembly r hr

/-- Three-radius configuration carried by the concrete xi construction. -/
noncomputable def xiJensenDiskConfiguration
    (r : Real)
    (hr : 0 < r) : TS275.Goldbach.JensenDiskConfiguration :=
  (xiBufferedFactorizationConstruction r hr).spec.config

/-- Finite Jensen disk data carried by the concrete xi construction. -/
noncomputable def xiJensenFactorZeroData
    (r : Real)
    (hr : 0 < r) : TS275.Goldbach.JensenFactorZeroData :=
  TS282.Goldbach.XiFiniteZeroFactorizationSpec.toJensenFactorZeroData
    (xiBufferedFactorizationConstruction r hr).spec

/-- Inner TS275 data carried by the concrete xi construction. -/
noncomputable def xiJensenInnerZeroData
    (r : Real)
    (hr : 0 < r) : TS275.Goldbach.JensenInnerZeroData :=
  TS275.Goldbach.JensenFactorZeroData.toJensenInnerZeroData
    (xiJensenFactorZeroData r hr)

/-- Finite Jensen disk data carried by the concrete xi construction. -/
noncomputable def xiFiniteJensenDiskData
    (r : Real)
    (hr : 0 < r) : TS274.Goldbach.FiniteJensenDiskData :=
  TS275.Goldbach.JensenInnerZeroData.toFiniteJensenDiskData
    (xiJensenInnerZeroData r hr)

/-- Concrete TS275 buffered datum carried by the xi construction. -/
noncomputable def xiBufferedJensenFactorizationData
  (r : Real)
    (hr : 0 < r) : TS275.Goldbach.BufferedJensenFactorizationData :=
  TS282.Goldbach.XiBufferedFactorizationConstruction.toBufferedJensenFactorizationData
    (xiBufferedFactorizationConstruction r hr)

/-- Canonical finite Jensen boundary estimate for the xi candidate. -/
theorem riemannXi_finiteJensenBoundaryEstimate_canonical
    (r : Real)
    (hr : 0 < r) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      (xiFiniteJensenDiskData r hr)
      TS282.Goldbach.riemannXiCandidate
      (TS280.Goldbach.canonicalBoundaryNorm
        (xiBufferedJensenFactorizationData r hr)) := by
  simpa [xiFiniteJensenDiskData, xiBufferedJensenFactorizationData] using
    TS282.Goldbach.XiBufferedFactorizationConstruction.finiteJensenBoundaryEstimate_canonical
      (xiBufferedFactorizationConstruction r hr)

/-- Canonical finite multiplicity-count bound for the xi candidate. -/
theorem riemannXi_finiteJensenMultiplicityCount_le_canonical
    (r : Real)
    (hr : 0 < r) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        (xiFiniteJensenDiskData r hr) :
      Real) <=
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (TS280.Goldbach.canonicalBoundaryNorm
            (xiBufferedJensenFactorizationData r hr))
          (TS282.Goldbach.riemannXiCandidate
            (xiJensenDiskConfiguration r hr).center) /
        Real.log
          ((xiJensenDiskConfiguration r hr).averagingRadius /
            (xiJensenDiskConfiguration r hr).innerRadius) := by
  simpa [xiJensenDiskConfiguration] using
    TS282.Goldbach.XiBufferedFactorizationConstruction.finiteJensenMultiplicityCount_le_canonical
      (xiBufferedFactorizationConstruction r hr)

structure RiemannXiFiniteQuotientAssemblyLedger where
  ts284_local_forms :
    TS284.Goldbach.RiemannXiMultiplicityAndLocalNormalFormLedger
  positive_inner_radius_construction :
    forall r : Real,
      0 < r -> TS282.Goldbach.XiBufferedFactorizationConstruction
  quotient_entire :
    forall r : Real,
      forall hr : 0 < r,
        AnalyticOnNhd Complex
          (xiBufferedQuotientAssembly r hr).quotient Set.univ
  effective_xi_growth_not_proved : True
  quantitative_zero_counting_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def riemannXiFiniteQuotientAssemblyLedger :
    RiemannXiFiniteQuotientAssemblyLedger where
  ts284_local_forms :=
    TS284.Goldbach.riemannXiMultiplicityAndLocalNormalFormLedger
  positive_inner_radius_construction := xiBufferedFactorizationConstruction
  quotient_entire := by
    intro r hr
    exact riemannXiFiniteQuotient_analyticOnNhd
      (TS284.Goldbach.xiFiniteZeroFactorizationSpec r hr) Set.univ
  effective_xi_growth_not_proved := True.intro
  quantitative_zero_counting_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def RiemannXiFiniteQuotientAssemblyTarget : Prop :=
  Nonempty RiemannXiFiniteQuotientAssemblyLedger

theorem riemannXiFiniteQuotientAssemblyTarget :
    RiemannXiFiniteQuotientAssemblyTarget :=
  Nonempty.intro riemannXiFiniteQuotientAssemblyLedger

end Goldbach
end TS285
