import Mathlib.Tactic
import TS.Goldbach.Strong.TS283.RiemannXiFiniteZeroGeometry

/-!
# TS284 - Riemann Xi Multiplicity and Local Normal Form

TS283 constructed exact finite xi-zero geometry and a zero-free buffered
collar.  This sprint enriches that geometry with the canonical analytic
multiplicity and the local normal form required by the TS282 xi factorization
specification.

The multiplicity at `rho` is the natural value of `AnalyticAt.order`.  The
order is never top because TS283 proved that xi is not locally zero anywhere,
and it is nonzero at every selected xi zero.  Mathlib's
`AnalyticAt.order_eq_nat_iff` then supplies the analytic nonvanishing local
factor and the exact eventual factorization.

The resulting `xiFiniteZeroFactorizationSpec` is a genuine TS282 specification
for every positive inner radius.  This module does not assemble the global
analytic quotient, prove effective xi growth, prove a zero-counting estimate,
prove the explicit formula, prove Gallagher, close an OTSA bridge, or claim
Goldbach.
-/

noncomputable section

namespace TS284
namespace Goldbach

open Complex Metric Set Topology Filter

/-- Canonical natural analytic multiplicity of the xi candidate. -/
noncomputable def riemannXiCandidateMultiplicity
    (rho : Complex) : Nat :=
  (TS282.Goldbach.riemannXiCandidate_analyticAt rho).order.toNat

/-- The xi-candidate order is finite at every point. -/
theorem riemannXiCandidate_order_ne_top
    (rho : Complex) :
    Not ((TS282.Goldbach.riemannXiCandidate_analyticAt rho).order = Top.top) := by
  intro hTop
  have hLocalZero :
      Filter.Eventually
        (fun z => TS282.Goldbach.riemannXiCandidate z = 0)
        (nhds rho) :=
    (AnalyticAt.order_eq_top_iff
      (TS282.Goldbach.riemannXiCandidate_analyticAt rho)).mp hTop
  exact TS283.Goldbach.riemannXiCandidate_not_eventually_zero rho hLocalZero

/-- The analytic order cannot be zero at an actual xi zero. -/
theorem riemannXiCandidate_order_ne_zero
    {rho : Complex}
    (hZero : TS282.Goldbach.riemannXiCandidate rho = 0) :
    Not ((TS282.Goldbach.riemannXiCandidate_analyticAt rho).order = 0) := by
  intro hOrderZero
  let hf := TS282.Goldbach.riemannXiCandidate_analyticAt rho
  have hFactorExists :=
    (AnalyticAt.order_eq_nat_iff hf 0).mp (by simpa using hOrderZero)
  let g : Complex -> Complex := Classical.choose hFactorExists
  have hgSpec := Classical.choose_spec hFactorExists
  have hAt := mem_of_mem_nhds hgSpec.2.2
  apply hgSpec.2.1
  simpa [hZero, smul_eq_mul] using hAt.symm

/-- Every xi zero has strictly positive canonical multiplicity. -/
theorem riemannXiCandidateMultiplicity_positive
    {rho : Complex}
    (hZero : TS282.Goldbach.riemannXiCandidate rho = 0) :
    0 < riemannXiCandidateMultiplicity rho := by
  unfold riemannXiCandidateMultiplicity
  apply Nat.pos_of_ne_zero
  intro hNatZero
  have hCases := ENat.toNat_eq_zero.mp hNatZero
  exact hCases.elim
    (riemannXiCandidate_order_ne_zero hZero)
    (riemannXiCandidate_order_ne_top rho)

/-- Coercing the canonical multiplicity recovers the analytic order. -/
theorem riemannXiCandidateMultiplicity_coe_eq_order
    (rho : Complex) :
    (riemannXiCandidateMultiplicity rho : ENat) =
      (TS282.Goldbach.riemannXiCandidate_analyticAt rho).order := by
  unfold riemannXiCandidateMultiplicity
  exact ENat.coe_toNat (riemannXiCandidate_order_ne_top rho)

/-- Exact local analytic normal form at every point. -/
theorem riemannXiCandidate_local_normal_form
    (rho : Complex) :
    Exists fun h : Complex -> Complex =>
      AnalyticAt Complex h rho /\
      Not (h rho = 0) /\
      Filter.Eventually
        (fun z =>
          TS282.Goldbach.riemannXiCandidate z =
            (z - rho) ^ riemannXiCandidateMultiplicity rho * h z)
        (nhds rho) := by
  let hf := TS282.Goldbach.riemannXiCandidate_analyticAt rho
  have hOrder :
      hf.order = (riemannXiCandidateMultiplicity rho : ENat) :=
    (riemannXiCandidateMultiplicity_coe_eq_order rho).symm
  simpa [smul_eq_mul] using
    (AnalyticAt.order_eq_nat_iff
      hf (riemannXiCandidateMultiplicity rho)).mp hOrder

namespace XiFiniteZeroGeometryData

/-- Every selected factor zero lies in the analytic closed ball. -/
theorem factor_zero_mem_analyticClosedBall
    (G : TS283.Goldbach.XiFiniteZeroGeometryData)
    (rho : Complex)
    (hRho : Membership.mem G.factorZeros rho) :
    Membership.mem
      (Metric.closedBall G.config.center G.config.analyticRadius) rho := by
  rw [G.config.mem_closedBall_iff_abs_sub]
  exact (G.factor_zero_mem_open_disk rho hRho).le.trans
    G.config.averagingRadius_lt_analyticRadius.le

/-- Every selected factor point is an actual xi zero. -/
theorem factor_zero_is_xi_zero
    (G : TS283.Goldbach.XiFiniteZeroGeometryData)
    (rho : Complex)
    (hRho : Membership.mem G.factorZeros rho) :
    TS282.Goldbach.riemannXiCandidate rho = 0 :=
  (G.factor_zero_iff rho
    (factor_zero_mem_analyticClosedBall G rho hRho)).mpr hRho

end XiFiniteZeroGeometryData

/-- TS283 geometry enriched to the complete finite xi-zero specification. -/
noncomputable def xiFiniteZeroFactorizationSpec
    (r : Real)
    (hr : 0 < r) : TS282.Goldbach.XiFiniteZeroFactorizationSpec := by
  let G := TS283.Goldbach.xiFiniteZeroGeometryData r hr
  exact
    { config := G.config
      innerZeros := G.innerZeros
      factorZeros := G.factorZeros
      multiplicity := riemannXiCandidateMultiplicity
      center_eq_zero := G.center_eq_zero
      innerZeros_subset_factorZeros := G.innerZeros_subset_factorZeros
      inner_zero_mem_disk := G.inner_zero_mem_disk
      factor_zero_mem_open_disk := G.factor_zero_mem_open_disk
      multiplicity_positive := by
        intro rho hRho
        exact riemannXiCandidateMultiplicity_positive
          (XiFiniteZeroGeometryData.factor_zero_is_xi_zero G rho hRho)
      factor_zero_iff := G.factor_zero_iff
      local_normal_form := by
        intro rho _
        exact riemannXiCandidate_local_normal_form rho }

@[simp]
theorem xiFiniteZeroFactorizationSpec_innerRadius
    (r : Real)
    (hr : 0 < r) :
    (xiFiniteZeroFactorizationSpec r hr).config.innerRadius = r :=
  rfl

/-- Existence facade for a complete finite xi-zero specification. -/
theorem exists_xiFiniteZeroFactorizationSpec
    (r : Real)
    (hr : 0 < r) :
    Exists fun S : TS282.Goldbach.XiFiniteZeroFactorizationSpec =>
      S.config.innerRadius = r :=
  Exists.intro (xiFiniteZeroFactorizationSpec r hr) rfl

structure RiemannXiMultiplicityAndLocalNormalFormLedger where
  ts283_geometry : TS283.Goldbach.RiemannXiFiniteZeroGeometryLedger
  multiplicity_positive_at_zeros :
    forall rho : Complex,
      TS282.Goldbach.riemannXiCandidate rho = 0 ->
        0 < riemannXiCandidateMultiplicity rho
  local_normal_form_at_zeros :
    forall rho : Complex,
      TS282.Goldbach.riemannXiCandidate rho = 0 ->
        Exists fun h : Complex -> Complex =>
          AnalyticAt Complex h rho /\
          Not (h rho = 0) /\
          Filter.Eventually
            (fun z =>
              TS282.Goldbach.riemannXiCandidate z =
                (z - rho) ^ riemannXiCandidateMultiplicity rho * h z)
            (nhds rho)
  positive_inner_radius_specification :
    forall r : Real,
      0 < r ->
        Exists fun S : TS282.Goldbach.XiFiniteZeroFactorizationSpec =>
          S.config.innerRadius = r
  quotient_not_constructed : True
  effective_xi_growth_not_proved : True
  zero_counting_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def riemannXiMultiplicityAndLocalNormalFormLedger :
    RiemannXiMultiplicityAndLocalNormalFormLedger where
  ts283_geometry := TS283.Goldbach.riemannXiFiniteZeroGeometryLedger
  multiplicity_positive_at_zeros :=
    fun _ hZero => riemannXiCandidateMultiplicity_positive hZero
  local_normal_form_at_zeros :=
    fun rho _ => riemannXiCandidate_local_normal_form rho
  positive_inner_radius_specification :=
    exists_xiFiniteZeroFactorizationSpec
  quotient_not_constructed := True.intro
  effective_xi_growth_not_proved := True.intro
  zero_counting_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def RiemannXiMultiplicityAndLocalNormalFormTarget : Prop :=
  Nonempty RiemannXiMultiplicityAndLocalNormalFormLedger

theorem riemannXiMultiplicityAndLocalNormalFormTarget :
    RiemannXiMultiplicityAndLocalNormalFormTarget :=
  Nonempty.intro riemannXiMultiplicityAndLocalNormalFormLedger

end Goldbach
end TS284
