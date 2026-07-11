import Mathlib.Tactic
import TS.Goldbach.Strong.TS263.RiemannZetaSchwarzReflection

/-!
# TS264 - Concrete Riemann Zeta Zero Family Realization

TS263 closed Schwarz reflection and the conjugation route for every abstract
TS185 zero-family contract.  This sprint constructs that contract for the
actual nontrivial zeros of Mathlib's `riemannZeta`.

The multiplicity is the natural value of `AnalyticAt.order`.  The order is
proved finite by analytic uniqueness on the punctured plane and nonzero by
the local factorization at an actual zero.  Schwarz reflection supplies
conjugation closure, while `riemannZeta_one_sub` supplies the symmetry about
one half.  These facts assemble a concrete TS260 realization and make every
future valid TS256 truncation real without a floating multiplicity premise.

No exact zero enumeration, concrete finite truncation, global zero
summability, explicit formula, analytic bound, Gallagher estimate, or
Goldbach statement is proved.
-/

namespace TS264
namespace Goldbach

open Filter Set

def concreteNontrivialRiemannZetaZeroSet : Set Complex :=
  TS185.Goldbach.nontrivialRiemannZetaZeroPredicate

theorem concreteZero_is_zeta_zero
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    riemannZeta rho = 0 := by
  simpa [concreteNontrivialRiemannZetaZeroSet,
    TS185.Goldbach.nontrivialRiemannZetaZeroPredicate,
    TS185.Goldbach.riemannZetaZeroPredicate,
    TS185.Goldbach.mathlibRiemannZetaFunction] using hZero.1

theorem concreteZero_in_critical_strip
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    TS185.Goldbach.criticalStripPredicate rho := by
  exact hZero.2

theorem concreteZero_ne_one
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    Not (rho = 1) := by
  intro h
  have hStrip := concreteZero_in_critical_strip hZero
  unfold TS185.Goldbach.criticalStripPredicate at hStrip
  rw [h] at hStrip
  norm_num at hStrip

theorem concreteZero_ne_neg_nat
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho)
    (n : Nat) :
    Not (rho = -(n : Complex)) := by
  intro h
  have hStrip := concreteZero_in_critical_strip hZero
  unfold TS185.Goldbach.criticalStripPredicate at hStrip
  have hRe := congrArg Complex.re h
  simp at hRe
  have hNatNonneg : (0 : Real) <= n := Nat.cast_nonneg n
  linarith

theorem concreteRiemannZetaVanishingOrder_ne_top
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    (TS260.Goldbach.riemannZeta_analyticAt_of_ne_one
      rho (concreteZero_ne_one hZero)).order = Top.top -> False := by
  intro hTop
  let hf := TS260.Goldbach.riemannZeta_analyticAt_of_ne_one
    rho (concreteZero_ne_one hZero)
  have hLocalZero :
      Filter.Eventually (fun z => riemannZeta z = 0) (nhds rho) :=
    (AnalyticAt.order_eq_top_iff hf).mp hTop
  have hAnalyticOn :
      AnalyticOnNhd Complex riemannZeta TS263.Goldbach.zetaPuncturedDomain :=
    TS260.Goldbach.riemannZeta_differentiableOn_compl_one.analyticOnNhd
      isOpen_compl_singleton
  have hEqOn :
      Set.EqOn riemannZeta 0 TS263.Goldbach.zetaPuncturedDomain :=
    hAnalyticOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      TS263.Goldbach.zetaPuncturedDomain_isPreconnected
      (show TS263.Goldbach.zetaPuncturedDomain rho by
        simpa [TS263.Goldbach.zetaPuncturedDomain] using
          concreteZero_ne_one hZero)
      hLocalZero
  have hAtZero := hEqOn (show TS263.Goldbach.zetaPuncturedDomain 0 by
    change Not ((0 : Complex) = 1)
    norm_num)
  rw [riemannZeta_zero] at hAtZero
  norm_num at hAtZero

theorem concreteRiemannZetaVanishingOrder_ne_zero
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    (TS260.Goldbach.riemannZeta_analyticAt_of_ne_one
      rho (concreteZero_ne_one hZero)).order = 0 -> False := by
  intro hOrderZero
  let hf := TS260.Goldbach.riemannZeta_analyticAt_of_ne_one
    rho (concreteZero_ne_one hZero)
  have hFactorExists :=
    (AnalyticAt.order_eq_nat_iff hf 0).mp (by simpa using hOrderZero)
  let g : Complex -> Complex := Classical.choose hFactorExists
  have hgSpec := Classical.choose_spec hFactorExists
  have hAt := mem_of_mem_nhds hgSpec.2.2
  apply hgSpec.2.1
  have hZeta : riemannZeta rho = 0 := concreteZero_is_zeta_zero hZero
  simpa [hZeta, smul_eq_mul] using hAt.symm

noncomputable def concreteRiemannZetaMultiplicity
    (rho : Complex) : Nat := by
  classical
  exact
    if hZero : concreteNontrivialRiemannZetaZeroSet rho then
      (TS260.Goldbach.riemannZeta_analyticAt_of_ne_one
        rho (concreteZero_ne_one hZero)).order.toNat
    else
      0

theorem concreteRiemannZetaMultiplicity_positive
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    0 < concreteRiemannZetaMultiplicity rho := by
  unfold concreteRiemannZetaMultiplicity
  simp only [dif_pos hZero]
  apply Nat.pos_of_ne_zero
  intro hNatZero
  have hCases := ENat.toNat_eq_zero.mp hNatZero
  exact hCases.elim
    (concreteRiemannZetaVanishingOrder_ne_zero hZero)
    (concreteRiemannZetaVanishingOrder_ne_top hZero)

theorem concreteRiemannZetaMultiplicity_coe_eq_order
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    (concreteRiemannZetaMultiplicity rho : ENat) =
      (TS260.Goldbach.riemannZeta_analyticAt_of_ne_one
        rho (concreteZero_ne_one hZero)).order := by
  unfold concreteRiemannZetaMultiplicity
  rw [dif_pos hZero]
  exact ENat.coe_toNat
    (concreteRiemannZetaVanishingOrder_ne_top hZero)

theorem concreteNontrivialZero_conjugate_closed
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    concreteNontrivialRiemannZetaZeroSet (star rho) := by
  constructor
  case left =>
    unfold TS185.Goldbach.riemannZetaZeroPredicate
    unfold TS185.Goldbach.mathlibRiemannZetaFunction
    rw [TS263.Goldbach.riemannZeta_schwarzReflection rho]
    rw [concreteZero_is_zeta_zero hZero]
    simp
  case right =>
    unfold TS185.Goldbach.criticalStripPredicate
    simpa using concreteZero_in_critical_strip hZero

theorem concreteNontrivialZero_symmetry_about_half
    {rho : Complex}
    (hZero : concreteNontrivialRiemannZetaZeroSet rho) :
    concreteNontrivialRiemannZetaZeroSet
      (TS93.Goldbach.ZetaZero.symmetry rho) := by
  have hNotNeg : forall n : Nat, Not (rho = -(n : Complex)) :=
    fun n => concreteZero_ne_neg_nat hZero n
  have hFunctional :=
    riemannZeta_one_sub hNotNeg (concreteZero_ne_one hZero)
  constructor
  case left =>
    unfold TS93.Goldbach.ZetaZero.symmetry
    unfold TS185.Goldbach.riemannZetaZeroPredicate
    unfold TS185.Goldbach.mathlibRiemannZetaFunction
    rw [hFunctional]
    rw [concreteZero_is_zeta_zero hZero]
    simp
  case right =>
    unfold TS93.Goldbach.ZetaZero.symmetry
    unfold TS185.Goldbach.criticalStripPredicate
    simp only [Complex.sub_re, Complex.one_re]
    have hStrip := concreteZero_in_critical_strip hZero
    constructor <;> linarith [hStrip.1, hStrip.2]

noncomputable def concreteRiemannZetaZeroFamilyContract :
    TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract where
  zeroSet := concreteNontrivialRiemannZetaZeroSet
  multiplicity := concreteRiemannZetaMultiplicity
  zeroSet_is_zeta_zero := fun _ hZero => hZero.1
  zeroSet_in_critical_strip := fun _ hZero => hZero.2
  multiplicity_positive := fun _ hZero =>
    concreteRiemannZetaMultiplicity_positive hZero
  conjugate_closed := fun _ hZero =>
    concreteNontrivialZero_conjugate_closed hZero
  symmetry_about_half := fun _ hZero =>
    concreteNontrivialZero_symmetry_about_half hZero
  zeta_zero_summability_required := True.intro
  multiplicity_api_required := True.intro
  exact_zero_enumeration_required := True.intro

noncomputable def concreteRiemannZetaMultiplicityRealization :
    TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract where
  base := concreteRiemannZetaZeroFamilyContract
  multiplicity_eq_vanishingOrder := by
    intro rho hZero
    simpa [concreteRiemannZetaZeroFamilyContract,
      TS260.Goldbach.riemannZetaVanishingOrderAtZero] using
      concreteRiemannZetaMultiplicity_coe_eq_order hZero

theorem concreteTruncation_zeroSumReality
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData
        concreteRiemannZetaMultiplicityRealization) :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      concreteRiemannZetaZeroFamilyContract truncation
      TS257.Goldbach.triangleSplineZeroSpectralSummand :=
  TS263.Goldbach.realizedTruncation_zeroSumReality
    concreteRiemannZetaMultiplicityRealization truncation

/-- The concrete TS185 contract supplies the historical TS93 ledger. -/
noncomputable def concreteZetaZeroFamilyLedger :
    TS93.Goldbach.ZetaZeroFamilyLedger :=
  TS185.Goldbach.zetaZeroFamilyLedger_of_apiContract
    concreteRiemannZetaZeroFamilyContract

/-- Schwarz reflection and the concrete realization build the TS259 wrapper. -/
noncomputable def concreteRiemannZetaTS259Extension :
    TS259.Goldbach.RiemannZetaZeroFamilyMultiplicityConjugationContract :=
  TS263.Goldbach.ts259Extension_of_realization
    concreteRiemannZetaMultiplicityRealization

/-- Real projection loses no information for every valid concrete-family
    truncation. -/
theorem concreteTruncation_realProjectionLossless
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData
        concreteRiemannZetaMultiplicityRealization)
    (X : Nat) :
    ((TS257.Goldbach.triangleSplineZeroContributionFunction
      concreteRiemannZetaZeroFamilyContract truncation X : Real) : Complex) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        concreteRiemannZetaZeroFamilyContract truncation X :=
  TS263.Goldbach.realizedTruncation_realProjectionLossless
    concreteRiemannZetaMultiplicityRealization truncation X

/-- Real absolute value is exactly the complex spectral modulus for every
    valid concrete-family truncation. -/
theorem concreteTruncation_realAbs_eq_complexAbs
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData
        concreteRiemannZetaMultiplicityRealization)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          concreteRiemannZetaZeroFamilyContract truncation X) =
      Complex.abs
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          concreteRiemannZetaZeroFamilyContract truncation X) :=
  TS263.Goldbach.realizedTruncation_realAbs_eq_complexAbs
    concreteRiemannZetaMultiplicityRealization truncation X

/-- Ledger recording the concrete zero family and multiplicity realization. -/
structure ConcreteRiemannZetaZeroFamilyRealizationLedger where
  ts263_schwarz_reflection :
    TS263.Goldbach.RiemannZetaSchwarzReflectionLedger

  concrete_zero_family :
    TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract

  concrete_ts93_ledger :
    TS93.Goldbach.ZetaZeroFamilyLedger

  concrete_multiplicity_realization :
    TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract

  concrete_ts259_extension :
    TS259.Goldbach.RiemannZetaZeroFamilyMultiplicityConjugationContract

  all_valid_truncations_real :
    forall truncation :
        TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData
          concrete_multiplicity_realization,
      TS256.Goldbach.TruncatedZeroSumRealityStatement
        concrete_multiplicity_realization.base truncation
        TS257.Goldbach.triangleSplineZeroSpectralSummand

  global_zero_summability_not_proved : True
  exact_zero_enumeration_not_proved : True
  concrete_finite_truncation_not_constructed : True
  explicit_formula_identity_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS264 ledger. -/
noncomputable def concreteRiemannZetaZeroFamilyRealizationLedger :
    ConcreteRiemannZetaZeroFamilyRealizationLedger where
  ts263_schwarz_reflection :=
    TS263.Goldbach.riemannZetaSchwarzReflectionLedger
  concrete_zero_family :=
    concreteRiemannZetaZeroFamilyContract
  concrete_ts93_ledger :=
    concreteZetaZeroFamilyLedger
  concrete_multiplicity_realization :=
    concreteRiemannZetaMultiplicityRealization
  concrete_ts259_extension :=
    concreteRiemannZetaTS259Extension
  all_valid_truncations_real :=
    concreteTruncation_zeroSumReality
  global_zero_summability_not_proved := True.intro
  exact_zero_enumeration_not_proved := True.intro
  concrete_finite_truncation_not_constructed := True.intro
  explicit_formula_identity_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS264. -/
def ConcreteRiemannZetaZeroFamilyRealizationTarget : Prop :=
  Nonempty ConcreteRiemannZetaZeroFamilyRealizationLedger

/-- TS264 target: the concrete zero family and multiplicity realization are
    assembled. -/
theorem concreteRiemannZetaZeroFamilyRealizationTarget :
    ConcreteRiemannZetaZeroFamilyRealizationTarget :=
  Nonempty.intro concreteRiemannZetaZeroFamilyRealizationLedger

end Goldbach
end TS264
