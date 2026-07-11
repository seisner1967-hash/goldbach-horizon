import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic
import TS.Goldbach.Strong.TS259.ZeroMultiplicityConjugationExtension

/-!
# TS260 - Riemann Zeta Vanishing Order Realization

TS259 installed a wrapper carrying conjugation invariance of the abstract
TS185 multiplicity.  This sprint connects that multiplicity to Mathlib's
canonical `AnalyticAt.order` for `riemannZeta`.

The Riemann zeta function is proved analytic at every selected TS185 zero,
because such a zero lies in the open critical strip and is therefore not the
pole at one.  A realization contract then identifies the natural-valued TS185
multiplicity with the finite `ENat` analytic order.

Conjugation invariance of that analytic order is isolated as one named future
statement.  Given it, the realization supplies the TS259 extension and all
finite-sum reality consequences.  The conjugation theorem itself, a concrete
realization, and all explicit-formula estimates remain open.
-/

namespace TS260
namespace Goldbach

/-- The Riemann zeta function is differentiable on the complement of one. -/
theorem riemannZeta_differentiableOn_compl_one :
    DifferentiableOn Complex riemannZeta
      (Set.compl (Set.singleton (1 : Complex))) := by
  intro s hs
  apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
  simpa using hs

/-- Differentiability off the pole gives analyticity at every other point. -/
theorem riemannZeta_analyticAt_of_ne_one
    (s : Complex)
    (hs : Not (s = 1)) :
    AnalyticAt Complex riemannZeta s := by
  apply riemannZeta_differentiableOn_compl_one.analyticAt
  exact compl_singleton_mem_nhds hs

/-- Every selected TS185 zero is different from the pole at one. -/
theorem zeroSet_ne_one
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (rho : Complex)
    (hZero : C.zeroSet rho) :
    Not (rho = 1) := by
  intro hOne
  have hStrip := C.zeroSet_in_critical_strip rho hZero
  rw [hOne] at hStrip
  unfold TS185.Goldbach.criticalStripPredicate at hStrip
  norm_num at hStrip

/-- The Riemann zeta function is analytic at every selected TS185 zero. -/
theorem riemannZeta_analyticAt_zeroSet
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (rho : Complex)
    (hZero : C.zeroSet rho) :
    AnalyticAt Complex riemannZeta rho :=
  riemannZeta_analyticAt_of_ne_one rho (zeroSet_ne_one C rho hZero)

/-- Canonical analytic order of Riemann zeta away from its pole at one. -/
noncomputable def riemannZetaVanishingOrderAt
    (s : Complex)
    (hs : Not (s = 1)) :
    ENat :=
  (riemannZeta_analyticAt_of_ne_one s hs).order

/-- Canonical analytic order at a zero selected by a TS185 contract. -/
noncomputable def riemannZetaVanishingOrderAtZero
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (rho : Complex)
    (hZero : C.zeroSet rho) :
    ENat :=
  (riemannZeta_analyticAt_zeroSet C rho hZero).order

/-- Local factorization characterization of the canonical zeta order. -/
theorem riemannZetaVanishingOrderAt_eq_nat_iff
    (s : Complex)
    (hs : Not (s = 1))
    (n : Nat) :
    riemannZetaVanishingOrderAt s hs = (n : ENat) <->
      Exists fun g : Complex -> Complex =>
        AnalyticAt Complex g s /\
          Not (g s = 0) /\
            Filter.Eventually
              (fun z => riemannZeta z = (z - s) ^ n * g z)
              (nhds s) := by
  simpa [riemannZetaVanishingOrderAt, smul_eq_mul] using
    (AnalyticAt.order_eq_nat_iff (riemannZeta_analyticAt_of_ne_one s hs) n)

/-- The abstract TS185 multiplicity is the canonical analytic zeta order. -/
structure RiemannZetaZeroMultiplicityRealizationContract where
  base : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract

  multiplicity_eq_vanishingOrder :
    forall
      (rho : Complex)
      (hZero : base.zeroSet rho),
      (base.multiplicity rho : ENat) =
        riemannZetaVanishingOrderAtZero base rho hZero

/-- The remaining analytic target: conjugation preserves zeta zero order. -/
def RiemannZetaVanishingOrderConjugationStatement
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract) :
    Prop :=
  forall (rho : Complex) (hZero : C.zeroSet rho),
    riemannZetaVanishingOrderAtZero
        C (star rho) (C.conjugate_closed rho hZero) =
      riemannZetaVanishingOrderAtZero C rho hZero

/-- Order realization plus conjugation of order gives conjugate multiplicity. -/
theorem multiplicityConjugation_of_realization
    (R : RiemannZetaZeroMultiplicityRealizationContract)
    (hConjugation :
      RiemannZetaVanishingOrderConjugationStatement R.base) :
    TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement R.base := by
  intro rho hZero
  have hStarZero := R.base.conjugate_closed rho hZero
  have hCoe :
      (R.base.multiplicity (star rho) : ENat) =
        (R.base.multiplicity rho : ENat) := by
    calc
      (R.base.multiplicity (star rho) : ENat) =
          riemannZetaVanishingOrderAtZero R.base (star rho) hStarZero :=
        R.multiplicity_eq_vanishingOrder (star rho) hStarZero
      _ = riemannZetaVanishingOrderAtZero R.base rho hZero :=
        hConjugation rho hZero
      _ = (R.base.multiplicity rho : ENat) :=
        (R.multiplicity_eq_vanishingOrder rho hZero).symm
  exact ENat.coe_inj.mp hCoe

/-- Build the TS259 wrapper from a realized order and conjugation theorem. -/
noncomputable def ts259Extension_of_realization
    (R : RiemannZetaZeroMultiplicityRealizationContract)
    (hConjugation :
      RiemannZetaVanishingOrderConjugationStatement R.base) :
    TS259.Goldbach.RiemannZetaZeroFamilyMultiplicityConjugationContract :=
  TS259.Goldbach.RiemannZetaZeroFamilyMultiplicityConjugationContract.ofBase
    R.base
    (multiplicityConjugation_of_realization R hConjugation)

/-- TS256 truncation data for an order-realized TS185 contract. -/
abbrev RiemannZetaZeroMultiplicityRealizationTruncationData
    (R : RiemannZetaZeroMultiplicityRealizationContract) :=
  TS256.Goldbach.RiemannZetaZeroTruncationData R.base

/-- A realized order plus conjugation gives finite-sum reality. -/
theorem realizedTruncation_zeroSumReality
    (R : RiemannZetaZeroMultiplicityRealizationContract)
    (hConjugation :
      RiemannZetaVanishingOrderConjugationStatement R.base)
    (truncation : RiemannZetaZeroMultiplicityRealizationTruncationData R) :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      R.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand :=
  TS259.Goldbach.extendedTruncation_zeroSumReality
    (ts259Extension_of_realization R hConjugation) truncation

/-- A realized order plus conjugation gives lossless real projection. -/
theorem realizedTruncation_realProjectionLossless
    (R : RiemannZetaZeroMultiplicityRealizationContract)
    (hConjugation :
      RiemannZetaVanishingOrderConjugationStatement R.base)
    (truncation : RiemannZetaZeroMultiplicityRealizationTruncationData R)
    (X : Nat) :
    ((TS257.Goldbach.triangleSplineZeroContributionFunction
      R.base truncation X : Real) : Complex) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        R.base truncation X :=
  TS259.Goldbach.extendedTruncation_realProjectionLossless
    (ts259Extension_of_realization R hConjugation) truncation X

/-- A realized order plus conjugation transports real absolute value exactly. -/
theorem realizedTruncation_realAbs_eq_complexAbs
    (R : RiemannZetaZeroMultiplicityRealizationContract)
    (hConjugation :
      RiemannZetaVanishingOrderConjugationStatement R.base)
    (truncation : RiemannZetaZeroMultiplicityRealizationTruncationData R)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          R.base truncation X) =
      Complex.abs
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          R.base truncation X) :=
  TS259.Goldbach.extendedTruncation_realAbs_eq_complexAbs
    (ts259Extension_of_realization R hConjugation) truncation X

/-- Ledger recording the canonical order realization and its routing. -/
structure RiemannZetaVanishingOrderRealizationLedger where
  ts259_multiplicity_extension :
    TS259.Goldbach.ZeroMultiplicityConjugationExtensionLedger

  analytic_at_selected_zero :
    forall
      (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
      (rho : Complex),
      C.zeroSet rho -> AnalyticAt Complex riemannZeta rho

  order_realization_implies_multiplicity_conjugation :
    forall R : RiemannZetaZeroMultiplicityRealizationContract,
      RiemannZetaVanishingOrderConjugationStatement R.base ->
        TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement R.base

  order_realization_supplies_ts259_extension :
    forall R : RiemannZetaZeroMultiplicityRealizationContract,
      RiemannZetaVanishingOrderConjugationStatement R.base ->
        TS259.Goldbach.RiemannZetaZeroFamilyMultiplicityConjugationContract

  order_realization_implies_zero_sum_reality :
    forall R : RiemannZetaZeroMultiplicityRealizationContract,
      RiemannZetaVanishingOrderConjugationStatement R.base ->
        forall truncation :
            RiemannZetaZeroMultiplicityRealizationTruncationData R,
          TS256.Goldbach.TruncatedZeroSumRealityStatement
            R.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand

  order_realization_implies_abs_transport :
    forall R : RiemannZetaZeroMultiplicityRealizationContract,
      RiemannZetaVanishingOrderConjugationStatement R.base ->
        forall
          (truncation : RiemannZetaZeroMultiplicityRealizationTruncationData R)
          (X : Nat),
          abs
              (TS257.Goldbach.triangleSplineZeroContributionFunction
                R.base truncation X) =
            Complex.abs
              (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
                R.base truncation X)

  vanishing_order_conjugation_not_proved : True
  concrete_realization_not_constructed : True
  explicit_formula_identity_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS260 ledger. -/
noncomputable def riemannZetaVanishingOrderRealizationLedger :
    RiemannZetaVanishingOrderRealizationLedger where
  ts259_multiplicity_extension :=
    TS259.Goldbach.zeroMultiplicityConjugationExtensionLedger
  analytic_at_selected_zero := riemannZeta_analyticAt_zeroSet
  order_realization_implies_multiplicity_conjugation :=
    multiplicityConjugation_of_realization
  order_realization_supplies_ts259_extension :=
    ts259Extension_of_realization
  order_realization_implies_zero_sum_reality :=
    realizedTruncation_zeroSumReality
  order_realization_implies_abs_transport :=
    realizedTruncation_realAbs_eq_complexAbs
  vanishing_order_conjugation_not_proved := True.intro
  concrete_realization_not_constructed := True.intro
  explicit_formula_identity_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS260. -/
def RiemannZetaVanishingOrderRealizationTarget : Prop :=
  Nonempty RiemannZetaVanishingOrderRealizationLedger

/-- TS260 target: canonical zeta order realization is installed. -/
theorem riemannZetaVanishingOrderRealizationTarget :
    RiemannZetaVanishingOrderRealizationTarget :=
  Nonempty.intro riemannZetaVanishingOrderRealizationLedger

end Goldbach
end TS260
