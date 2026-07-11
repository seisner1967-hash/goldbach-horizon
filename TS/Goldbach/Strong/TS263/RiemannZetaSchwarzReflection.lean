import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Tactic
import TS.Goldbach.Strong.TS262.DoubleConjugationAnalyticity

/-!
# TS263 - Riemann Zeta Schwarz Reflection

TS262 left Schwarz reflection as the sole analytic input needed by the
vanishing-order conjugation route.  This sprint proves it.

On the half-plane `1 < re s`, the proof conjugates the absolutely convergent
Dirichlet series term by term.  The identity principle then extends equality
between zeta and its double conjugate across the connected punctured plane.
The conventionally assigned Mathlib value at one is handled separately and is
real.  The resulting theorem closes the TS261 analytic input contract.

No concrete TS185 zero family or multiplicity realization is constructed, and
no explicit-formula identity, zero bound, residual bound, Gallagher estimate,
or Goldbach statement is proved.
-/

namespace TS263
namespace Goldbach

open Filter Set

/-- Conjugation of one term in the zeta Dirichlet series. -/
theorem star_one_div_nat_add_one_cpow (n : Nat) (s : Complex) :
    star (1 / ((n : Complex) + 1) ^ s) =
      1 / ((n : Complex) + 1) ^ star s := by
  rw [div_eq_mul_inv, one_mul]
  rw [show
    star (Inv.inv (((n : Complex) + 1) ^ s)) =
      Inv.inv (star (((n : Complex) + 1) ^ s)) by
        exact Complex.conj_inv (((n : Complex) + 1) ^ s)]
  symm
  simpa using
    (Complex.cpow_conj (((n : Complex) + 1)) s (by
      have hCast :
          ((n : Complex) + 1) = (((n + 1 : Nat) : Complex)) := by
        norm_num
      rw [hCast, Complex.natCast_arg]
      exact ne_of_lt Real.pi_pos))

/-- Schwarz reflection on the half-plane of convergence of the Dirichlet
    series. -/
theorem riemannZeta_schwarzReflection_of_one_lt_re
    {s : Complex}
    (hs : 1 < s.re) :
    riemannZeta (star s) = star (riemannZeta s) := by
  have hsStar : 1 < (star s).re := by
    simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hsStar]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  calc
    tsum (fun n : Nat => 1 / ((n : Complex) + 1) ^ star s) =
        tsum (fun n : Nat => star (1 / ((n : Complex) + 1) ^ s)) := by
      apply tsum_congr
      intro n
      exact (star_one_div_nat_add_one_cpow n s).symm
    _ = star (tsum (fun n : Nat => 1 / ((n : Complex) + 1) ^ s)) := by
      exact (Complex.conj_tsum _).symm

/-- The domain on which Riemann zeta is analytic. -/
def zetaPuncturedDomain : Set Complex :=
  Set.compl (Set.singleton (1 : Complex))

/-- Removing one point from the complex plane leaves a preconnected set. -/
theorem zetaPuncturedDomain_isPreconnected :
    IsPreconnected zetaPuncturedDomain := by
  have hRank : 1 < Module.rank Real Complex := by
    rw [Complex.rank_real_complex]
    exact Nat.one_lt_ofNat
  exact
    (isConnected_compl_singleton_of_one_lt_rank
      hRank
      (1 : Complex)).isPreconnected

/-- Analytic continuation extends Schwarz reflection to every point away from
    the exceptional value one. -/
theorem riemannZeta_schwarzReflection_ne_one
    {s : Complex}
    (hs : Not (s = 1)) :
    riemannZeta (star s) = star (riemannZeta s) := by
  let A : Complex -> Complex :=
    TS261.Goldbach.conjugatedFunction riemannZeta
  let B : Complex -> Complex := riemannZeta
  have hB : AnalyticOnNhd Complex B zetaPuncturedDomain := by
    exact
      TS260.Goldbach.riemannZeta_differentiableOn_compl_one.analyticOnNhd
        isOpen_compl_singleton
  have hA : AnalyticOnNhd Complex A zetaPuncturedDomain := by
    intro z hz
    have hzNe : Not (z = 1) := by
      simpa [zetaPuncturedDomain] using hz
    have hStarNe : Not (star z = 1) := by
      intro h
      apply hzNe
      have hStar := congrArg star h
      simpa using hStar
    have hZeta :=
      TS260.Goldbach.riemannZeta_analyticAt_of_ne_one (star z) hStarNe
    have hConjugated :=
      TS262.Goldbach.conjugatedFunction_analyticAt hZeta
    simpa [A] using hConjugated
  have hTwo : zetaPuncturedDomain (2 : Complex) := by
    change Not ((2 : Complex) = 1)
    norm_num
  have hEventually :
      Filter.EventuallyEq (nhds (2 : Complex)) A B := by
    have hOpen : IsOpen {z : Complex | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hMem : (fun z : Complex => 1 < z.re) (2 : Complex) := by
      norm_num
    filter_upwards [hOpen.mem_nhds hMem] with z hz
    have hReflection := riemannZeta_schwarzReflection_of_one_lt_re hz
    have hStar := congrArg star hReflection
    simpa [A, B, TS261.Goldbach.conjugatedFunction] using hStar
  have hEqOn : Set.EqOn A B zetaPuncturedDomain :=
    hA.eqOn_of_preconnected_of_eventuallyEq hB
      zetaPuncturedDomain_isPreconnected hTwo hEventually
  have hAt := hEqOn (show zetaPuncturedDomain s by
    simpa [zetaPuncturedDomain] using hs)
  have hStar := congrArg star hAt
  simpa [A, B, TS261.Goldbach.conjugatedFunction] using hStar

/-- Schwarz reflection for the Mathlib Riemann zeta function on all of the
    complex plane, including Mathlib's conventionally assigned value at one. -/
theorem riemannZeta_schwarzReflection :
    TS261.Goldbach.RiemannZetaSchwarzReflectionStatement := by
  intro s
  by_cases hs : s = 1
  case pos =>
    subst s
    have hLog :
        Complex.log (4 * (Real.pi : Complex)) =
          (Real.log (4 * Real.pi) : Complex) := by
      calc
        Complex.log (4 * (Real.pi : Complex)) =
            Complex.log ((4 * Real.pi : Real) : Complex) := by
          congr 1
          norm_num [Complex.ofReal_mul]
        _ = (Real.log (4 * Real.pi) : Complex) :=
          (Complex.ofReal_log
            (mul_nonneg
              (show (0 : Real) <= 4 by norm_num)
              Real.pi_pos.le)).symm
    simp only [star_one]
    simp [riemannZeta_one, hLog]
  case neg =>
    exact riemannZeta_schwarzReflection_ne_one hs

/-- The complete TS261 analytic input is now unconditional. -/
noncomputable def riemannZetaVanishingOrderConjugationInputs :
    TS261.Goldbach.RiemannZetaVanishingOrderConjugationInputContract :=
  TS262.Goldbach.ts261Inputs_of_schwarzReflection
    riemannZeta_schwarzReflection

/-- Zeta analytic order is preserved by conjugation for every TS185 family. -/
theorem riemannZetaVanishingOrderConjugation
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract) :
    TS260.Goldbach.RiemannZetaVanishingOrderConjugationStatement C :=
  TS262.Goldbach.riemannZetaVanishingOrderConjugation_of_schwarzReflection
    riemannZeta_schwarzReflection C

/-- A concrete order realization now supplies conjugate multiplicities. -/
theorem multiplicityConjugation_of_realization
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract) :
    TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement R.base :=
  TS262.Goldbach.multiplicityConjugation_of_realization_and_schwarzReflection
    riemannZeta_schwarzReflection R

/-- A concrete order realization now builds the TS259 extension. -/
noncomputable def ts259Extension_of_realization
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract) :
    TS259.Goldbach.RiemannZetaZeroFamilyMultiplicityConjugationContract :=
  TS262.Goldbach.ts259Extension_of_realization_and_schwarzReflection
    riemannZeta_schwarzReflection R

/-- Every realized TS256 truncation has a real zero sum. -/
theorem realizedTruncation_zeroSumReality
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R) :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      R.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand :=
  TS262.Goldbach.realizedTruncation_zeroSumReality_of_schwarzReflection
    riemannZeta_schwarzReflection R truncation

/-- Every realized TS256 truncation has lossless real projection. -/
theorem realizedTruncation_realProjectionLossless
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R)
    (X : Nat) :
    ((TS257.Goldbach.triangleSplineZeroContributionFunction
      R.base truncation X : Real) : Complex) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        R.base truncation X :=
  TS262.Goldbach.realizedTruncation_realProjectionLossless_of_schwarzReflection
    riemannZeta_schwarzReflection R truncation X

/-- Every realized TS256 truncation has exact real-to-complex absolute-value
    transport. -/
theorem realizedTruncation_realAbs_eq_complexAbs
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          R.base truncation X) =
      Complex.abs
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          R.base truncation X) :=
  TS262.Goldbach.realizedTruncation_realAbs_eq_complexAbs_of_schwarzReflection
    riemannZeta_schwarzReflection R truncation X

/-- Ledger recording the unconditional Schwarz-reflection discharge. -/
structure RiemannZetaSchwarzReflectionLedger where
  ts262_double_conjugation :
    TS262.Goldbach.DoubleConjugationAnalyticityLedger

  dirichlet_half_plane_reflection :
    forall {s : Complex},
      1 < s.re -> riemannZeta (star s) = star (riemannZeta s)

  schwarz_reflection_proved :
    TS261.Goldbach.RiemannZetaSchwarzReflectionStatement

  ts261_inputs_assembled :
    TS261.Goldbach.RiemannZetaVanishingOrderConjugationInputContract

  zeta_order_conjugation_proved :
    forall C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract,
      TS260.Goldbach.RiemannZetaVanishingOrderConjugationStatement C

  realization_supplies_multiplicity_conjugation :
    forall R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract,
      TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement R.base

  realization_supplies_zero_sum_reality :
    forall R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract,
      forall truncation :
          TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R,
        TS256.Goldbach.TruncatedZeroSumRealityStatement
          R.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand

  concrete_zero_family_not_constructed : True
  concrete_realization_not_constructed : True
  explicit_formula_identity_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS263 ledger. -/
noncomputable def riemannZetaSchwarzReflectionLedger :
    RiemannZetaSchwarzReflectionLedger where
  ts262_double_conjugation :=
    TS262.Goldbach.doubleConjugationAnalyticityLedger
  dirichlet_half_plane_reflection :=
    riemannZeta_schwarzReflection_of_one_lt_re
  schwarz_reflection_proved :=
    riemannZeta_schwarzReflection
  ts261_inputs_assembled :=
    riemannZetaVanishingOrderConjugationInputs
  zeta_order_conjugation_proved :=
    riemannZetaVanishingOrderConjugation
  realization_supplies_multiplicity_conjugation :=
    multiplicityConjugation_of_realization
  realization_supplies_zero_sum_reality :=
    realizedTruncation_zeroSumReality
  concrete_zero_family_not_constructed := True.intro
  concrete_realization_not_constructed := True.intro
  explicit_formula_identity_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS263. -/
def RiemannZetaSchwarzReflectionTarget : Prop :=
  Nonempty RiemannZetaSchwarzReflectionLedger

/-- TS263 target: Riemann zeta Schwarz reflection is proved and routed. -/
theorem riemannZetaSchwarzReflectionTarget :
    RiemannZetaSchwarzReflectionTarget :=
  Nonempty.intro riemannZetaSchwarzReflectionLedger

end Goldbach
end TS263
