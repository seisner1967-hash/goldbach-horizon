import Mathlib.Tactic
import TS.Goldbach.Strong.TS87.FareySpacingRoadmap

namespace TS88
namespace Goldbach

/-!
# TS88 - Farey Separation Proof

TS87 isolates the classical Farey separation inequality as a contract. This
sprint proves that contract for the `FareyPoint` API introduced there.
-/

/-- The integer cross-difference attached to two Farey points. -/
def fareyCrossDiff
    (p r : TS87.Goldbach.FareyPoint) :
    Int :=
  p.num * (r.den : Int) - r.num * (p.den : Int)

/-- A nonzero integer has real absolute value at least one. -/
lemma one_le_abs_int_cast
    {z : Int}
    (hz : Not (z = 0)) :
    (1 : Real) <= |(z : Real)| := by
  have hnat : (1 : Nat) <= z.natAbs := by
    exact Nat.succ_le_of_lt (Int.natAbs_pos.mpr hz)
  have hreal : (1 : Real) <= (z.natAbs : Real) := by
    exact_mod_cast hnat
  simpa [Nat.cast_natAbs] using hreal

/-- The cross-difference is nonzero when the two embedded values are distinct. -/
lemma fareyCrossDiff_ne_zero_of_valueDistinct
    {p r : TS87.Goldbach.FareyPoint}
    (hpr : TS87.Goldbach.FareyPoint.valueDistinct p r) :
    Not (fareyCrossDiff p r = 0) := by
  have hpr_ne :
      Not
        (TS87.Goldbach.FareyPoint.value p =
          TS87.Goldbach.FareyPoint.value r) := by
    simpa [TS87.Goldbach.FareyPoint.valueDistinct] using hpr
  have hpden_ne : Not ((p.den : Real) = 0) := by
    exact_mod_cast (ne_of_gt p.den_pos)
  have hrden_ne : Not ((r.den : Real) = 0) := by
    exact_mod_cast (ne_of_gt r.den_pos)
  have hmul_ne :
      Not
        ((p.num : Real) * (r.den : Real) =
          (r.num : Real) * (p.den : Real)) := by
    intro hmul
    apply hpr_ne
    unfold TS87.Goldbach.FareyPoint.value
    exact (div_eq_div_iff hpden_ne hrden_ne).mpr hmul
  intro hz
  apply hmul_ne
  have hz_real :
      (p.num : Real) * (r.den : Real) -
          (r.num : Real) * (p.den : Real) =
        0 := by
    have hz_cast : ((fareyCrossDiff p r : Int) : Real) = 0 := by
      exact_mod_cast hz
    simpa [fareyCrossDiff, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      using hz_cast
  linarith

/-- Real-value difference in terms of the integer cross-difference. -/
lemma farey_value_sub_eq_crossDiff_div
    (p r : TS87.Goldbach.FareyPoint) :
    TS87.Goldbach.FareyPoint.value p -
        TS87.Goldbach.FareyPoint.value r =
      (fareyCrossDiff p r : Real) /
        ((p.den : Real) * (r.den : Real)) := by
  have hpden_ne : Not ((p.den : Real) = 0) := by
    exact_mod_cast (ne_of_gt p.den_pos)
  have hrden_ne : Not ((r.den : Real) = 0) := by
    exact_mod_cast (ne_of_gt r.den_pos)
  unfold TS87.Goldbach.FareyPoint.value
  field_simp [fareyCrossDiff, hpden_ne, hrden_ne]
  ring_nf

/-- The TS87 Farey separation statement. -/
theorem fareySeparationStatement :
    TS87.Goldbach.FareySeparationStatement := by
  intro p r hpr
  have hpden_pos : 0 < (p.den : Real) := by
    exact_mod_cast p.den_pos
  have hrden_pos : 0 < (r.den : Real) := by
    exact_mod_cast r.den_pos
  have hden_pos :
      0 < (p.den : Real) * (r.den : Real) :=
    mul_pos hpden_pos hrden_pos
  have hcross_ne :
      Not (fareyCrossDiff p r = 0) :=
    fareyCrossDiff_ne_zero_of_valueDistinct hpr
  have hcross_abs :
      (1 : Real) <= |(fareyCrossDiff p r : Real)| :=
    one_le_abs_int_cast hcross_ne
  have hvalue_abs :
      |TS87.Goldbach.FareyPoint.value p -
          TS87.Goldbach.FareyPoint.value r| =
        |(fareyCrossDiff p r : Real)| /
          ((p.den : Real) * (r.den : Real)) := by
    rw [farey_value_sub_eq_crossDiff_div]
    rw [abs_div]
    rw [abs_of_pos hden_pos]
  rw [hvalue_abs]
  exact
    (div_le_div_iff_of_pos_right hden_pos).mpr hcross_abs

/-- Concrete Farey separation contract. -/
def fareySeparationContract :
    TS87.Goldbach.FareySeparationContract where
  separation := fareySeparationStatement

/-- TS88 discharges the TS87 Farey separation target. -/
theorem fareySeparationContractTarget :
    TS87.Goldbach.FareySeparationContractTarget :=
  Nonempty.intro fareySeparationContract

/-- Local target for TS88. -/
def FareySeparationProofTarget : Prop :=
  TS87.Goldbach.FareySeparationContractTarget

/-- The local TS88 target is discharged. -/
theorem fareySeparationProofTarget :
    FareySeparationProofTarget :=
  fareySeparationContractTarget

/--
After TS88, only covering and counting remain on the Farey side: the separation
component is supplied by `fareySeparationContractTarget`.
-/
theorem fareySpacingContractTarget_of_covering_counting
    (Hc : TS87.Goldbach.FareyCoveringContractTarget)
    (Hn : TS87.Goldbach.FareyCountingContractTarget) :
    TS87.Goldbach.FareySpacingContractTarget :=
  TS87.Goldbach.fareySpacingContractTarget_of_components
    fareySeparationContractTarget
    Hc
    Hn

/--
Covering and counting targets now give the TS86 Farey-spacing infrastructure
target, because TS88 supplies separation.
-/
theorem fareySpacingInfrastructureTarget_of_covering_counting
    (Hc : TS87.Goldbach.FareyCoveringContractTarget)
    (Hn : TS87.Goldbach.FareyCountingContractTarget) :
    TS86.Goldbach.FareySpacingInfrastructureTarget :=
  TS87.Goldbach.fareySpacingInfrastructureTarget_of_contractTarget
    (fareySpacingContractTarget_of_covering_counting Hc Hn)

/--
Covering, counting, and a padded dual large-sieve bound give the padded
grand-sieve variance target.
-/
theorem paddedGrandSieveVarianceInfrastructureTarget_of_covering_counting_paddedDualLargeSieveTarget
    (Hc : TS87.Goldbach.FareyCoveringContractTarget)
    (Hn : TS87.Goldbach.FareyCountingContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS86.Goldbach.PaddedGrandSieveVarianceInfrastructureTarget :=
  TS87.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
    (fareySpacingContractTarget_of_covering_counting Hc Hn)
    HD

/--
Covering, counting, and a padded dual large-sieve bound give the TS84
scale-transfer API target.
-/
theorem scaleTransferMajorantAPIContractsTarget_of_covering_counting_paddedDualLargeSieveTarget
    (Hc : TS87.Goldbach.FareyCoveringContractTarget)
    (Hn : TS87.Goldbach.FareyCountingContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget :=
  TS87.Goldbach.scaleTransferMajorantAPIContractsTarget_of_fareyContract_paddedDualLargeSieveTarget
    (fareySpacingContractTarget_of_covering_counting Hc Hn)
    HD

end Goldbach
end TS88
