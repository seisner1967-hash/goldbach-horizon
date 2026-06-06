import Mathlib.Tactic
import TS.Goldbach.Strong.TS133.SelbergProperDivisorMobiusChainCollapse

namespace TS134
namespace Goldbach

/-!
# TS134 - Selberg Proper Divisor Quotient Reindexing Discharge

TS133 proves that the proper-divisor Mobius chain coefficient collapses once
the finite quotient reindexing is available.

This sprint discharges that reindexing.  The proof has two finite steps:

* the chain coefficient over the positive reconstruction support is the same
  sum over divisors `m` of `e`, filtered by `d | m`;
* the map `r -> d * r` reindexes divisors of `e / d` onto those filtered
  divisors of `e`.

Together these prove the TS133 quotient reindexing obligation.
-/

/-- A divisor of a supported `e` lies in the positive reconstruction support. -/
theorem divisor_mem_reconstructionSupport_of_mem
    {level e m : Nat}
    (he :
      Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) e)
    (hm : Membership.mem (Nat.divisors e) m) :
    Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) m := by
  have he_support :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) e := by
    simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using he
  have he_level : e <= level :=
    TS130.Goldbach.mem_selbergReconstructionSupport_le_level he_support
  have he_pos : 0 < e :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos he_support
  have he_ne : Not (e = 0) := Nat.ne_of_gt he_pos
  have hm_dvd_e : Dvd.dvd m e := (Nat.mem_divisors.mp hm).1
  have hm_ne : Not (m = 0) := by
    intro hm_zero
    apply he_ne
    exact Nat.eq_zero_of_zero_dvd (by simpa [hm_zero] using hm_dvd_e)
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
  have hm_le_e : m <= e := Nat.divisor_le hm
  have hm_le_level : m <= level := le_trans hm_le_e he_level
  have hm_range :
      Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) m := by
    simpa [TS108.Goldbach.selbergQuadraticSupport, Nat.lt_succ_iff]
      using hm_le_level
  have hm_positive_support :
      Membership.mem (TS121.Goldbach.selbergPositiveQuadraticSupport level) m := by
    rw [TS121.Goldbach.mem_selbergPositiveQuadraticSupport]
    exact And.intro hm_range hm_pos
  simpa
    [TS131.Goldbach.selbergMobiusReconstructionSupport,
      TS130.Goldbach.selbergReconstructionSupport,
      TS122.Goldbach.selbergOptimizationSupport]
    using hm_positive_support

/--
The chain coefficient is the divisor sum over `e`, filtered by multiples of
`d`.
-/
theorem selbergMobiusChainCoefficient_eq_filteredDivisorSum
    (level d e : Nat)
    (he :
      Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) e) :
    TS131.Goldbach.selbergMobiusChainCoefficient level d e =
      Finset.sum ((Nat.divisors e).filter fun m => Dvd.dvd d m) (fun m =>
        TS122.Goldbach.selbergMobiusRatCoefficient (e / m)) := by
  classical
  have he_support :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) e := by
    simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using he
  have he_pos : 0 < e :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos he_support
  have he_ne : Not (e = 0) := Nat.ne_of_gt he_pos
  have hset :
      (TS131.Goldbach.selbergMobiusReconstructionSupport level).filter
          (fun m => Dvd.dvd d m /\ Dvd.dvd m e) =
        (Nat.divisors e).filter fun m => Dvd.dvd d m := by
    apply Finset.ext
    intro m
    constructor
    case mp =>
      intro hm
      have hm_support_and :
          Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) m /\
            (Dvd.dvd d m /\ Dvd.dvd m e) := by
        simpa using (Finset.mem_filter.mp hm)
      exact
        Finset.mem_filter.mpr
          (And.intro
            (Nat.mem_divisors.mpr
              (And.intro hm_support_and.2.2 he_ne))
            hm_support_and.2.1)
    case mpr =>
      intro hm
      have hm_divisor_and :
          Membership.mem (Nat.divisors e) m /\ Dvd.dvd d m := by
        simpa using (Finset.mem_filter.mp hm)
      have hm_support :
          Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) m :=
        divisor_mem_reconstructionSupport_of_mem he hm_divisor_and.1
      have hm_dvd_e : Dvd.dvd m e :=
        Nat.dvd_of_mem_divisors hm_divisor_and.1
      exact
        Finset.mem_filter.mpr
          (And.intro hm_support
            (And.intro hm_divisor_and.2 hm_dvd_e))
  unfold TS131.Goldbach.selbergMobiusChainCoefficient
  calc
    Finset.sum
        (TS131.Goldbach.selbergMobiusReconstructionSupport level)
        (fun m =>
          if Dvd.dvd d m then
            if Dvd.dvd m e then
              TS122.Goldbach.selbergMobiusRatCoefficient (e / m)
            else
              0
          else
            0) =
        Finset.sum
          (TS131.Goldbach.selbergMobiusReconstructionSupport level)
          (fun m =>
            if Dvd.dvd d m /\ Dvd.dvd m e then
              TS122.Goldbach.selbergMobiusRatCoefficient (e / m)
            else
              0) := by
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hdm : Dvd.dvd d m
      case pos =>
        by_cases hme : Dvd.dvd m e
        case pos =>
          simp [hdm, hme]
        case neg =>
          simp [hdm, hme]
      case neg =>
        simp [hdm]
    _ =
        Finset.sum
          ((TS131.Goldbach.selbergMobiusReconstructionSupport level).filter
            (fun m => Dvd.dvd d m /\ Dvd.dvd m e))
          (fun m => TS122.Goldbach.selbergMobiusRatCoefficient (e / m)) := by
      rw [<- Finset.sum_filter]
    _ =
        Finset.sum ((Nat.divisors e).filter fun m => Dvd.dvd d m) (fun m =>
          TS122.Goldbach.selbergMobiusRatCoefficient (e / m)) := by
      rw [hset]

/--
The quotient divisor sum reindexes through the map `r -> d * r`.
-/
theorem quotientDivisorSum_eq_filteredDivisorSum
    {d e : Nat}
    (hd_pos : 0 < d)
    (he_pos : 0 < e)
    (hdvd : Dvd.dvd d e) :
    Finset.sum (Nat.divisors (e / d)) (fun r =>
        TS122.Goldbach.selbergMobiusRatCoefficient ((e / d) / r)) =
      Finset.sum ((Nat.divisors e).filter fun m => Dvd.dvd d m) (fun m =>
        TS122.Goldbach.selbergMobiusRatCoefficient (e / m)) := by
  classical
  have he_ne : Not (e = 0) := Nat.ne_of_gt he_pos
  have hn_pos : 0 < e / d :=
    Nat.div_pos (Nat.le_of_dvd he_pos hdvd) hd_pos
  have hn_ne : Not (e / d = 0) := Nat.ne_of_gt hn_pos
  have he_eq : e = d * (e / d) := by
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel hdvd).symm
  refine
    Finset.sum_bij
      (fun r _hr => d * r)
      (by
        intro r hr
        have hr_dvd : Dvd.dvd r (e / d) :=
          Nat.dvd_of_mem_divisors hr
        have hmul_dvd : Dvd.dvd (d * r) e := by
          rw [he_eq]
          exact Nat.mul_dvd_mul_left d hr_dvd
        exact
          Finset.mem_filter.mpr
            (And.intro
              (Nat.mem_divisors.mpr (And.intro hmul_dvd he_ne))
              (dvd_mul_right d r)))
      (by
        intro r1 _hr1 r2 _hr2 h
        exact Nat.eq_of_mul_eq_mul_left hd_pos h)
      (by
        intro m hm
        have hm_divisor_and :
            Membership.mem (Nat.divisors e) m /\ Dvd.dvd d m := by
          simpa using (Finset.mem_filter.mp hm)
        have hm_dvd_e : Dvd.dvd m e :=
          Nat.dvd_of_mem_divisors hm_divisor_and.1
        have hmul : d * (m / d) = m :=
          Nat.mul_div_cancel' hm_divisor_and.2
        have hr_dvd : Dvd.dvd (m / d) (e / d) := by
          rw [Nat.dvd_div_iff_mul_dvd hdvd]
          simpa [hmul] using hm_dvd_e
        exact
          Exists.intro (m / d)
            (Exists.intro
              (Nat.mem_divisors.mpr (And.intro hr_dvd hn_ne))
              hmul))
      (by
        intro r hr
        have hr_dvd : Dvd.dvd r (e / d) :=
          Nat.dvd_of_mem_divisors hr
        have hdiv : e / (d * r) = (e / d) / r := by
          calc
            e / (d * r) =
                (d * (e / d)) / (d * r) := by
              rw [<- he_eq]
            _ =
                (d / d) * ((e / d) / r) := by
              exact Nat.mul_div_mul_comm (dvd_refl d) hr_dvd
            _ =
                (e / d) / r := by
              simp [Nat.div_self hd_pos]
        simp [hdiv])

/-- TS134 discharges the quotient reindexing obligation from TS133. -/
theorem selbergMobiusProperDivisorQuotientReindexing
    (level : Nat) :
    TS133.Goldbach.SelbergMobiusProperDivisorQuotientReindexing level := by
  intro d hd e he hdvd
  have hd_support :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) d := by
    simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using hd
  have he_support :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) e := by
    simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using he
  have hd_pos : 0 < d :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos hd_support
  have he_pos : 0 < e :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos he_support
  rw [selbergMobiusChainCoefficient_eq_filteredDivisorSum level d e he]
  exact
    (quotientDivisorSum_eq_filteredDivisorSum
      hd_pos
      he_pos
      hdvd).symm

/-- The quotient reindexing closes the TS132 proper-divisor collapse. -/
theorem selbergMobiusProperDivisorChainCollapse
    (level : Nat) :
    TS132.Goldbach.SelbergMobiusProperDivisorChainCollapse level := by
  exact
    TS133.Goldbach.selbergMobiusProperDivisorChainCollapse_of_quotientReindexing
      level
      (selbergMobiusProperDivisorQuotientReindexing level)

/-- The quotient reindexing closes the full TS131 chain coefficient collapse. -/
theorem selbergMobiusChainCoefficientCollapse
    (level : Nat) :
    TS131.Goldbach.SelbergMobiusChainCoefficientCollapse level := by
  exact
    TS133.Goldbach.selbergMobiusChainCoefficientCollapse_of_quotientReindexing
      level
      (selbergMobiusProperDivisorQuotientReindexing level)

/-- TS134 package around the discharged quotient reindexing. -/
structure SelbergProperDivisorQuotientReindexingDischarge
    (level : Nat) where
  ts133 :
    TS133.Goldbach.SelbergProperDivisorMobiusChainCollapse level

  quotient_reindexing :
    TS133.Goldbach.SelbergMobiusProperDivisorQuotientReindexing level

  proper_divisor_collapse :
    TS132.Goldbach.SelbergMobiusProperDivisorChainCollapse level

  full_chain_collapse :
    TS131.Goldbach.SelbergMobiusChainCoefficientCollapse level

  reconstruction_identity_if_expansion :
    forall Y : Nat -> Rat,
      TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion level Y ->
        TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y

  reconstruction_fubini_expansion_obligation :
    True

  selberg_sieve_application_obligation :
    True

/-- Concrete TS134 quotient reindexing package. -/
def selbergProperDivisorQuotientReindexingDischarge
    (level : Nat) :
    SelbergProperDivisorQuotientReindexingDischarge level where
  ts133 :=
    TS133.Goldbach.selbergProperDivisorMobiusChainCollapse level
  quotient_reindexing :=
    selbergMobiusProperDivisorQuotientReindexing level
  proper_divisor_collapse :=
    selbergMobiusProperDivisorChainCollapse level
  full_chain_collapse :=
    selbergMobiusChainCoefficientCollapse level
  reconstruction_identity_if_expansion := by
    intro Y hexpansion
    exact
      TS133.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_quotientReindexing
        level
        Y
        hexpansion
        (selbergMobiusProperDivisorQuotientReindexing level)
  reconstruction_fubini_expansion_obligation := True.intro
  selberg_sieve_application_obligation := True.intro

/-- Target proposition for the TS134 quotient reindexing discharge. -/
def SelbergProperDivisorQuotientReindexingDischargeTarget : Prop :=
  forall level : Nat,
    Nonempty (SelbergProperDivisorQuotientReindexingDischarge level)

/-- The TS134 quotient reindexing discharge package is populated. -/
theorem selbergProperDivisorQuotientReindexingDischargeTarget :
    SelbergProperDivisorQuotientReindexingDischargeTarget := by
  intro level
  exact Nonempty.intro
    (selbergProperDivisorQuotientReindexingDischarge level)

/-- TS134 keeps the TS133 target available. -/
theorem selbergProperDivisorMobiusChainCollapseTarget :
    TS133.Goldbach.SelbergProperDivisorMobiusChainCollapseTarget :=
  TS133.Goldbach.selbergProperDivisorMobiusChainCollapseTarget

end Goldbach
end TS134
