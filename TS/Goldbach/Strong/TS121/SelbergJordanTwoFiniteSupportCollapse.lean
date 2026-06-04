import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import TS.Goldbach.Strong.TS120.SelbergGcdSquareGlobalReindexingLedger

namespace TS121
namespace Goldbach

/-!
# TS121 - Selberg Jordan-Two Finite Support Collapse

TS120 reduces the corrected gcd-square diagonalization to a local coefficient
collapse on the finite support `range (level + 1)`. This sprint discharges the
support issue on the positive part of that finite window and then uses the
absorbed weights from TS118 to handle the zero index.

The key point is:

* if `0 < m` and `m <= level`, then every divisor of `gcd(m,n)` lies in
  `range (level + 1)`;
* hence the finite filtered coefficient from TS120 is the full divisor sum
  from TS119;
* if `m = 0`, the absorbed weight `weight m / m` is `0`, so the weighted pair
  term vanishes.

Together these facts prove the corrected absorbed dense-to-diagonal identity
for the TS118/TS119 route.
-/

/-- Positive part of the TS108 finite support window. -/
def selbergPositiveQuadraticSupport
    (level : Nat) :
    Finset Nat :=
  (TS108.Goldbach.selbergQuadraticSupport level).filter fun m =>
    0 < m

/-- Membership in the positive support is support membership plus positivity. -/
theorem mem_selbergPositiveQuadraticSupport
    {level m : Nat} :
    Membership.mem (selbergPositiveQuadraticSupport level) m <->
      Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) m /\
        0 < m := by
  simp [selbergPositiveQuadraticSupport]

/--
The TS120 pair coefficient is the filtered finite sum over divisors of
`gcd(m,n)` inside the TS108 support.
-/
theorem selbergJordanTwoPairCoefficient_eq_filter
    (level m n : Nat) :
    TS120.Goldbach.selbergJordanTwoPairCoefficient level m n =
      Finset.sum
        ((TS108.Goldbach.selbergQuadraticSupport level).filter fun d =>
          Dvd.dvd d (Nat.gcd m n))
        (fun d => TS119.Goldbach.selbergJordanTwoCoefficient d) := by
  unfold TS120.Goldbach.selbergJordanTwoPairCoefficient
  rw [<- Finset.sum_filter]

/--
If `m` is positive and in the finite support, then filtering the support by
divisors of `gcd(m,n)` gives the full divisor finset of `gcd(m,n)`.
-/
theorem selbergSupportFilter_dvd_gcd_eq_divisors_of_pos_left
    (level m n : Nat)
    (hm_mem : Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) m)
    (hm_pos : 0 < m) :
    ((TS108.Goldbach.selbergQuadraticSupport level).filter fun d =>
        Dvd.dvd d (Nat.gcd m n)) =
      (Nat.gcd m n).divisors := by
  apply Finset.ext
  intro d
  rw [Finset.mem_filter, Nat.mem_divisors]
  constructor
  case mp =>
    intro h
    exact And.intro h.2 (ne_of_gt (Nat.gcd_pos_of_pos_left n hm_pos))
  case mpr =>
    intro h
    constructor
    case left =>
      have hd_le_gcd :
          d <= Nat.gcd m n :=
        Nat.divisor_le (Nat.mem_divisors.mpr h)
      have hgcd_le_m :
          Nat.gcd m n <= m :=
        Nat.le_of_dvd hm_pos (Nat.gcd_dvd_left m n)
      have hm_le_level :
          m <= level := by
        have hm_lt :
            m < level + 1 := by
          simpa [TS108.Goldbach.selbergQuadraticSupport] using hm_mem
        exact Nat.lt_succ_iff.mp hm_lt
      have hd_le_level :
          d <= level :=
        le_trans hd_le_gcd (le_trans hgcd_le_m hm_le_level)
      simpa [TS108.Goldbach.selbergQuadraticSupport] using
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hd_le_level)
    case right =>
      exact h.1

/-- Positive local coefficient collapse from TS119's full divisor identity. -/
theorem selbergJordanTwoPairCoefficient_eq_gcdSquareKernel_of_pos_left
    (level m n : Nat)
    (hm_mem : Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) m)
    (hm_pos : 0 < m) :
    TS120.Goldbach.selbergJordanTwoPairCoefficient level m n =
      TS118.Goldbach.selbergGcdSquareKernel m n := by
  rw [selbergJordanTwoPairCoefficient_eq_filter]
  rw [selbergSupportFilter_dvd_gcd_eq_divisors_of_pos_left
    level m n hm_mem hm_pos]
  rw [TS119.Goldbach.selbergJordanTwoCoefficient_divisor_sum_eq_square]
  rfl

/-- Positive-support version of the TS120 local coefficient collapse. -/
def SelbergJordanTwoPositiveLocalCoefficientCollapse
    (level : Nat)
    (_weight : Nat -> Rat) :
    Prop :=
  forall m : Nat,
    Membership.mem (selbergPositiveQuadraticSupport level) m ->
      forall n : Nat,
        Membership.mem (selbergPositiveQuadraticSupport level) n ->
          TS120.Goldbach.selbergJordanTwoPairCoefficient level m n =
            TS118.Goldbach.selbergGcdSquareKernel m n

/-- The positive-support local collapse is fully discharged. -/
theorem selbergJordanTwoPositiveLocalCoefficientCollapse
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergJordanTwoPositiveLocalCoefficientCollapse level weight := by
  intro m hm n _hn
  have hm' := (mem_selbergPositiveQuadraticSupport.mp hm)
  exact
    selbergJordanTwoPairCoefficient_eq_gcdSquareKernel_of_pos_left
      level
      m
      n
      hm'.1
      hm'.2

/-- Absorbed weights vanish at the zero index under Lean's totalized division. -/
theorem selbergLCMAbsorbedWeight_zero
    (weight : Nat -> Rat) :
    TS118.Goldbach.selbergLCMAbsorbedWeight weight 0 = 0 := by
  simp [TS118.Goldbach.selbergLCMAbsorbedWeight]

/--
The weighted pair term agrees with the gcd-square dense term for absorbed
weights. The `m = 0` case vanishes; the positive case uses the divisor support
collapse.
-/
theorem selbergAbsorbedPairCoefficientTerm_eq_gcdSquareTerm
    (level : Nat)
    (weight : Nat -> Rat)
    (m n : Nat)
    (hm_mem : Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) m) :
    TS118.Goldbach.selbergLCMAbsorbedWeight weight m *
        TS118.Goldbach.selbergLCMAbsorbedWeight weight n *
          TS120.Goldbach.selbergJordanTwoPairCoefficient level m n =
      TS118.Goldbach.selbergLCMAbsorbedWeight weight m *
        TS118.Goldbach.selbergLCMAbsorbedWeight weight n *
          TS118.Goldbach.selbergGcdSquareKernel m n := by
  by_cases hm0 : m = 0
  case pos =>
    subst m
    simp [selbergLCMAbsorbedWeight_zero]
  case neg =>
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    rw [selbergJordanTwoPairCoefficient_eq_gcdSquareKernel_of_pos_left
      level m n hm_mem hm_pos]

/--
The TS120 pair-first side equals the TS118 gcd-square dense side for absorbed
weights.
-/
theorem selbergJordanTwoPairFirstSide_absorbed_eq_gcdSquareDenseSide
    (level : Nat)
    (weight : Nat -> Rat) :
    TS120.Goldbach.selbergJordanTwoPairFirstSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) =
      TS118.Goldbach.selbergGcdSquareDenseSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) := by
  unfold TS120.Goldbach.selbergJordanTwoPairFirstSide
  unfold TS120.Goldbach.selbergJordanTwoPairFirstTerm
  unfold TS118.Goldbach.selbergGcdSquareDenseSide
  unfold TS118.Goldbach.selbergGcdSquareFormTerm
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n _hn
  exact
    selbergAbsorbedPairCoefficientTerm_eq_gcdSquareTerm
      level
      weight
      m
      n
      hm

/-- Corrected absorbed gcd-square dense side equals the Jordan-two diagonal side. -/
theorem selbergGcdSquareDenseSide_absorbed_eq_jordanDiagonalSide
    (level : Nat)
    (weight : Nat -> Rat) :
    TS118.Goldbach.selbergGcdSquareDenseSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) =
      TS119.Goldbach.selbergJordanTwoDiagonalSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) := by
  calc
    TS118.Goldbach.selbergGcdSquareDenseSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) =
        TS120.Goldbach.selbergJordanTwoPairFirstSide
          level
          (TS118.Goldbach.selbergLCMAbsorbedWeight weight) :=
      (selbergJordanTwoPairFirstSide_absorbed_eq_gcdSquareDenseSide
        level
        weight).symm
    _ =
        TS119.Goldbach.selbergJordanTwoDiagonalSide
          level
          (TS118.Goldbach.selbergLCMAbsorbedWeight weight) :=
      (TS120.Goldbach.selbergJordanTwoDiagonalSide_eq_pairFirst
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight)).symm

/--
Original dense `gcd/lcm` side equals the corrected Jordan-two diagonal side
with absorbed weights.
-/
theorem selbergOriginalDenseSide_eq_correctedJordanDiagonalSide
    (level : Nat)
    (weight : Nat -> Rat) :
    TS110.Goldbach.selbergDenseSide level weight =
      TS119.Goldbach.selbergJordanTwoDiagonalSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) := by
  calc
    TS110.Goldbach.selbergDenseSide level weight =
        TS118.Goldbach.selbergGcdSquareDenseSide
          level
          (TS118.Goldbach.selbergLCMAbsorbedWeight weight) :=
      TS118.Goldbach.selbergDenseSide_eq_gcdSquareDenseSide_absorbed
        level
        weight
    _ =
        TS119.Goldbach.selbergJordanTwoDiagonalSide
          level
          (TS118.Goldbach.selbergLCMAbsorbedWeight weight) :=
      selbergGcdSquareDenseSide_absorbed_eq_jordanDiagonalSide level weight

/--
TS121 finite-support collapse package.

It records the positive local collapse and the resulting global corrected
dense-to-diagonal identity for absorbed weights.
-/
structure SelbergJordanTwoFiniteSupportCollapse
    (level : Nat)
    (weight : Nat -> Rat) where
  reindexing :
    TS120.Goldbach.SelbergGcdSquareGlobalReindexing level weight

  positiveLocalCollapse :
    SelbergJordanTwoPositiveLocalCoefficientCollapse level weight

  absorbedPairFirstEqualsDense :
    TS120.Goldbach.selbergJordanTwoPairFirstSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) =
      TS118.Goldbach.selbergGcdSquareDenseSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight)

  absorbedDenseEqualsJordanDiagonal :
    TS118.Goldbach.selbergGcdSquareDenseSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) =
      TS119.Goldbach.selbergJordanTwoDiagonalSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight)

  originalDenseEqualsCorrectedJordanDiagonal :
    TS110.Goldbach.selbergDenseSide level weight =
      TS119.Goldbach.selbergJordanTwoDiagonalSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight)

  zero_index_absorbed :
    TS118.Goldbach.selbergLCMAbsorbedWeight weight 0 = 0

  support_collapse_ready :
    True

  corrected_dense_to_diagonal_closed :
    True

  square_sum_majorant_obligation :
    True

/-- Concrete TS121 finite-support collapse package. -/
def selbergJordanTwoFiniteSupportCollapse
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergJordanTwoFiniteSupportCollapse level weight where
  reindexing := TS120.Goldbach.selbergGcdSquareGlobalReindexing level weight
  positiveLocalCollapse :=
    selbergJordanTwoPositiveLocalCoefficientCollapse level weight
  absorbedPairFirstEqualsDense :=
    selbergJordanTwoPairFirstSide_absorbed_eq_gcdSquareDenseSide level weight
  absorbedDenseEqualsJordanDiagonal :=
    selbergGcdSquareDenseSide_absorbed_eq_jordanDiagonalSide level weight
  originalDenseEqualsCorrectedJordanDiagonal :=
    selbergOriginalDenseSide_eq_correctedJordanDiagonalSide level weight
  zero_index_absorbed :=
    selbergLCMAbsorbedWeight_zero weight
  support_collapse_ready := True.intro
  corrected_dense_to_diagonal_closed := True.intro
  square_sum_majorant_obligation := True.intro

/-- Target proposition for TS121 finite-support collapse. -/
def SelbergJordanTwoFiniteSupportCollapseTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergJordanTwoFiniteSupportCollapse level weight)

/-- The TS121 finite-support collapse package is populated. -/
theorem selbergJordanTwoFiniteSupportCollapseTarget :
    SelbergJordanTwoFiniteSupportCollapseTarget := by
  intro level weight
  exact Nonempty.intro (selbergJordanTwoFiniteSupportCollapse level weight)

/-- TS121 keeps the TS120 corrected global reindexing target available. -/
theorem selbergGcdSquareGlobalReindexingTarget :
    TS120.Goldbach.SelbergGcdSquareGlobalReindexingTarget :=
  TS120.Goldbach.selbergGcdSquareGlobalReindexingTarget

end Goldbach
end TS121
