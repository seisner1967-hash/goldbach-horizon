import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Tactic
import TS.Goldbach.Strong.TS341.PairedEtaBounds

namespace TS341.Goldbach

noncomputable section

open Complex Filter Set Topology

private theorem exp_half_nat (n : Nat) :
    Complex.exp
        (2 * (Real.pi : Complex) * Complex.I * ((1 : Real) / 2 : Real) * n) =
      (-1 : Complex) ^ n := by
  rw [show
    2 * (Real.pi : Complex) * Complex.I * ((1 : Real) / 2 : Real) * n =
      (n : Complex) * ((Real.pi : Complex) * Complex.I) by
        push_cast
        ring]
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private noncomputable def expZetaHalfTerm (s : Complex) (n : Nat) : Complex :=
  Complex.exp
      (2 * (Real.pi : Complex) * Complex.I * ((1 : Real) / 2 : Real) * n) /
    (n : Complex) ^ s

private theorem shifted_expZeta_hasSum
    {s : Complex} (hs : 1 < s.re) :
    HasSum
      (fun n : Nat => expZetaHalfTerm s (n + 1))
      (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s) := by
  have hRaw := HurwitzZeta.hasSum_expZeta_of_one_lt_re ((1 : Real) / 2) hs
  have hCircle :
      (((1 : Real) / 2 : Real) : UnitAddCircle) =
        ZMod.toAddCircle (1 : ZMod 2) := by
    symm
    simpa using (ZMod.toAddCircle_natCast (N := 2) 1)
  rw [hCircle] at hRaw
  have hs0 : Not (s = 0) := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hShift := (hasSum_nat_add_iff' 1).mpr hRaw
  simpa [expZetaHalfTerm, Complex.zero_cpow hs0] using hShift

private theorem shifted_expZeta_even_summable
    {s : Complex} (hs : 1 < s.re) :
    Summable (fun n : Nat => expZetaHalfTerm s (2 * n + 1)) := by
  let f : Nat -> Complex := fun n => expZetaHalfTerm s (n + 1)
  have hf : Summable f := (shifted_expZeta_hasSum hs).summable
  have hi : Function.Injective (fun n : Nat => 2 * n) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) hab
  change Summable (Function.comp f fun n : Nat => 2 * n)
  exact hf.comp_injective hi

private theorem shifted_expZeta_odd_summable
    {s : Complex} (hs : 1 < s.re) :
    Summable (fun n : Nat => expZetaHalfTerm s (2 * n + 2)) := by
  let f : Nat -> Complex := fun n => expZetaHalfTerm s (n + 1)
  have hf : Summable f := (shifted_expZeta_hasSum hs).summable
  have hi : Function.Injective (fun n : Nat => 2 * n + 1) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel hab)
  change Summable (Function.comp f fun n : Nat => 2 * n + 1)
  exact hf.comp_injective hi

set_option maxHeartbeats 0 in
/-- In the half-plane of absolute convergence, grouping consecutive terms of
the exponential Hurwitz series gives the negative paired eta series. -/
theorem complexEta_eq_neg_expZeta_gt_one
    {s : Complex} (hs : 1 < s.re) :
    complexEta s =
      -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
  let f : Nat -> Complex := fun n => expZetaHalfTerm s (n + 1)
  let evenSum : Complex :=
    tsum (fun n : Nat => expZetaHalfTerm s (2 * n + 1))
  let oddSum : Complex :=
    tsum (fun n : Nat => expZetaHalfTerm s (2 * n + 2))
  have hEven : HasSum
      (fun n : Nat => expZetaHalfTerm s (2 * n + 1)) evenSum :=
    (shifted_expZeta_even_summable hs).hasSum
  have hOdd : HasSum
      (fun n : Nat => expZetaHalfTerm s (2 * n + 2)) oddSum :=
    (shifted_expZeta_odd_summable hs).hasSum
  have hEven' : HasSum (fun n : Nat => f (2 * n)) evenSum := by
    exact hEven
  have hOdd' : HasSum (fun n : Nat => f (2 * n + 1)) oddSum := by
    exact hOdd
  have hRecombined : HasSum f (evenSum + oddSum) := by
    exact hEven'.even_add_odd hOdd'
  have hTotal :
      evenSum + oddSum =
        HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s :=
    hRecombined.unique (shifted_expZeta_hasSum hs)
  have hPairs : HasSum
      (fun n : Nat =>
        expZetaHalfTerm s (2 * n + 1) +
          expZetaHalfTerm s (2 * n + 2))
      (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s) := by
    have h := hEven.add hOdd
    rwa [hTotal] at h
  have hTerm (n : Nat) :
      expZetaHalfTerm s (2 * n + 1) +
          expZetaHalfTerm s (2 * n + 2) =
        -complexEtaPair n s := by
    rw [expZetaHalfTerm, expZetaHalfTerm, exp_half_nat, exp_half_nat]
    simp [complexEtaPair, Complex.cpow_neg, div_eq_mul_inv, pow_add, pow_mul]
    ring
  have hNegPairs : HasSum
      (fun n : Nat => -complexEtaPair n s)
      (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s) := by
    simpa only [hTerm] using hPairs
  have hEta : HasSum (fun n : Nat => complexEtaPair n s) (complexEta s) := by
    exact (complexEtaPair_summable (lt_trans zero_lt_one hs)).hasSum
  exact neg_eq_iff_eq_neg.mp (hEta.neg.unique hNegPairs)

/-- Analytic continuation of the paired eta identity to the full open right
half-plane. No point is removed at `s = 1`, since the nontrivial exponential
Hurwitz zeta function is entire. -/
theorem complexEta_eq_neg_expZeta
    {s : Complex} (hs : 0 < s.re) :
    complexEta s =
      -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
  let U : Set Complex := {z | 0 < z.re}
  let g : Complex -> Complex := fun z =>
    -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) z
  have hUOpen : IsOpen U :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  have hEtaAnalytic : AnalyticOnNhd Complex complexEta U := by
    simpa [U] using complexEta_analyticOnNhd
  have hHalfNe : Not (ZMod.toAddCircle (1 : ZMod 2) = 0) := by
    exact ZMod.toAddCircle_eq_zero.not.mpr (by norm_num)
  have hExpDiff : Differentiable Complex g := by
    dsimp [g]
    exact (HurwitzZeta.differentiable_expZeta_of_ne_zero hHalfNe).neg
  have hExpAnalytic : AnalyticOnNhd Complex g U := by
    apply DifferentiableOn.analyticOnNhd
    next =>
      intro z hz
      exact (hExpDiff z).differentiableWithinAt
    next => exact hUOpen
  have hUPreconnected : IsPreconnected U := by
    exact (convex_halfSpace_re_gt 0).isPreconnected
  have hTwo : Membership.mem U (2 : Complex) := by norm_num [U]
  have hEventually : Filter.EventuallyEq (nhds (2 : Complex)) complexEta g := by
    have hV : Membership.mem (nhds (2 : Complex)) {z : Complex | 1 < z.re} :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    exact complexEta_eq_neg_expZeta_gt_one hz
  have hEq := hEtaAnalytic.eqOn_of_preconnected_of_eventuallyEq
    hExpAnalytic hUPreconnected hTwo hEventually
  exact hEq (by simpa [U] using hs)

end

end TS341.Goldbach
