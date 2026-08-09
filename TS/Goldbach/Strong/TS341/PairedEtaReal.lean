import Mathlib.Tactic
import TS.Goldbach.Strong.TS341.RealAlternatingEtaPositive
import TS.Goldbach.Strong.TS341.PairedEtaIdentification

namespace TS341.Goldbach

noncomputable section

open Complex Filter

private theorem ofReal_etaTerm (x : Real) (n : Nat) :
    (etaTerm x n : Complex) =
      ((n + 1 : Nat) : Complex) ^ (-(x : Complex)) := by
  simpa [etaTerm] using
    (Complex.ofReal_cpow
      (show 0 <= ((n + 1 : Nat) : Real) by positivity) (-x))

private theorem complexEtaPair_real (x : Real) (n : Nat) :
    complexEtaPair n (x : Complex) =
      (etaTerm x (2 * n) - etaTerm x (2 * n + 1) : Real) := by
  rw [complexEtaPair]
  rw [<- ofReal_etaTerm x (2 * n)]
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
  rw [<- ofReal_etaTerm x (2 * n + 1)]
  push_cast
  ring

private theorem sum_pairs_eq_even_partial (x : Real) (N : Nat) :
    Finset.sum (Finset.range N) (fun n => complexEtaPair n (x : Complex)) =
      (Finset.sum (Finset.range (2 * N))
        (fun i => (-1 : Real) ^ i * etaTerm x i) : Real) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, complexEtaPair_real]
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      simp [pow_add, pow_mul]
      ring

set_option maxHeartbeats 0 in
/-- On the positive real axis, the paired complex eta function is the
complexification of the real alternating-series limit. -/
theorem complexEta_real_eq_realEtaLimit
    {x : Real} (hx : 0 < x) :
    complexEta (x : Complex) = (realEtaLimit x : Complex) := by
  have hComplex : Tendsto
      (fun N => Finset.sum (Finset.range N)
        (fun n => complexEtaPair n (x : Complex)))
      atTop (nhds (complexEta (x : Complex))) :=
    (complexEtaPair_summable (by simpa using hx)).hasSum.tendsto_sum_nat
  have hDouble : Tendsto (fun N : Nat => 2 * N) atTop atTop := by
    have hId : Tendsto (fun N : Nat => N) atTop atTop := tendsto_id
    exact Filter.tendsto_atTop_mono (fun N => by omega) hId
  have hRealEven : Tendsto
      (fun N => Finset.sum (Finset.range (2 * N))
        (fun i => (-1 : Real) ^ i * etaTerm x i))
      atTop (nhds (realEtaLimit x)) :=
    (realEtaLimit_tendsto hx).comp hDouble
  have hRealComplex : Tendsto
      (fun N =>
        ((Finset.sum (Finset.range (2 * N))
          (fun i => (-1 : Real) ^ i * etaTerm x i) : Real) : Complex))
      atTop (nhds (realEtaLimit x : Complex)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hRealEven
  have hPairLimit : Tendsto
      (fun N => Finset.sum (Finset.range N)
        (fun n => complexEtaPair n (x : Complex)))
      atTop (nhds (realEtaLimit x : Complex)) := by
    simpa only [sum_pairs_eq_even_partial] using hRealComplex
  exact tendsto_nhds_unique hComplex hPairLimit

/-- Correctly signed eta identity: Mathlib's nontrivial exponential Hurwitz
zeta at one half is the negative of the standard real eta limit. -/
theorem expZeta_half_eq_neg_realEtaLimit
    {x : Real} (hx0 : 0 < x) (_hx1 : x < 1) :
    HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) =
      -(realEtaLimit x : Complex) := by
  have hEta :
      complexEta (x : Complex) = (realEtaLimit x : Complex) :=
    complexEta_real_eq_realEtaLimit hx0
  have hNeg :
      complexEta (x : Complex) =
        -HurwitzZeta.expZeta
          (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) :=
    complexEta_eq_neg_expZeta (by simpa using hx0)
  have hExp :
      HurwitzZeta.expZeta
          (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) =
        -complexEta (x : Complex) := by
    simpa using (congrArg Neg.neg hNeg).symm
  exact hExp.trans (congrArg Neg.neg hEta)

end

end TS341.Goldbach
