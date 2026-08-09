import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace TS341.Goldbach

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# TS341: positivity of the real alternating eta limit

This is the order-theoretic half of a future proof that Riemann zeta has no
real zero in the open critical strip. The identification with the analytic
continuation of zeta is deliberately not claimed here.
-/

def etaTerm (x : Real) (n : Nat) : Real :=
  ((n + 1 : Nat) : Real) ^ (-x)

private theorem etaTerm_antitone {x : Real} (hx : 0 <= x) :
    Antitone (etaTerm x) := by
  intro m n hmn
  unfold etaTerm
  apply Real.rpow_le_rpow_of_exponent_nonpos
  next => positivity
  next => exact_mod_cast Nat.add_le_add_right hmn 1
  next => exact neg_nonpos.mpr hx

private theorem etaTerm_tendsto_zero {x : Real} (hx : 0 < x) :
    Filter.Tendsto (etaTerm x) Filter.atTop (nhds 0) := by
  have hEta : etaTerm x = fun n : Nat => ((n : Real) + 1) ^ (-x) := by
    funext n
    simp [etaTerm]
  rw [hEta]
  have hBase :
      Filter.Tendsto (fun n : Nat => (n : Real) + 1)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right
      Filter.atTop 1 tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def] using
    (tendsto_rpow_neg_atTop hx).comp hBase

/-- The limit selected by the alternating-series theorem. -/
noncomputable def realEtaLimit (x : Real) : Real :=
  if hx : 0 < x then
    Classical.choose
      ((etaTerm_antitone hx.le).tendsto_alternating_series_of_tendsto_zero
        (etaTerm_tendsto_zero hx))
  else
    0

theorem realEtaLimit_tendsto {x : Real} (hx : 0 < x) :
    Filter.Tendsto
      (fun n => Finset.sum (Finset.range n)
        (fun i => (-1 : Real) ^ i * etaTerm x i))
      Filter.atTop (nhds (realEtaLimit x)) := by
  unfold realEtaLimit
  rw [dif_pos hx]
  exact Classical.choose_spec
    ((etaTerm_antitone hx.le).tendsto_alternating_series_of_tendsto_zero
      (etaTerm_tendsto_zero hx))

/-- The alternating eta limit is strictly positive for every positive real
exponent. -/
theorem realEtaLimit_pos {x : Real} (hx : 0 < x) :
    0 < realEtaLimit x := by
  have hLower := (etaTerm_antitone hx.le).alternating_series_le_tendsto
    (realEtaLimit_tendsto hx) 1
  have hTwo : (2 : Real) ^ (-x) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hx)
  simp [etaTerm, Finset.sum_range_succ] at hLower
  norm_num at hLower
  linarith

end

end TS341.Goldbach
