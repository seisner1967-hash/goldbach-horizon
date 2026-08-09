import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic
import TS.Goldbach.Strong.TS327.PositiveSymmetryAdapter
import TS.Goldbach.Strong.TS341.PairedEtaReal

namespace TS341.Goldbach

noncomputable section

open Complex Filter Set Topology

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def modTwoOne (_ : ZMod 2) : Complex := 1

private def modTwoDelta (j : ZMod 2) : Complex :=
  if j = 0 then 1 else 0

private def modTwoSign (j : ZMod 2) : Complex :=
  if j = 0 then 1 else -1

private theorem modTwoSign_eq_stdAddChar :
    modTwoSign = fun j : ZMod 2 => ZMod.stdAddChar j := by
  funext j
  fin_cases j
  next => simp [modTwoSign]
  next =>
    change (-1 : Complex) = ZMod.stdAddChar ((1 : Int) : ZMod 2)
    rw [ZMod.stdAddChar_coe (N := 2) 1]
    calc
      (-1 : Complex) = Complex.exp (Real.pi * Complex.I) :=
        Complex.exp_pi_mul_I.symm
      _ = Complex.exp
          ((2 : Complex) * Real.pi * Complex.I * (1 : Int) / (2 : Nat)) := by
        congr 1
        norm_num
        ring

private theorem modTwoSign_decompose :
    modTwoSign = fun j => 2 * modTwoDelta j - modTwoOne j := by
  funext j
  fin_cases j <;> norm_num [modTwoSign, modTwoDelta, modTwoOne]

private theorem LFunction_modTwoOne_eq_riemannZeta
    {s : Complex} (hs : Not (s = 1)) :
    ZMod.LFunction modTwoOne s = riemannZeta s := by
  let U : Set Complex := {z | Not (z = 1)}
  let V : Set Complex := {z | 1 < z.re}
  let f := ZMod.LFunction modTwoOne
  let g := riemannZeta
  have hUo : IsOpen U := by
    have hUeq : U = ({(1 : Complex)} : Set Complex).compl := by
      ext z
      change (Not (z = 1)) <-> Membership.mem ({(1 : Complex)} : Set Complex).compl z
      constructor
      next =>
        intro h
        intro hz
        exact h (Set.mem_singleton_iff.mp hz)
      next =>
        intro h
        intro hz
        exact h (Set.mem_singleton_iff.mpr hz)
    rw [hUeq]
    exact isOpen_compl_singleton
  have hf : AnalyticOnNhd Complex f U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu => ?_) hUo
    exact (ZMod.differentiableAt_LFunction modTwoOne u
      (Or.inl (by simpa [U] using hu))).differentiableWithinAt
  have hg : AnalyticOnNhd Complex g U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu => ?_) hUo
    exact (differentiableAt_riemannZeta
      (by simpa [U] using hu)).differentiableWithinAt
  have hUc : IsPreconnected U := by
    simpa [U] using
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : Complex)).isPreconnected
  have hV : Membership.mem (nhds (2 : Complex)) V :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num [V])
  have hTwo : Membership.mem U (2 : Complex) := by norm_num [U]
  have hsU : Membership.mem U s := by simpa [U] using hs
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hTwo ?_ hsU
  filter_upwards [hV] with z hz
  dsimp only [f, g]
  rw [ZMod.LFunction_eq_LSeries modTwoOne hz]
  simpa [modTwoOne] using LSeries_one_eq_riemannZeta hz

private theorem LFunction_modTwoDelta (s : Complex) :
    ZMod.LFunction modTwoDelta s =
      (2 : Complex) ^ (-s) * riemannZeta s := by
  simp [ZMod.LFunction, modTwoDelta, HurwitzZeta.hurwitzZeta_zero]

private theorem LFunction_modTwoSign (s : Complex) :
    ZMod.LFunction modTwoSign s =
      2 * ZMod.LFunction modTwoDelta s -
        ZMod.LFunction modTwoOne s := by
  rw [modTwoSign_decompose]
  simp only [ZMod.LFunction]
  simp_rw [sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
  ring

/-- Analytic eta is the standard factor times zeta away from the removable
point `s = 1`. -/
theorem expZeta_half_eq_factor_mul_riemannZeta
    {s : Complex} (hs : Not (s = 1)) :
    HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s =
      ((2 : Complex) ^ (1 - s) - 1) * riemannZeta s := by
  rw [<- ZMod.LFunction_stdAddChar_eq_expZeta (1 : ZMod 2) s
      (Or.inl (by norm_num))]
  simp only [one_mul]
  rw [<- modTwoSign_eq_stdAddChar,
    LFunction_modTwoSign,
    LFunction_modTwoDelta,
    LFunction_modTwoOne_eq_riemannZeta hs]
  rw [show (1 : Complex) - s = 1 + (-s) by ring,
    Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  ring

/-- Real-axis nonvanishing on the open critical interval is sufficient for
the TS327 zero-ordinate premise, uniformly in the truncation height. -/
private theorem noZeroOrdinateInTruncation_of_realStripNonvanishing
    (hReal : forall x : Real,
      0 < x -> x < 1 -> Not (riemannZeta (x : Complex) = 0))
    (H : Nat) :
    TS327.Goldbach.NoZeroOrdinateInTruncation H := by
  intro rho hRho hIm
  have hStrip :=
    TS264.Goldbach.concreteZero_in_critical_strip rho.property
  have hValue : rho.1 = (rho.1.re : Complex) := by
    apply Complex.ext
    next => simp
    next => simp [hIm]
  have hZeta : riemannZeta (rho.1.re : Complex) = 0 := by
    rw [<- hValue]
    exact TS264.Goldbach.concreteZero_is_zeta_zero rho.property
  exact (hReal rho.1.re hStrip.1 hStrip.2) hZeta

/-- The correctly signed eta representation rules out real zeros of Riemann
zeta in the open critical interval. -/
theorem riemannZeta_real_ne_zero
    {x : Real} (hx0 : 0 < x) (hx1 : x < 1) :
    Not (riemannZeta (x : Complex) = 0) := by
  intro hZeta
  have hxNeOne : Not ((x : Complex) = 1) := by
    intro hx
    have hxRe := congrArg Complex.re hx
    norm_num at hxRe
    linarith
  have hFactor := expZeta_half_eq_factor_mul_riemannZeta hxNeOne
  rw [hZeta, mul_zero] at hFactor
  have hEta := expZeta_half_eq_neg_realEtaLimit hx0 hx1
  have hNegLimitZero : -(realEtaLimit x : Complex) = 0 :=
    hEta.symm.trans hFactor
  have hLimitZero : (realEtaLimit x : Complex) = 0 :=
    neg_eq_zero.mp hNegLimitZero
  have hLimitZeroReal : realEtaLimit x = 0 :=
    Complex.ofReal_eq_zero.mp hLimitZero
  exact (ne_of_gt (realEtaLimit_pos hx0)) hLimitZeroReal

/-- Permanent TS341 certificate: no concrete Riemann zeta zero in the
critical strip has zero ordinate, uniformly in the truncation height. -/
theorem noZeroOrdinateInTruncation (H : Nat) :
    TS327.Goldbach.NoZeroOrdinateInTruncation H :=
  noZeroOrdinateInTruncation_of_realStripNonvanishing
    (fun x hx0 hx1 => riemannZeta_real_ne_zero (x := x) hx0 hx1) H

end

end TS341.Goldbach
