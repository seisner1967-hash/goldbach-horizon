import TS.Goldbach.Strong.TS310.ScalarMellinInversion

/-!
# TS310 - Scalar Mellin-Perron inversion

This file combines the scalar inversion theorem with the absolutely convergent
von Mangoldt L-series on `re(s) = c > 1`. A summable product majorant justifies
the exchange of the natural-number `tsum` and the full real-line integral.
Each scalar integral then gives the exact triangle-spline weight.

The final theorems inhabit the TS293 Perron inversion contract and combine it
with the unconditional TS309 residue theorem. Thus the canonical truncated
explicit identity is unconditional. No infinite-height limit, infinite
explicit formula, Gallagher estimate, OTSA bridge, or Goldbach theorem is
claimed here.
-/

noncomputable section

namespace TS310
namespace Goldbach

open Complex Filter MeasureTheory Metric Set
open scoped BigOperators Interval

noncomputable def vonMangoldtPerronTerm
    (x : Nat) (c : Real) (n : Nat) (t : Real) : Complex :=
  LSeries.term TS298.Goldbach.vM
      ((c : Complex) + (t : Complex) * I) n *
    (x : Complex) ^ ((c : Complex) + (t : Complex) * I) *
    TS257.Goldbach.triangleSplineMellinKernel
      ((c : Complex) + (t : Complex) * I)

theorem norm_LSeries_term_vertical_eq
    (c t : Real) (n : Nat) :
    norm
        (LSeries.term TS298.Goldbach.vM
          ((c : Complex) + (t : Complex) * I) n) =
      norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) := by
  simp only [LSeries.norm_term_eq]
  congr 1
  simp

theorem triangleSplineMellinKernel_vertical_norm_le
    {c : Real} (hc : 1 <= c) (t : Real) :
    norm
        (TS257.Goldbach.triangleSplineMellinKernel
          ((c : Complex) + (t : Complex) * I)) <=
      1 / (1 + t ^ 2) := by
  unfold TS257.Goldbach.triangleSplineMellinKernel
  rw [norm_div, norm_one, norm_mul]
  have hbase : 0 < 1 + t ^ 2 := by positivity
  have hprod := one_add_sq_le_vertical_denominator_norm_of_one_le
    (sigma := c) (t := t) hc
  simpa [one_div] using one_div_le_one_div_of_le hbase hprod

theorem vonMangoldtPerronTerm_norm_le
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 <= c)
    (n : Nat) (t : Real) :
    norm (vonMangoldtPerronTerm x c n t) <=
      norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
        (x : Real) ^ c * (1 / (1 + t ^ 2)) := by
  unfold vonMangoldtPerronTerm
  rw [norm_mul, norm_mul, norm_LSeries_term_vertical_eq]
  rw [Complex.norm_natCast_cpow_of_pos hx]
  simp only [ofReal_re, add_re, mul_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  have hfactor : 0 <=
      norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
        (x : Real) ^ c :=
    mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg x) c)
  exact mul_le_mul_of_nonneg_left
    (triangleSplineMellinKernel_vertical_norm_le hc t)
    hfactor

theorem continuous_vonMangoldtPerronTerm
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 <= c) (n : Nat) :
    Continuous (vonMangoldtPerronTerm x c n) := by
  by_cases hn : n = 0
  . subst n
    unfold vonMangoldtPerronTerm
    simp only [LSeries.term_zero, zero_mul]
    exact continuous_const
  . have hnC : Not ((n : Complex) = 0) := by exact_mod_cast hn
    letI : NeZero (n : Complex) := { out := hnC }
    have hTerm : Continuous
        (fun t : Real =>
          LSeries.term TS298.Goldbach.vM
            ((c : Complex) + (t : Complex) * I) n) := by
      simp_rw [LSeries.term_of_ne_zero hn]
      rw [continuous_iff_continuousAt]
      intro t
      have hz : ContinuousAt
          (fun u : Real => (c : Complex) + (u : Complex) * I) t := by
        fun_prop
      exact continuousAt_const.div
        (hz.const_cpow (Or.inl hnC))
        (by
          intro hzero
          exact hnC (Complex.cpow_eq_zero_iff _ _ |>.mp hzero).1)
    have hxR : (0 : Real) < (x : Real) := by exact_mod_cast hx
    have hScalar := continuous_scalarMellinVerticalIntegrand hxR
      (show Not (c = 0) by linarith) (show Not (c = -1) by linarith)
    convert hTerm.mul hScalar using 1
    funext t
    unfold vonMangoldtPerronTerm scalarMellinVerticalIntegrand
      scalarMellinIntegrand TS257.Goldbach.triangleSplineMellinKernel
    norm_num
    simp only [div_eq_mul_inv, mul_inv]
    ring

theorem integrable_vonMangoldtPerronTerm
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 <= c) (n : Nat) :
    Integrable (vonMangoldtPerronTerm x c n) := by
  have hBound : Integrable
      (fun t : Real =>
        norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
          (x : Real) ^ c * (1 / (1 + t ^ 2))) := by
    simpa [mul_assoc, one_div] using
      integrable_inv_one_add_sq.const_mul
        (norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
          (x : Real) ^ c)
  refine Integrable.mono' hBound ?_ ?_
  . exact (continuous_vonMangoldtPerronTerm hx hc n).aestronglyMeasurable
  . exact Filter.Eventually.of_forall (vonMangoldtPerronTerm_norm_le hx hc n)

theorem integral_norm_vonMangoldtPerronTerm_le
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 <= c) (n : Nat) :
    integral (volume : Measure Real)
        (fun t => norm (vonMangoldtPerronTerm x c n t)) <=
      norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
        (x : Real) ^ c * scalarCauchyMass := by
  have hBound : Integrable
      (fun t : Real =>
        norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
          (x : Real) ^ c * (1 / (1 + t ^ 2))) := by
    simpa [mul_assoc, one_div] using
      integrable_inv_one_add_sq.const_mul
        (norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
          (x : Real) ^ c)
  refine (integral_mono (integrable_vonMangoldtPerronTerm hx hc n).norm
    hBound ?_).trans_eq ?_
  . exact vonMangoldtPerronTerm_norm_le hx hc n
  . unfold scalarCauchyMass
    have h : integral (volume : Measure Real)
          (fun t : Real =>
            (norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
              (x : Real) ^ c) * (1 / (1 + t ^ 2))) =
        (norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
          (x : Real) ^ c) *
          integral (volume : Measure Real) (fun t : Real => 1 / (1 + t ^ 2)) := by
      exact integral_mul_left _ _
    simpa [mul_assoc] using h

theorem summable_integral_norm_vonMangoldtPerronTerm
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 < c) :
    Summable
      (fun n : Nat =>
        integral (volume : Measure Real)
          (fun t => norm (vonMangoldtPerronTerm x c n t))) := by
  have hTerm : Summable
      (fun n : Nat => norm (LSeries.term TS298.Goldbach.vM (c : Complex) n)) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (c : Complex)) (by simpa using hc)).norm
  have hMajorant : Summable
      (fun n : Nat =>
        norm (LSeries.term TS298.Goldbach.vM (c : Complex) n) *
          ((x : Real) ^ c * scalarCauchyMass)) :=
    hTerm.mul_right _
  exact hMajorant.of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => by
      simpa [mul_assoc] using
        integral_norm_vonMangoldtPerronTerm_le hx hc.le n)

theorem tsum_vonMangoldtPerronTerm
    (x : Nat) {c : Real} (hc : 1 < c) (t : Real) :
    tsum (fun n : Nat => vonMangoldtPerronTerm x c n t) =
      TS293.Goldbach.triangleSplineVonMangoldtLSeriesIntegrand x
        ((c : Complex) + (t : Complex) * I) := by
  have hSum := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex) + (t : Complex) * I) (by simpa using hc)
  unfold vonMangoldtPerronTerm
    TS293.Goldbach.triangleSplineVonMangoldtLSeriesIntegrand LSeries
    TS298.Goldbach.vM
  rw [tsum_mul_right, tsum_mul_right]

theorem integral_tsum_vonMangoldtPerronTerm
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 < c) :
    tsum (fun n : Nat =>
        integral (volume : Measure Real) (vonMangoldtPerronTerm x c n)) =
      integral (volume : Measure Real)
        (fun t : Real =>
          TS293.Goldbach.triangleSplineVonMangoldtLSeriesIntegrand x
            ((c : Complex) + (t : Complex) * I)) := by
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => integrable_vonMangoldtPerronTerm hx hc.le n)
    (summable_integral_norm_vonMangoldtPerronTerm hx hc)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => tsum_vonMangoldtPerronTerm x hc t)

theorem integral_triangleSplinePerronIntegrand_eq_tsum
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 < c) :
    integral (volume : Measure Real)
        (fun t : Real =>
          TS293.Goldbach.triangleSplinePerronIntegrand x
            ((c : Complex) + (t : Complex) * I)) =
      tsum (fun n : Nat =>
        integral (volume : Measure Real) (vonMangoldtPerronTerm x c n)) := by
  rw [integral_tsum_vonMangoldtPerronTerm hx hc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t =>
    TS293.Goldbach.triangleSplinePerronIntegrand_eq_vonMangoldtLSeries
      x (by simpa using hc))

theorem nat_ratio_cpow
    {x n : Nat} (hx : 0 < x) (hn : 0 < n) (z : Complex) :
    (((x : Real) / (n : Real) : Real) : Complex) ^ z =
      (x : Complex) ^ z / (n : Complex) ^ z := by
  have hxR : (0 : Real) < (x : Real) := by exact_mod_cast hx
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hqR : (0 : Real) < (x : Real) / (n : Real) := div_pos hxR hnR
  have hxC : Not ((x : Complex) = 0) := by exact_mod_cast ne_of_gt hx
  have hnC : Not ((n : Complex) = 0) := by exact_mod_cast ne_of_gt hn
  have hqC : Not ((((x : Real) / (n : Real) : Real) : Complex) = 0) := by
    exact_mod_cast ne_of_gt hqR
  rw [Complex.cpow_def_of_ne_zero hqC,
    Complex.cpow_def_of_ne_zero hxC,
    Complex.cpow_def_of_ne_zero hnC]
  rw [<- Complex.exp_sub]
  congr 1
  rw [<- Complex.ofReal_log hqR.le]
  rw [<- Complex.ofReal_natCast x, <- Complex.ofReal_natCast n]
  rw [<- Complex.ofReal_log hxR.le,
    <- Complex.ofReal_log hnR.le,
    Real.log_div hxR.ne' hnR.ne']
  push_cast
  ring

theorem vonMangoldtPerronTerm_eq_scalar
    {x n : Nat} (hx : 0 < x) (hn : 0 < n)
    (c t : Real) :
    vonMangoldtPerronTerm x c n t =
      TS298.Goldbach.vM n *
        scalarMellinVerticalIntegrand
          ((x : Real) / (n : Real)) c t := by
  have hn0 : Not (n = 0) := ne_of_gt hn
  unfold vonMangoldtPerronTerm scalarMellinVerticalIntegrand
    scalarMellinIntegrand TS257.Goldbach.triangleSplineMellinKernel
  rw [LSeries.term_of_ne_zero hn0]
  have hRatio := nat_ratio_cpow hx hn
    ((c : Complex) + (t : Complex) * I)
  rw [hRatio]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem integral_vonMangoldtPerronTerm_eq_scalar
    {x n : Nat} (hx : 0 < x) (hn : 0 < n) (c : Real) :
    integral (volume : Measure Real) (vonMangoldtPerronTerm x c n) =
      TS298.Goldbach.vM n *
        scalarMellinVerticalIntegral ((x : Real) / (n : Real)) c := by
  rw [show
    vonMangoldtPerronTerm x c n =
      (fun t : Real =>
        TS298.Goldbach.vM n *
          scalarMellinVerticalIntegrand ((x : Real) / (n : Real)) c t) by
      funext t
      exact vonMangoldtPerronTerm_eq_scalar hx hn c t]
  unfold scalarMellinVerticalIntegral
  exact integral_mul_left _ _

theorem integral_vonMangoldtPerronTerm
    {x n : Nat} (hx : 0 < x) (hn : 0 < n)
    {c : Real} (hc : 1 < c) :
    integral (volume : Measure Real) (vonMangoldtPerronTerm x c n) =
      if n < x then
        (2 * Real.pi : Complex) * TS298.Goldbach.vM n *
          (1 - ((n : Real) / (x : Real) : Real))
      else 0 := by
  rw [integral_vonMangoldtPerronTerm_eq_scalar hx hn]
  have hxR : (0 : Real) < (x : Real) := by exact_mod_cast hx
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  rw [triangleSplineScalarMellinInversion (div_pos hxR hnR) hc]
  by_cases hnx : n < x
  . rw [if_pos hnx, if_pos ((one_lt_div hnR).2 (by exact_mod_cast hnx))]
    rw [Complex.cpow_neg_one]
    norm_num [TS298.Goldbach.vM]
    ring
  . rw [if_neg hnx]
    have hnot : Not (1 < (x : Real) / (n : Real)) := by
      rw [one_lt_div hnR]
      exact_mod_cast hnx
    rw [if_neg hnot]
    ring

noncomputable def normalizedArithmeticPerronTerm
    (x n : Nat) : Real :=
  if n < x then
    TS184.Goldbach.mathlibVonMangoldtWeight n *
      (1 - (n : Real) / (x : Real))
  else 0

theorem integral_vonMangoldtPerronTerm_all
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 < c) (n : Nat) :
    integral (volume : Measure Real) (vonMangoldtPerronTerm x c n) =
      (2 * Real.pi : Complex) *
        (normalizedArithmeticPerronTerm x n : Complex) := by
  by_cases hn : n = 0
  . subst n
    have hzero : vonMangoldtPerronTerm x c 0 = (fun _ : Real => 0) := by
      funext t
      simp [vonMangoldtPerronTerm]
    rw [hzero]
    simp [normalizedArithmeticPerronTerm,
      TS184.Goldbach.mathlibVonMangoldtWeight, TS298.Goldbach.vM, hx]
  . have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    rw [integral_vonMangoldtPerronTerm hx hnPos hc]
    unfold normalizedArithmeticPerronTerm
    by_cases hnx : n < x
    . rw [if_pos hnx, if_pos hnx]
      unfold TS184.Goldbach.mathlibVonMangoldtWeight TS298.Goldbach.vM
      push_cast
      ring
    . rw [if_neg hnx, if_neg hnx]
      simp

theorem normalizedArithmeticPerronTerm_eq_zero_of_not_lt
    (x n : Nat) (h : Not (n < x)) :
    normalizedArithmeticPerronTerm x n = 0 := by
  simp [normalizedArithmeticPerronTerm, h]

theorem tsum_normalizedArithmeticPerronTerm
    {x : Nat} (hx : 0 < x) :
    tsum (normalizedArithmeticPerronTerm x) =
      TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x := by
  rw [tsum_eq_sum (s := Finset.range x) (fun n hn =>
    normalizedArithmeticPerronTerm_eq_zero_of_not_lt x n
      (by simpa using hn))]
  have hRange :
      Finset.sum (Finset.range x) (normalizedArithmeticPerronTerm x) =
        Finset.sum (Finset.range x)
          (fun n =>
            TS184.Goldbach.mathlibVonMangoldtWeight n *
              (1 - (n : Real) / (x : Real))) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [normalizedArithmeticPerronTerm, Finset.mem_range.mp hn]
  rw [hRange]
  rw [TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum_affine hx]
  rw [Finset.sum_range_succ]
  have hxR0 : Not ((x : Real) = 0) := by exact_mod_cast ne_of_gt hx
  simp [div_self hxR0]

theorem tsum_integral_vonMangoldtPerronTerm
    {x : Nat} (hx : 0 < x) {c : Real} (hc : 1 < c) :
    tsum (fun n : Nat =>
        integral (volume : Measure Real) (vonMangoldtPerronTerm x c n)) =
      (2 * Real.pi : Complex) *
        (TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
          Complex) := by
  simp_rw [integral_vonMangoldtPerronTerm_all hx hc]
  rw [tsum_mul_left]
  rw [show tsum (fun n : Nat =>
      (normalizedArithmeticPerronTerm x n : Complex)) =
      (TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
        Complex) by
    rw [<- Complex.ofReal_tsum]
    congr 1
    exact tsum_normalizedArithmeticPerronTerm hx]

theorem triangleSplinePerronInversion
    (x : Nat) (c : Real) (hx : 0 < x) (hc : 1 < c) :
    ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
        Real) : Complex) =
      TS293.Goldbach.fullPerronRightLineValue x c := by
  unfold TS293.Goldbach.fullPerronRightLineValue
    TS293.Goldbach.normalizeContourIntegral
  rw [integral_triangleSplinePerronIntegrand_eq_tsum hx hc]
  rw [tsum_integral_vonMangoldtPerronTerm hx hc]
  have hPi : Not ((Real.pi : Complex) = 0) := by
    exact_mod_cast Real.pi_ne_zero
  have hI : Not (I = 0) := I_ne_zero
  field_simp [hPi, hI]
  ring

theorem triangleSplinePerronInversionStatement :
    TS293.Goldbach.TriangleSplinePerronInversionStatement := by
  intro x c hx hc
  exact triangleSplinePerronInversion x c hx hc

theorem canonical_truncatedPerronExplicitIdentity_complex
    (x T : Nat) (hx : 0 < x)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) :
    ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
        Real) : Complex) =
      (x : Complex) / 2 -
        TS292.Goldbach.truncatedInfiniteZeroContribution x T +
          TS293.Goldbach.triangleSplineContourResidualComplex x T
            D.toCleanPerronContourData
            (TS308.Goldbach.completePerronResidueCensus
              x T hx D).exceptional.inventory := by
  exact TS293.Goldbach.truncatedPerronExplicitIdentity_complex
    x T hx D.toCleanPerronContourData
    (TS308.Goldbach.completePerronResidueCensus
      x T hx D).exceptional.inventory
    triangleSplinePerronInversionStatement
    (TS309.Goldbach.canonical_triangleSplineRectangleResidueStatement
      x T hx D)

theorem canonical_truncatedPerronExplicitIdentity
    (x T : Nat) (hx : 0 < x)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) :
    TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x =
      TS293.Goldbach.triangleSplinePerronMainTerm x -
        (TS292.Goldbach.truncatedInfiniteZeroContribution x T).re +
          TS293.Goldbach.triangleSplineContourResidual x T
            D.toCleanPerronContourData
            (TS308.Goldbach.completePerronResidueCensus
              x T hx D).exceptional.inventory := by
  exact TS293.Goldbach.truncatedPerronExplicitIdentity
    x T hx D.toCleanPerronContourData
    (TS308.Goldbach.completePerronResidueCensus
      x T hx D).exceptional.inventory
    triangleSplinePerronInversionStatement
    (TS309.Goldbach.canonical_triangleSplineRectangleResidueStatement
      x T hx D)

structure ScalarMellinPerronInversionLedger where
  scalar_rectangle_inversion_proved : True
  endpoint_kernel_kept_integrable : True
  von_mangoldt_tonelli_exchange_proved : True
  n_zero_isolated : True
  arithmetic_triangle_weight_identified : True
  perron_inversion_proved : True
  truncated_explicit_identity_proved : True
  infinite_height_limit_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def scalarMellinPerronInversionLedger :
    ScalarMellinPerronInversionLedger where
  scalar_rectangle_inversion_proved := True.intro
  endpoint_kernel_kept_integrable := True.intro
  von_mangoldt_tonelli_exchange_proved := True.intro
  n_zero_isolated := True.intro
  arithmetic_triangle_weight_identified := True.intro
  perron_inversion_proved := True.intro
  truncated_explicit_identity_proved := True.intro
  infinite_height_limit_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS310
