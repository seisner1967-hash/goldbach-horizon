import GammaPrerequisites22

/- Second module in source preparation; never compiled. The moments below are
   exact analytic integrals, independent of a spectral measure or zero count. -/

noncomputable section
open Set MeasureTheory

namespace GoldbachContinuous22

theorem integrable_laplace_moment (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(a * t))) (Ioi 0) := by
  have h := real_laplace_integrable (show 0 < (k : ℝ) + 1 by positivity) ha
  simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using h

theorem integral_laplace_moment (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-(a * t))) =
      (k.factorial : ℝ) / a ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show 0 < (k : ℝ) + 1 by positivity) ha
  rw [add_sub_cancel_right, Real.Gamma_nat_eq_factorial] at h
  simp_rw [Real.rpow_natCast] at h
  have hpow : (1 / a) ^ ((k : ℝ) + 1) = (1 / a) ^ (k + 1) := by
    rw [← Nat.cast_succ, Real.rpow_natCast]
  rw [hpow] at h
  simpa only [one_div_pow, one_div, div_eq_mul_inv, mul_comm] using h

def quadraticLaplace (a c0 c1 c2 t : ℝ) : ℝ :=
  (c0 + c1 * t + c2 * t ^ 2) * Real.exp (-(a * t))

theorem quadraticLaplace_expand (a c0 c1 c2 t : ℝ) :
    quadraticLaplace a c0 c1 c2 t =
      c0 * (t ^ 0 * Real.exp (-(a * t))) +
      c1 * (t ^ 1 * Real.exp (-(a * t))) +
      c2 * (t ^ 2 * Real.exp (-(a * t))) := by
  simp only [quadraticLaplace, pow_zero, pow_one]
  ring

theorem quadraticLaplace_integrable {a : ℝ} (ha : 0 < a) (c0 c1 c2 : ℝ) :
    IntegrableOn (quadraticLaplace a c0 c1 c2) (Ioi 0) := by
  have h0 := (integrable_laplace_moment 0 ha).const_mul c0
  have h1 := (integrable_laplace_moment 1 ha).const_mul c1
  have h2 := (integrable_laplace_moment 2 ha).const_mul c2
  apply (h0.add h1 |>.add h2).congr
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t _
  exact (quadraticLaplace_expand a c0 c1 c2 t).symm

/-- Closed evaluation, with no unspecified norm, quadrature, or constant. -/
theorem integral_quadraticLaplace {a : ℝ} (ha : 0 < a) (c0 c1 c2 : ℝ) :
    (∫ t : ℝ in Ioi 0, quadraticLaplace a c0 c1 c2 t) =
      c0 / a + c1 / a ^ 2 + 2 * c2 / a ^ 3 := by
  have h0 := (integrable_laplace_moment 0 ha).const_mul c0
  have h1 := (integrable_laplace_moment 1 ha).const_mul c1
  have h2 := (integrable_laplace_moment 2 ha).const_mul c2
  simp_rw [quadraticLaplace_expand]
  rw [integral_add (h0.add h1) h2, integral_add h0 h1,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_laplace_moment 0 ha, integral_laplace_moment 1 ha,
    integral_laplace_moment 2 ha]
  norm_num <;> ring

/-- Exact integrated polynomial majorant underlying the spectral exponential tail. -/
theorem integral_heat_polynomial {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    (∫ u : ℝ in Ioi 0,
      a * (T * Real.log T + (Real.log T + 1) * u + u ^ 2 / (2 * T)) *
        Real.exp (-(a * (T + u)))) =
      Real.exp (-(a * T)) *
        (T * Real.log T + (Real.log T + 1) / a + 1 / (a ^ 2 * T)) := by
  have hfun : (fun u : ℝ =>
      a * (T * Real.log T + (Real.log T + 1) * u + u ^ 2 / (2 * T)) *
        Real.exp (-(a * (T + u)))) =
      (fun u : ℝ => a * Real.exp (-(a * T)) *
        quadraticLaplace a (T * Real.log T) (Real.log T + 1) (1 / (2 * T)) u) := by
    funext u
    have hexp : Real.exp (-(a * (T + u))) =
        Real.exp (-(a * T)) * Real.exp (-(a * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    unfold quadraticLaplace
    ring
  rw [hfun, integral_const_mul, integral_quadraticLaplace ha]
  field_simp [ha.ne', hT.ne']
  ring

/-- Exact integrated tangent majorant underlying the prime-side exponential tail. -/
theorem integral_prime_polynomial {Y X : ℝ} (hY : 0 < Y) (hX : 0 < X) :
    (∫ u : ℝ in Ioi 0,
      ((X + u) / Y) * (Real.log X + u / X) * Real.exp (-(X + u) / Y)) =
      Real.exp (-X / Y) * ((X + Y) * Real.log X + Y + 2 * Y ^ 2 / X) := by
  have hfun : (fun u : ℝ =>
      ((X + u) / Y) * (Real.log X + u / X) * Real.exp (-(X + u) / Y)) =
      (fun u : ℝ => Real.exp (-X / Y) / Y *
        quadraticLaplace (1 / Y) (X * Real.log X) (Real.log X + 1) (1 / X) u) := by
    funext u
    have hexp : Real.exp (-(X + u) / Y) =
        Real.exp (-X / Y) * Real.exp (-((1 / Y) * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    unfold quadraticLaplace
    field_simp [hY.ne', hX.ne']
    ring
  rw [hfun, integral_const_mul, integral_quadraticLaplace (one_div_pos.mpr hY)]
  field_simp [hY.ne', hX.ne']
  ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.integrable_laplace_moment
#print axioms GoldbachContinuous22.integral_laplace_moment
#print axioms GoldbachContinuous22.quadraticLaplace
#print axioms GoldbachContinuous22.quadraticLaplace_expand
#print axioms GoldbachContinuous22.quadraticLaplace_integrable
#print axioms GoldbachContinuous22.integral_quadraticLaplace
#print axioms GoldbachContinuous22.integral_heat_polynomial
#print axioms GoldbachContinuous22.integral_prime_polynomial
