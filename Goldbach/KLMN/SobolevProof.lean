/-
  Goldbach/KLMN/SobolevProof.lean
  Proof of the 1D Sobolev trace inequality on a bounded interval.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

open Real MeasureTheory Set intervalIntegral

/-! ## §1 Young's product inequality -/

theorem young_signed (a b δ : ℝ) (hδ : 0 < δ) :
    2 * a * b ≤ a ^ 2 / δ + δ * b ^ 2 := by
  suffices h : 0 ≤ a ^ 2 / δ + δ * b ^ 2 - 2 * a * b by linarith
  have : a ^ 2 / δ + δ * b ^ 2 - 2 * a * b = (a - δ * b) ^ 2 / δ := by field_simp; ring
  rw [this]; exact div_nonneg (sq_nonneg _) hδ.le

theorem young_abs (a b δ : ℝ) (hδ : 0 < δ) :
    2 * |a * b| ≤ a ^ 2 / δ + δ * b ^ 2 := by
  have h := young_signed (|a|) (|b|) δ hδ
  rw [sq_abs, sq_abs] at h
  calc 2 * |a * b| = 2 * (|a| * |b|) := by rw [abs_mul]
    _ = 2 * |a| * |b| := by ring
    _ ≤ _ := h

/-! ## §2 Helpers -/

theorem uIcc_subset_Icc_of_mem {a b y x : ℝ}
    (hy : y ∈ Icc a b) (hx : x ∈ Icc a b) :
    uIcc y x ⊆ Icc a b := by
  intro t ht; simp only [mem_uIcc] at ht
  constructor
  · rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hy.1, hx.1]
  · rcases ht with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith [hy.2, hx.2]

/-! ## §3 FTC for u² -/

theorem ftc_sq {a b : ℝ} (u : ℝ → ℝ)
    (hu_diff : ∀ t ∈ Icc a b, HasDerivAt u (deriv u t) t)
    (hu_cont : ContinuousOn u (Icc a b))
    (hu'_cont : ContinuousOn (deriv u) (Icc a b))
    {y x : ℝ} (hy : y ∈ Icc a b) (hx : x ∈ Icc a b) :
    u x ^ 2 - u y ^ 2 = ∫ t in y..x, 2 * u t * deriv u t := by
  symm; apply integral_eq_sub_of_hasDerivAt
  · intro t ht
    convert (hu_diff t (uIcc_subset_Icc_of_mem hy hx ht)).pow 2 using 1
    simp [Nat.cast_ofNat, pow_one]
  · exact ((continuousOn_const.mul hu_cont).mul hu'_cont).mono
      (uIcc_subset_Icc_of_mem hy hx) |>.intervalIntegrable

/-! ## §4 Subinterval integral bound -/

theorem subinterval_integral_le {f : ℝ → ℝ} {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_nn : ∀ t ∈ Icc a b, 0 ≤ f t) :
    ∫ t in c..d, f t ≤ ∫ t in a..b, f t := by
  have hf_ac : IntervalIntegrable f volume a c :=
    (hf_cont.mono (by rw [uIcc_of_le hac]; exact Icc_subset_Icc le_rfl (le_trans hcd hdb))).intervalIntegrable
  have hf_cd : IntervalIntegrable f volume c d :=
    (hf_cont.mono (by rw [uIcc_of_le hcd]; exact Icc_subset_Icc hac hdb)).intervalIntegrable
  have hf_db : IntervalIntegrable f volume d b :=
    (hf_cont.mono (by rw [uIcc_of_le hdb]; exact Icc_subset_Icc (le_trans hac hcd) le_rfl)).intervalIntegrable
  set I_ab := ∫ t in a..b, f t; set I_ac := ∫ t in a..c, f t
  set I_cb := ∫ t in c..b, f t; set I_cd := ∫ t in c..d, f t
  set I_db := ∫ t in d..b, f t
  have h1 : 0 ≤ I_ac := integral_nonneg hac fun t ht =>
    hf_nn t ⟨ht.1, le_trans ht.2 (le_trans hcd hdb)⟩
  have h2 : 0 ≤ I_db := integral_nonneg hdb fun t ht =>
    hf_nn t ⟨le_trans (le_trans hac hcd) ht.1, ht.2⟩
  have s1 : I_ac + I_cb = I_ab := integral_add_adjacent_intervals hf_ac (hf_cd.trans hf_db)
  have s2 : I_cd + I_db = I_cb := integral_add_adjacent_intervals hf_cd hf_db
  linarith

/-! ## §5 Key integral bound: |∫_y^x f| ≤ ∫_a^b g when |f| ≤ g pointwise -/

/-- For continuous f, g with |f(t)| ≤ g(t) on [a,b] and g ≥ 0,
    we have |∫_y^x f| ≤ ∫_a^b g for y, x ∈ [a,b]. -/
theorem integral_bound_of_pointwise {f g : ℝ → ℝ} {a b y x : ℝ}
    (_hab : a ≤ b) (hy : y ∈ Icc a b) (hx : x ∈ Icc a b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_nn : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hfg : ∀ t ∈ Icc a b, |f t| ≤ g t) :
    |∫ t in y..x, f t| ≤ ∫ t in a..b, g t := by
  -- Use norm_integral_le_of_norm_le to get ‖∫f‖ ≤ |∫g|
  -- Then bound |∫_y^x g| ≤ ∫_a^b g (since g ≥ 0)
  have hf_int_yx : IntervalIntegrable f volume y x :=
    (hf_cont.mono (uIcc_subset_Icc_of_mem hy hx)).intervalIntegrable
  have hg_int_yx : IntervalIntegrable g volume y x :=
    (hg_cont.mono (uIcc_subset_Icc_of_mem hy hx)).intervalIntegrable
  -- ‖∫_y^x f‖ ≤ |∫_y^x g| (by norm_integral_le_of_norm_le)
  have h1 : ‖∫ t in y..x, f t‖ ≤ |∫ t in y..x, g t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le
    · -- ‖f t‖ ≤ g t ae on uIoc y x
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      apply Filter.Eventually.of_forall
      intro t ht
      simp only [Real.norm_eq_abs]
      exact hfg t (uIcc_subset_Icc_of_mem hy hx (Set.uIoc_subset_uIcc ht))
    · exact hg_int_yx
  rw [Real.norm_eq_abs] at h1
  -- |∫_y^x g| ≤ ∫_a^b g (case split on y ≤ x)
  rcases le_total y x with hyx | hyx
  · -- y ≤ x: ∫_y^x g ≥ 0, so |∫_y^x g| = ∫_y^x g ≤ ∫_a^b g
    have hg_nn_yx : 0 ≤ ∫ t in y..x, g t :=
      integral_nonneg hyx fun t ht => hg_nn t ⟨le_trans hy.1 ht.1, le_trans ht.2 hx.2⟩
    rw [abs_of_nonneg hg_nn_yx] at h1
    exact le_trans h1 (subinterval_integral_le hy.1 hyx hx.2 hg_cont hg_nn)
  · -- y > x: ∫_y^x g = -∫_x^y g ≤ 0, so |∫_y^x g| = ∫_x^y g ≤ ∫_a^b g
    have hg_nn_xy : 0 ≤ ∫ t in x..y, g t :=
      integral_nonneg hyx fun t ht => hg_nn t ⟨le_trans hx.1 ht.1, le_trans ht.2 hy.2⟩
    have hg_neg : ∫ t in y..x, g t ≤ 0 := by
      rw [integral_symm]; linarith
    rw [abs_of_nonpos hg_neg] at h1
    have h2 : -(∫ t in y..x, g t) = ∫ t in x..y, g t := by
      rw [integral_symm]; ring
    rw [h2] at h1
    exact le_trans h1 (subinterval_integral_le hx.1 hyx hy.2 hg_cont hg_nn)

/-! ## §6 Main theorem -/

theorem sobolev_trace_bounded_interval
    {a b : ℝ} (hab : a < b) (u : ℝ → ℝ)
    (hu_diff : ∀ x ∈ Icc a b, HasDerivAt u (deriv u x) x)
    (hu_cont : ContinuousOn u (Icc a b))
    (hu'_cont : ContinuousOn (deriv u) (Icc a b))
    (x : ℝ) (hx : x ∈ Icc a b) :
    (u x) ^ 2 ≤
      (2 / (b - a)) * (∫ t in a..b, (u t) ^ 2) +
      (b - a) * (∫ t in a..b, (deriv u t) ^ 2) := by
  set L := b - a with hL_def
  have hL : 0 < L := sub_pos.mpr hab
  have hab' : a ≤ b := hab.le
  -- Continuity and integrability
  have hu_sq_cont : ContinuousOn (fun t => u t ^ 2) (Icc a b) := hu_cont.pow 2
  have hu'_sq_cont : ContinuousOn (fun t => (deriv u t) ^ 2) (Icc a b) := hu'_cont.pow 2
  have hu_sq_int : IntervalIntegrable (fun t => u t ^ 2) volume a b :=
    (hu_sq_cont.mono (by rw [uIcc_of_le hab'])).intervalIntegrable
  have hu'_sq_int : IntervalIntegrable (fun t => (deriv u t) ^ 2) volume a b :=
    (hu'_sq_cont.mono (by rw [uIcc_of_le hab'])).intervalIntegrable
  -- Name the integrals for linarith
  set Iu := ∫ t in a..b, u t ^ 2
  set Iu' := ∫ t in a..b, (deriv u t) ^ 2
  have hIu_nn : 0 ≤ Iu := integral_nonneg hab' fun t _ => sq_nonneg _
  have hIu'_nn : 0 ≤ Iu' := integral_nonneg hab' fun t _ => sq_nonneg _
  -- Suffices: L · u(x)² ≤ 2·Iu + L²·Iu' (then divide by L)
  suffices h : L * u x ^ 2 ≤ 2 * Iu + L ^ 2 * Iu' by
    have : u x ^ 2 ≤ (2 * Iu + L ^ 2 * Iu') / L := (le_div_iff₀ hL).mpr (by linarith)
    calc u x ^ 2 ≤ (2 * Iu + L ^ 2 * Iu') / L := this
      _ = 2 / L * Iu + L * Iu' := by field_simp; ring
  -- Key claim: ∀ y ∈ [a,b], u(x)² ≤ u(y)² + K
  set K := 1 / L * Iu + L * Iu'
  suffices claim : ∀ y ∈ Icc a b, u x ^ 2 ≤ u y ^ 2 + K by
    -- Average over y: integrate both sides
    have h_mono : ∫ t in a..b, (fun _ : ℝ => u x ^ 2) t ≤
        ∫ t in a..b, (fun t => u t ^ 2 + K) t :=
      integral_mono_on hab' intervalIntegrable_const (hu_sq_int.add intervalIntegrable_const)
        (fun y hy => claim y hy)
    -- LHS = L * u(x)²
    set I_lhs := ∫ t in a..b, (fun _ : ℝ => u x ^ 2) t
    set I_rhs := ∫ t in a..b, (fun t => u t ^ 2 + K) t
    have hI_lhs : I_lhs = L * u x ^ 2 := by
      simp only [I_lhs, intervalIntegral.integral_const, smul_eq_mul, hL_def]
    -- RHS = Iu + L * K
    have hI_rhs : I_rhs = Iu + L * K := by
      simp only [I_rhs]
      have : (fun t => u t ^ 2 + K) = fun t => (fun t => u t ^ 2) t + (fun _ : ℝ => K) t := rfl
      rw [this, intervalIntegral.integral_add hu_sq_int intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, hL_def]
    rw [hI_lhs, hI_rhs] at h_mono
    have hK : L * K = Iu + L ^ 2 * Iu' := by simp only [K]; field_simp; ring
    linarith
  -- Prove claim: ∀ y, u(x)² ≤ u(y)² + K
  intro y hy
  have hftc := ftc_sq u hu_diff hu_cont hu'_cont hy hx
  -- Need: ∫_y^x 2uu' ≤ K
  suffices hint : ∫ t in y..x, 2 * u t * deriv u t ≤ K by linarith
  -- Use integral_bound_of_pointwise with f = 2uu', g = u²/L + L(u')²
  have h2uu'_cont : ContinuousOn (fun t => 2 * u t * deriv u t) (Icc a b) :=
    (continuousOn_const.mul hu_cont).mul hu'_cont
  have hbound_cont : ContinuousOn (fun t => u t ^ 2 / L + L * (deriv u t) ^ 2) (Icc a b) :=
    (hu_sq_cont.div_const L).add (continuousOn_const.mul hu'_sq_cont)
  have hbound_nn : ∀ t ∈ Icc a b, 0 ≤ u t ^ 2 / L + L * (deriv u t) ^ 2 :=
    fun t _ => add_nonneg (div_nonneg (sq_nonneg _) hL.le) (mul_nonneg hL.le (sq_nonneg _))
  have hYoung : ∀ t ∈ Icc a b, |2 * u t * deriv u t| ≤ u t ^ 2 / L + L * (deriv u t) ^ 2 := by
    intro t _
    have := young_abs (u t) (deriv u t) L hL
    rw [show 2 * u t * deriv u t = 2 * (u t * deriv u t) from by ring]
    calc |2 * (u t * deriv u t)| = |2| * |u t * deriv u t| := abs_mul 2 _
      _ = 2 * |u t * deriv u t| := by rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ _ := this
  have h_abs_bound : |∫ t in y..x, 2 * u t * deriv u t| ≤
      ∫ t in a..b, (u t ^ 2 / L + L * (deriv u t) ^ 2) :=
    integral_bound_of_pointwise hab' hy hx h2uu'_cont hbound_cont hbound_nn hYoung
  -- ∫_a^b (u²/L + L(u')²) = K
  have h_eq_K : ∫ t in a..b, (u t ^ 2 / L + L * (deriv u t) ^ 2) = K := by
    have : (fun t => u t ^ 2 / L + L * (deriv u t) ^ 2) =
        fun t => (1 / L) * (u t ^ 2) + L * ((deriv u t) ^ 2) := by ext; ring
    rw [this, intervalIntegral.integral_add
          (hu_sq_int.const_mul _) (hu'_sq_int.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  calc ∫ t in y..x, 2 * u t * deriv u t
      ≤ |∫ t in y..x, 2 * u t * deriv u t| := le_abs_self _
    _ ≤ ∫ t in a..b, (u t ^ 2 / L + L * (deriv u t) ^ 2) := h_abs_bound
    _ = K := h_eq_K