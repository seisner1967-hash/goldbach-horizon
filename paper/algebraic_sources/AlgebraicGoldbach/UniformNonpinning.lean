import AlgebraicGoldbach.UniformCountermodel

namespace AlgebraicGoldbach

theorem uniform_model_selects_composite_nine (N : ℕ) (hN : 24 ≤ N) :
    bit N 9 = 1 ∧ primeBit 9 = 0 := by
  have hb := high_bounds N
  have hs : selected N 9 := by
    right
    left
    refine ⟨by omega, by omega, by decide, ?_⟩
    omega
  constructor
  · simp [bit, hs]
  · norm_num [primeBit]

theorem uniform_model_differs_from_primes (N : ℕ) (hN : 24 ≤ N) :
    bit N ≠ primeBit := by
  intro he
  have he9 := congrFun he 9
  obtain ⟨h1, h0⟩ := uniform_model_selects_composite_nine N hN
  omega

end AlgebraicGoldbach
