theorem goldbach_binary : ∀ n : ℕ, Even n → 2 < n →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n
