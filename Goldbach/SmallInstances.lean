/-
  Goldbach/SmallInstances.lean
  Vérification machine-certifiée des premiers entiers pairs.
  0 sorry. Corrections vs GPT v1 :
    - Import corrigé : Goldbach.Basic (pas HorizonGoldbach.Basic)
    - Constructeur GoldbachAt : ⟨p, q, by decide, by decide, by norm_num⟩
    - by decide pour Nat.Prime (pas by norm_num)
    - verifiedUpTo_20 : traitement explicite des impairs via omega
-/
import Goldbach.Basic
import Mathlib.Tactic

namespace Goldbach

-- Cas individuels ──────────────────────────────────────────────────
theorem goldbach_4   : GoldbachAt 4   := ⟨2, 2,  by decide, by decide, by norm_num⟩
theorem goldbach_6   : GoldbachAt 6   := ⟨3, 3,  by decide, by decide, by norm_num⟩
theorem goldbach_8   : GoldbachAt 8   := ⟨3, 5,  by decide, by decide, by norm_num⟩
theorem goldbach_10  : GoldbachAt 10  := ⟨3, 7,  by decide, by decide, by norm_num⟩
theorem goldbach_12  : GoldbachAt 12  := ⟨5, 7,  by decide, by decide, by norm_num⟩
theorem goldbach_14  : GoldbachAt 14  := ⟨3, 11, by decide, by decide, by norm_num⟩
theorem goldbach_16  : GoldbachAt 16  := ⟨3, 13, by decide, by decide, by norm_num⟩
theorem goldbach_18  : GoldbachAt 18  := ⟨5, 13, by decide, by decide, by norm_num⟩
theorem goldbach_20  : GoldbachAt 20  := ⟨3, 17, by decide, by decide, by norm_num⟩
theorem goldbach_28  : GoldbachAt 28  := ⟨5, 23, by decide, by decide, by norm_num⟩
theorem goldbach_100 : GoldbachAt 100 := ⟨3, 97, by decide, by decide, by norm_num⟩

-- VerifiedUpTo 20 ──────────────────────────────────────────────────
-- interval_cases génère tous les cas n ∈ [4,20], y compris les impairs.
-- Les impairs sont éliminés par : hEven donne ⟨k, rfl⟩ avec 2*k = n,
-- puis omega résout les contradictions n impair.
theorem verifiedUpTo_20 : VerifiedUpTo 20 := by
  intro n hn4 hn20 hn_even
  obtain ⟨k, rfl⟩ := hn_even  -- n = 2 * k
  have hk_lower : 2 ≤ k := by omega
  have hk_upper : k ≤ 10 := by omega
  interval_cases k <;> first
    | exact goldbach_4
    | exact goldbach_6
    | exact goldbach_8
    | exact goldbach_10
    | exact goldbach_12
    | exact goldbach_14
    | exact goldbach_16
    | exact goldbach_18
    | exact goldbach_20
    | omega

end Goldbach
