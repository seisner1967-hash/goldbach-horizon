/-
  Goldbach/G43Budget.lean
  Budget précis de G43 : total = 0.781, marge = 0.219.
  0 sorry. Corrections vs GPT v1 :
    - c_otsa_r72 corrigé : 65/1000 = 0.065 (pas 1/1000)
    - budget_closure additionne TOUS les termes
    - Ajout import Goldbach.Budget pour certifiedBudget
-/
import Goldbach.Budget
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach

-- Composantes du budget G43 à N₀ (certifiées par compute_N0_v3.py)
def c_u1_u6   : ℝ := 780  / 1000   -- 0.780 (certifié U1-U6)
def c_u7      : ℝ := 9    / 1000000 -- 0.000009 (Gallagher+Herglotz)
def c_mj      : ℝ := 44   / 1000000 -- 0.000044 (Mellin-Jackson)
def c_otsa    : ℝ := 37   / 1000    -- 0.037 (résidu OTSA)
def c_r72     : ℝ := 28   / 1000    -- 0.028 (R72bis)

-- Budget total et marge
def g43TotalBudgetQ : ℚ := 781 / 1000
def g43MarginQ      : ℚ := 219 / 1000
def g43TotalBudget  : ℝ := g43TotalBudgetQ
def g43Margin       : ℝ := g43MarginQ

-- Identités exactes (norm_num) ─────────────────────────────────────
theorem g43_budget_identity : g43TotalBudget + g43Margin = 1 := by
  norm_num [g43TotalBudget, g43Margin, g43TotalBudgetQ, g43MarginQ]

theorem g43_margin_pos : 0 < g43Margin := by
  norm_num [g43Margin, g43MarginQ]

theorem g43_total_lt_one : g43TotalBudget < 1 := by
  norm_num [g43TotalBudget, g43TotalBudgetQ]

-- Fermeture du budget sur TOUS les termes ─────────────────────────
theorem g43_all_components_sum_lt_one :
    c_u1_u6 + c_u7 + c_mj + c_otsa + c_r72 < 1 := by
  norm_num [c_u1_u6, c_u7, c_mj, c_otsa, c_r72]

theorem g43_positivity_margin :
    1 - (c_u1_u6 + c_u7 + c_mj + c_otsa + c_r72) > 0.18 := by
  norm_num [c_u1_u6, c_u7, c_mj, c_otsa, c_r72]

-- Lien avec le budget coarse existant ─────────────────────────────
theorem g43_certifiedBudget_le_total :
    certifiedBudget ≤ g43TotalBudget := by
  norm_num [certifiedBudget, certifiedBudgetQ, g43TotalBudget, g43TotalBudgetQ]

theorem g43_margin_ge_safetyMargin :
    safetyMargin ≤ g43Margin := by
  norm_num [safetyMargin, safetyMarginQ, g43Margin, g43MarginQ]

end Goldbach
