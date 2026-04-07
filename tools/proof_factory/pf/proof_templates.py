from __future__ import annotations
from pf.models import Goal, ProofTemplate

def _t(n,p,tags): return ProofTemplate(name=n, proof_text=p, tags=tags)

BASIC = [
    lambda: _t("rfl",":= by\n  rfl",["definitional","rfl"]),
    lambda: _t("simp",":= by\n  simp",["simp"]),
    lambda: _t("simpa",":= by\n  simpa",["simpa","simp"]),
    lambda: _t("simp_all",":= by\n  simp_all",["simp"]),
    lambda: _t("aesop",":= by\n  aesop",["automation"]),
    lambda: _t("positivity",":= by\n  positivity",["numeric","nonneg"]),
    lambda: _t("norm_num",":= by\n  norm_num",["numeric","norm_num"]),
    lambda: _t("linarith",":= by\n  linarith",["linear","linarith"]),
    lambda: _t("nlinarith",":= by\n  nlinarith",["nonlinear","nlinarith"]),
    lambda: _t("omega",":= by\n  omega",["arith","omega"]),
    lambda: _t("sum_nonneg",":= by\n  classical\n  refine Finset.sum_nonneg ?_\n  intro x hx\n  positivity",["nonneg","finset","sum"]),
    lambda: _t("prod_nonneg",":= by\n  classical\n  refine Finset.prod_nonneg ?_\n  intro x hx\n  positivity",["nonneg","finset","prod"]),
    lambda: _t("card_nonneg",":= by\n  exact Nat.cast_nonneg _",["cardinality","nonneg"]),
    lambda: _t("constructor",":= by\n  constructor <;> aesop",["constructor","structured"]),
]

def _stub(g): return _t("stub",f":= by\n  -- TODO: {g.theorem_name}\n  sorry",["stub"])

def generate_templates_for_goal(goal):
    n = goal.theorem_name.lower(); out = []
    if "split" in n: return [BASIC[0](), BASIC[2](), BASIC[1]()]
    if "nonneg" in n: return [BASIC[5](), BASIC[10](), BASIC[11](), BASIC[12](), BASIC[2](), BASIC[1](), BASIC[4]()]
    if any(k in n for k in ["bound","3_5","_le","le_","_lt","lt_"]): return [BASIC[6](), BASIC[7](), BASIC[8](), BASIC[2](), BASIC[1]()]
    if goal.category == "bridge": return [BASIC[0](), BASIC[2](), BASIC[1](), BASIC[3](), BASIC[4](), BASIC[13]()]
    if goal.category == "numeric": return [BASIC[6](), BASIC[5](), BASIC[7](), BASIC[8](), BASIC[9](), BASIC[2]()]
    if goal.category == "analytic_deep": return [_stub(goal)]
    return [BASIC[2](), BASIC[1](), BASIC[3](), BASIC[4](), BASIC[13](), _stub(goal)]
