from __future__ import annotations
from pf.models import Goal, ProofTemplate

def specialize_goal(goal):
    n = goal.theorem_name.lower(); out = []
    if "split" in n:
        out.append(ProofTemplate("spec_split_rfl",":= by\n  rfl",["specialized","split","rfl"]))
    if "nonneg" in n:
        out.append(ProofTemplate("spec_nonneg",":= by\n  positivity",["specialized","nonneg"]))
    if "dickmanrho_bound_3_5" in n or "3_5" in n:
        out.append(ProofTemplate("spec_dickman",":= by\n  unfold dickmanRho\n  have : ¬((3.5:ℝ) ≤ 1) := by norm_num\n  simp [this]",["specialized","dickman"]))
    if any(k in n for k in ["gallagher","hildebrand","bombieri","brun","mertens"]):
        out.append(ProofTemplate("spec_deep_stub",f":= by\n  -- Deep: {goal.theorem_name}\n  sorry",["specialized","stub"]))
    return out
