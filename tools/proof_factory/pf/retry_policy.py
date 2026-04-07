from __future__ import annotations
from dataclasses import dataclass
from pf.models import BuildResult, Goal, ProofTemplate

@dataclass
class RetryDecision:
    preferred_tags: list[str]; deprioritized_tags: list[str]; note: str

def classify_build_failure(r):
    if r.ok: return "success"
    if not r.errors: return "unknown"
    kinds = [e.kind for e in r.errors]
    for k,v in [("unknown_identifier","unknown_identifier"),("type_mismatch","type_mismatch"),
                ("unsolved_goals","unsolved_goals"),("linarith_failed","linarith_failed"),
                ("norm_num_failed","norm_num_failed"),("simp_no_progress","simp_no_progress")]:
        if k in kinds: return v
    return "unknown"

def decide_retry(goal, result):
    if result is None: return RetryDecision(["specialized","certificate","definitional"],[],  "initial")
    f = classify_build_failure(result)
    MAP = {"unknown_identifier": (["specialized","stub"],["simp","calc"]),
           "type_mismatch": (["definitional","specialized","rfl"],["linarith"]),
           "unsolved_goals": (["calc","constructor","specialized"],["rfl"]),
           "linarith_failed": (["nlinarith","calc","certificate"],["linarith"]),
           "norm_num_failed": (["certificate","calc"],["norm_num"]),
           "simp_no_progress": (["specialized","calc","certificate"],["simp"])}
    pref, depri = MAP.get(f, (["specialized","certificate","stub"],[]))
    return RetryDecision(pref, depri, f)

def reorder_templates(templates, decision):
    def score(t):
        tags = set(t.tags)
        p = sum(1 for tag in decision.preferred_tags if tag in tags)
        d = sum(1 for tag in decision.deprioritized_tags if tag in tags)
        return (-p, d, t.name)
    return sorted(templates, key=score)
