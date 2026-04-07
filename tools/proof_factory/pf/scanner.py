from __future__ import annotations
import hashlib, re
from pathlib import Path
from pf.config import FactoryConfig
from pf.models import Goal

DECL_RE = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z0-9_'.]+)\b")

def classify_goal(name, sig):
    low = name.lower()
    if any(k in low for k in ["split","transfer","from_","canonical","variance"]): return ("bridge",2)
    if any(k in low for k in ["nonneg","bound","le_","_le","lt_","_lt","3_5"]): return ("numeric",2)
    if any(k in low for k in ["gallagher","hildebrand","bombieri","brun","mertens"]): return ("analytic_deep",10)
    if any(k in sig.lower() for k in ["≤","<","≥",">"]): return ("numeric",4)
    return ("structural",5)

def _gid(f,n,l): return hashlib.sha1(f"{f}:{n}:{l}".encode()).hexdigest()[:16]

def scan_file(fp, repo):
    rel = str(fp.relative_to(repo)).replace("\\","/")
    lines = fp.read_text(encoding="utf-8").splitlines()
    goals = []
    i = 0
    while i < len(lines):
        m = DECL_RE.match(lines[i])
        if m:
            dk, tn = m.group(1), m.group(2)
            sl = [lines[i]]; j = i; found = "sorry" in lines[i]
            while not found and j+1 < len(lines):
                j += 1; sl.append(lines[j])
                if "sorry" in lines[j]: found = True; break
                if re.match(r"^\s*(theorem|lemma|def|noncomputable|axiom)\s+", lines[j]): break
            if found:
                sig = "\n".join(sl)
                cat, diff = classify_goal(tn, sig)
                goals.append(Goal(id=_gid(rel,tn,i+1), file=rel, theorem_name=tn,
                    declaration_kind=dk, signature=sig, line_start=i+1, line_end=j+1,
                    body_start=i+1, body_end=j+1, category=cat, difficulty=diff,
                    context_before=lines[max(0,i-10):i], context_after=lines[j+1:min(len(lines),j+11)]))
                i = j+1; continue
        i += 1
    return goals

def scan_repo_for_goals(cfg):
    goals = []
    for fp in cfg.lean_root.rglob("*.lean"):
        goals.extend(scan_file(fp, cfg.repo_root))
    goals.sort(key=lambda g: (g.file, g.line_start))
    return goals
