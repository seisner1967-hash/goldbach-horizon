from __future__ import annotations
import json, re
from pathlib import Path
from pf.config import FactoryConfig
from pf.models import Goal

ZERO_PATS = [re.compile(r":=\s*0\b"), re.compile(r":=\s*1\b")]

def audit_goal_block(goal, block):
    risk, reasons = "low", []
    for p in ZERO_PATS:
        if p.search(block) and goal.category not in ("numeric","bridge"):
            risk = "high"; reasons.append(f"zero-like: {p.pattern}")
    if "max 1" in block: risk = max(risk,"medium",key=lambda x:{"low":0,"medium":1,"high":2}[x]); reasons.append("suspicious guard: max 1")
    if goal.category == "analytic_deep" and "sorry" not in block: risk = "medium"; reasons.append("deep closed without sorry")
    if "sorry" in block: reasons.append("contains sorry")
    return {"goal_id":goal.id,"theorem_name":goal.theorem_name,"file":goal.file,"category":goal.category,"risk":risk,"reasons":reasons}

def run_semantic_audit(cfg, goals):
    rows = []
    for g in goals:
        fp = (cfg.repo_root / g.file).resolve()
        if not fp.exists(): rows.append({"goal_id":g.id,"theorem_name":g.theorem_name,"file":g.file,"risk":"high","reasons":["file missing"]}); continue
        lines = fp.read_text(encoding="utf-8").splitlines()
        s, e = max(0,g.line_start-1), min(len(lines),g.line_end)
        rows.append(audit_goal_block(g, "\n".join(lines[s:e])))
    return rows

def write_semantic_audit(cfg, rows):
    out = cfg.state_dir / "semantic_audit.jsonl"
    with out.open("w", encoding="utf-8") as f:
        for r in rows: f.write(json.dumps(r, ensure_ascii=False)+"\n")
    return out
