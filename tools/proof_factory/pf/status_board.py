from __future__ import annotations
import json
from collections import defaultdict
from pathlib import Path
from pf.models import Goal

def load_jsonl(path):
    if not path.exists(): return []
    return [json.loads(l) for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]

def render_status_board(goals, attempts, builds, semantic_rows=None):
    gs = defaultdict(int); cs = defaultdict(int)
    for g in goals: gs[g.status] += 1; cs[g.category] += 1
    lines = ["="*72,"PROOF FACTORY STATUS BOARD","="*72,"","GOALS BY STATUS"]
    for k,v in sorted(gs.items()): lines.append(f"  {k:<12} {v:>5}")
    lines += ["","GOALS BY CATEGORY"]
    for k,v in sorted(cs.items()): lines.append(f"  {k:<12} {v:>5}")
    lines += ["",f"ATTEMPTS: {len(attempts)}",f"BUILDS: {len(builds)}","","REMAINING"]
    for g in sorted([g for g in goals if g.status != "closed"], key=lambda g:(g.category,g.difficulty)):
        lines.append(f"  - {g.theorem_name} [{g.status}] {g.category}/d{g.difficulty}")
    lines += ["","="*72]
    return "\n".join(lines)
