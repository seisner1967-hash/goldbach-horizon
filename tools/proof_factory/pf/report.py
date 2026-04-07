from __future__ import annotations
import json
from collections import defaultdict
from pathlib import Path
from pf.config import FactoryConfig
from pf.models import Goal

def append_attempt_log(cfg, *, goal_id, theorem_name, strategy, ok, summary):
    cfg.attempts_path.parent.mkdir(parents=True, exist_ok=True)
    with cfg.attempts_path.open("a", encoding="utf-8") as f:
        f.write(json.dumps({"goal_id":goal_id,"theorem_name":theorem_name,"strategy":strategy,"ok":ok,"summary":summary}, ensure_ascii=False)+"\n")

def render_markdown_report(cfg, goals, semantic_rows=None):
    by_s = defaultdict(int); by_c = defaultdict(int)
    for g in goals: by_s[g.status] += 1; by_c[g.category] += 1
    lines = ["# Proof Factory Report","",f"Total goals: **{len(goals)}**","","## By status",""]
    for k,v in sorted(by_s.items()): lines.append(f"- {k}: {v}")
    lines += ["","## By category",""]
    for k,v in sorted(by_c.items()): lines.append(f"- {k}: {v}")
    lines += ["","## Remaining",""]
    for g in goals:
        if g.status != "closed": lines.append(f"- `{g.theorem_name}` [{g.status}] {g.category}/d{g.difficulty}")
    return "\n".join(lines)+"\n"

def write_markdown_report(cfg, content):
    out = cfg.state_dir / "report.md"; out.write_text(content, encoding="utf-8"); return out
