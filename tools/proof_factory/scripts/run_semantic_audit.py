import sys, json; sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from pf.config import load_config
from pf.models import Goal
from pf.semantic_audit import run_semantic_audit, write_semantic_audit
if __name__ == "__main__":
    cfg = load_config()
    goals = [Goal.from_dict(x) for x in json.loads(cfg.goals_path.read_text(encoding="utf-8"))] if cfg.goals_path.exists() else []
    rows = run_semantic_audit(cfg, goals)
    out = write_semantic_audit(cfg, rows)
    print(f"[audit] {len(rows)} rows -> {out}")
