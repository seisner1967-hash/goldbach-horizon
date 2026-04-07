import sys, json, argparse; sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from pf.config import load_config
from pf.models import Goal
from pf.certificates import write_goal_certificate_bundle, append_certificate_log
if __name__ == "__main__":
    p = argparse.ArgumentParser(); p.add_argument("--category",default="numeric"); p.add_argument("--limit",type=int,default=50)
    args = p.parse_args(); cfg = load_config()
    goals = [Goal.from_dict(x) for x in json.loads(cfg.goals_path.read_text(encoding="utf-8"))] if cfg.goals_path.exists() else []
    sel = [g for g in goals if g.category == args.category and g.status != "closed"][:args.limit]
    n = 0
    for g in sel:
        b = write_goal_certificate_bundle(cfg, g)
        append_certificate_log(cfg, g, b is not None, b)
        if b: n += 1; print(f"  cert: {g.theorem_name}")
    print(f"[certificates] produced {n} bundles")
