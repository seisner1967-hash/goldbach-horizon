import sys, argparse; sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from pf.config import load_config
from pf.prioritizer import prioritize_goals
from pf.attempt_engine import AttemptEngine, load_goals
if __name__ == "__main__":
    p = argparse.ArgumentParser(); p.add_argument("--category",default=None); p.add_argument("--limit",type=int,default=5)
    args = p.parse_args(); cfg = load_config(); goals = load_goals(cfg.goals_path)
    sel = prioritize_goals(goals, category=args.category, remaining_only=True)
    engine = AttemptEngine(cfg); count = 0
    for g in sel:
        if count >= args.limit: break
        print(f"\n=== [{count+1}/{args.limit}] {g.theorem_name} ===")
        ok, strat, status = engine.try_goal_by_name(g.theorem_name)
        print(f"  -> {status}"); count += 1
