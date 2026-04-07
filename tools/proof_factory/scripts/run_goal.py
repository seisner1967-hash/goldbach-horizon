import sys; sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from pf.config import load_config
from pf.attempt_engine import AttemptEngine
if __name__ == "__main__":
    name = sys.argv[1] if len(sys.argv) > 1 else None
    if not name: print("Usage: run_goal.py <theorem_name>"); sys.exit(1)
    cfg = load_config(); engine = AttemptEngine(cfg)
    ok, strat, status = engine.try_goal_by_name(name)
    print(f"{'SUCCESS' if ok else 'FAILED'}: {name} via {strat} -> {status}")
    if not ok: sys.exit(1)
