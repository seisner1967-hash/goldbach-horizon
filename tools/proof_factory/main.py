from __future__ import annotations
import json, sys
from pathlib import Path
from pf.config import load_config
from pf.models import Goal
from pf.scanner import scan_repo_for_goals
from pf.attempt_engine import AttemptEngine, load_goals, save_goals

def cmd_inventory():
    cfg = load_config(); goals = scan_repo_for_goals(cfg)
    save_goals(cfg.goals_path, goals)
    print(f"[inventory] {len(goals)} goals -> {cfg.goals_path}")

def cmd_attempt(name):
    cfg = load_config(); engine = AttemptEngine(cfg)
    ok, strat, status = engine.try_goal_by_name(name)
    print(f"[attempt] {name}: ok={ok} strategy={strat} status={status}")

def cmd_auto(limit=5):
    cfg = load_config(); goals = load_goals(cfg.goals_path)
    from pf.prioritizer import prioritize_goals
    sel = prioritize_goals(goals, remaining_only=True)
    engine = AttemptEngine(cfg); count = 0
    for g in sel:
        if count >= limit: break
        print(f"\n=== [{count+1}/{limit}] {g.theorem_name} ===")
        ok, strat, status = engine.try_goal_by_name(g.theorem_name)
        print(f"  -> ok={ok} strategy={strat} status={status}")
        count += 1

if __name__ == "__main__":
    if len(sys.argv) < 2: print("Usage: inventory | attempt <name> | auto [limit]"); sys.exit(1)
    cmd = sys.argv[1]
    if cmd == "inventory": cmd_inventory()
    elif cmd == "attempt": cmd_attempt(sys.argv[2])
    elif cmd == "auto": cmd_auto(int(sys.argv[2]) if len(sys.argv)>2 else 5)
