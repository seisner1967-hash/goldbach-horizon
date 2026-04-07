from __future__ import annotations
import json
from pathlib import Path
from pf.config import FactoryConfig
from pf.models import Goal, ProofTemplate
from pf.patcher import LeanPatcher
from pf.lean_runner import LeanRunner
from pf.proof_templates import generate_templates_for_goal
from pf.goal_specializers import specialize_goal
from pf.certificate_templates import make_certificate_templates
from pf.retry_policy import decide_retry, reorder_templates
from pf.report import append_attempt_log
from pf.parser_lean import find_declaration_by_name

def load_goals(p):
    if not p.exists(): return []
    return [Goal.from_dict(x) for x in json.loads(p.read_text(encoding="utf-8"))]

def save_goals(p, goals):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps([g.to_dict() for g in goals], ensure_ascii=False, indent=2), encoding="utf-8")

class AttemptEngine:
    def __init__(self, cfg):
        self.cfg = cfg; self.runner = LeanRunner(cfg); self.patcher = LeanPatcher(cfg)

    def collect_templates(self, goal):
        seen = set(); out = []
        for t in specialize_goal(goal) + make_certificate_templates(self.cfg, goal) + generate_templates_for_goal(goal):
            k = (t.name, t.proof_text)
            if k not in seen: seen.add(k); out.append(t)
        return out

    def try_goal(self, goal):
        fp = (self.cfg.repo_root / goal.file).resolve()
        templates = self.collect_templates(goal)
        if not templates: return False, "none", "failed"
        decision = decide_retry(goal, None)
        templates = reorder_templates(templates, decision)
        for t in templates:
            try: self.patcher.apply_goal_proof(goal, t.proof_text)
            except Exception as e:
                append_attempt_log(self.cfg, goal_id=goal.id, theorem_name=goal.theorem_name, strategy=t.name, ok=False, summary=str(e)); continue
            result = self.runner.run_on_file(fp)
            self.runner.append_build_log(result, goal_id=goal.id, strategy=t.name)
            if result.ok:
                d = find_declaration_by_name(fp, goal.theorem_name)
                has_sorry = d is not None and "sorry" in d.text
                status = "stubbed" if has_sorry else "closed"
                append_attempt_log(self.cfg, goal_id=goal.id, theorem_name=goal.theorem_name, strategy=t.name, ok=True, summary=status)
                return True, t.name, status
            self.patcher.restore_backup(fp)
            append_attempt_log(self.cfg, goal_id=goal.id, theorem_name=goal.theorem_name, strategy=t.name, ok=False, summary=result.short_summary())
            decision = decide_retry(goal, result)
        return False, "all_failed", "failed"

    def try_goal_by_name(self, name):
        goals = load_goals(self.cfg.goals_path)
        target = next((g for g in goals if g.theorem_name == name), None)
        if not target: return False, f"'{name}' not found", "failed"
        ok, strat, status = self.try_goal(target)
        target.status = status
        if ok: target.last_strategy = strat
        save_goals(self.cfg.goals_path, goals)
        return ok, strat, status
