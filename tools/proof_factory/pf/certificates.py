from __future__ import annotations
import json
from pathlib import Path
from pf.config import FactoryConfig
from pf.models import Goal
from pf.numeric_workers import certify_log_of_exp_witness, certify_log_geq, write_certificate_json

def certificate_dir(cfg): d = cfg.state_dir/"certificates"; d.mkdir(parents=True, exist_ok=True); return d

def generate_goal_certificate(cfg, goal):
    n = goal.theorem_name.lower()
    if "dickmanrho_bound_3_5" in n or "3_5" in n: return certify_log_of_exp_witness(1.0, 3.5, 120)
    if "log" in n and "3_5" in n: return certify_log_geq(3.5, 1.0, 120)
    return None

def write_goal_certificate_bundle(cfg, goal):
    cert = generate_goal_certificate(cfg, goal)
    if cert is None: return None
    jp = certificate_dir(cfg) / f"{goal.theorem_name}.json"
    write_certificate_json(jp, cert)
    lp = certificate_dir(cfg) / f"{goal.theorem_name}.lean.txt"
    lp.write_text(f"-- Certificate for {goal.theorem_name}\n-- {cert.statement}\n-- Verified: {cert.verified}\n", encoding="utf-8")
    return jp, lp

def append_certificate_log(cfg, goal, success, bundle):
    lp = cfg.state_dir / "certificates.jsonl"
    with lp.open("a", encoding="utf-8") as f:
        f.write(json.dumps({"goal_id":goal.id,"theorem":goal.theorem_name,"success":success,
                            "bundle":[str(x) for x in bundle] if bundle else None}, ensure_ascii=False)+"\n")
