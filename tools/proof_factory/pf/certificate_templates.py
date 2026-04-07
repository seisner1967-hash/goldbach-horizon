from __future__ import annotations
import json
from pathlib import Path
from pf.config import FactoryConfig
from pf.models import Goal, ProofTemplate

def load_certificate_json(cfg, goal):
    p = cfg.state_dir / "certificates" / f"{goal.theorem_name}.json"
    if not p.exists(): return None
    try: return json.loads(p.read_text(encoding="utf-8"))
    except: return None

def make_certificate_templates(cfg, goal):
    cert = load_certificate_json(cfg, goal)
    if cert is None: return []
    if cert.get("kind") == "log_via_exp":
        return [ProofTemplate("cert_log_exp",":= by\n  -- Certificate: exp 1 <= 3.5\n  sorry",["certificate","log","exp"])]
    return [ProofTemplate("cert_stub",f":= by\n  -- Certificate: {cert.get('statement','')}\n  sorry",["certificate","stub"])]
