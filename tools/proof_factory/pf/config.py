from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Any
import yaml

@dataclass
class FactoryConfig:
    root: Path; repo_root: Path; lean_root: Path; state_dir: Path
    goals_path: Path; attempts_path: Path; builds_path: Path
    lean_cmd: str; lake_cmd: str; mode: str
    max_attempts_per_goal: int; backup_before_patch: bool

def _resolve(base, value):
    p = Path(value)
    return p if p.is_absolute() else (base / p).resolve()

def load_config(config_path=None):
    root = Path(__file__).resolve().parents[1]
    cfg_file = Path(config_path) if config_path else root / "proof_factory.yaml"
    if not cfg_file.exists():
        raise FileNotFoundError(f"Missing config: {cfg_file}")
    raw = yaml.safe_load(cfg_file.read_text(encoding="utf-8")) or {}
    repo_root = _resolve(root, raw.get("repo_root", "../.."))
    lean_root = _resolve(repo_root, raw.get("lean_root", "MT/lean/HorizonMT"))
    state_dir = _resolve(root, raw.get("state_dir", "state"))
    state_dir.mkdir(parents=True, exist_ok=True)
    return FactoryConfig(
        root=root, repo_root=repo_root, lean_root=lean_root, state_dir=state_dir,
        goals_path=state_dir/"goals.json", attempts_path=state_dir/"attempts.jsonl",
        builds_path=state_dir/"builds.jsonl", lean_cmd=raw.get("lean_cmd","lean"),
        lake_cmd=raw.get("lake_cmd","lake"), mode=raw.get("mode","standalone"),
        max_attempts_per_goal=int(raw.get("max_attempts_per_goal",12)),
        backup_before_patch=bool(raw.get("backup_before_patch",True)))
