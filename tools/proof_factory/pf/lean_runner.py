from __future__ import annotations
import json, subprocess
from pathlib import Path
from pf.config import FactoryConfig
from pf.models import BuildResult
from pf.build_parser import parse_lean_build_output

class LeanRunner:
    def __init__(self, cfg): self.cfg = cfg
    def run_on_file(self, fp):
        cmd = [self.cfg.lake_cmd, "build"] if self.cfg.mode == "lake" else [self.cfg.lean_cmd, str(fp)]
        proc = subprocess.run(cmd, cwd=str(self.cfg.repo_root), capture_output=True, text=True, encoding="utf-8", errors="replace")
        errors, warnings = parse_lean_build_output(proc.stdout, proc.stderr)
        return BuildResult(ok=proc.returncode==0, cmd=cmd, returncode=proc.returncode, stdout=proc.stdout, stderr=proc.stderr, errors=errors, warnings=warnings)
    def append_build_log(self, result, *, goal_id, strategy=None):
        self.cfg.builds_path.parent.mkdir(parents=True, exist_ok=True)
        with self.cfg.builds_path.open("a", encoding="utf-8") as f:
            f.write(json.dumps({"goal_id":goal_id,"strategy":strategy,"result":result.to_dict()}, ensure_ascii=False)+"\n")
