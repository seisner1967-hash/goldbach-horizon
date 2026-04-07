from __future__ import annotations
from pathlib import Path
from pf.config import FactoryConfig
from pf.models import Goal

class LeanPatcher:
    def __init__(self, cfg): self.cfg = cfg
    def _abs(self, rel): return (self.cfg.repo_root / rel).resolve()
    def _bak(self, fp): return fp.with_suffix(fp.suffix + ".bak")
    def apply_goal_proof(self, goal, proof_text):
        fp = self._abs(goal.file); src = fp.read_text(encoding="utf-8"); lines = src.splitlines()
        if self.cfg.backup_before_patch: self._bak(fp).write_text(src, encoding="utf-8")
        s, e = goal.line_start-1, goal.line_end-1
        block = "\n".join(lines[s:e+1])
        if ":= by sorry" in block: new = block.replace(":= by sorry", proof_text)
        elif "by sorry" in block: new = block.replace("by sorry", proof_text.removeprefix(":= ").strip())
        elif ":= by\n" in block and "sorry" in block: new = block.replace("sorry", proof_text.replace(":= by\n","").strip())
        else: raise ValueError(f"Cannot patch {goal.theorem_name}")
        fp.write_text("\n".join(lines[:s] + new.splitlines() + lines[e+1:]) + "\n", encoding="utf-8")
        return fp
    def restore_backup(self, fp):
        bak = self._bak(fp)
        if bak.exists(): fp.write_text(bak.read_text(encoding="utf-8"), encoding="utf-8")
