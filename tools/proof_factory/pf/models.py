from __future__ import annotations
from dataclasses import dataclass, asdict, field
from typing import Any

@dataclass
class Goal:
    id: str; file: str; theorem_name: str; declaration_kind: str
    signature: str; line_start: int; line_end: int
    body_start: int; body_end: int; status: str = "open"
    category: str = "unknown"; difficulty: int = 5
    context_before: list[str] = field(default_factory=list)
    context_after: list[str] = field(default_factory=list)
    last_strategy: str | None = None
    def to_dict(self): return asdict(self)
    @classmethod
    def from_dict(cls, d): return cls(**d)
    def priority_score(self):
        w = {"numeric":1,"bridge":2,"structural":3,"analytic_deep":10,"unknown":50}.get(self.category,50)
        return (w, self.difficulty)

@dataclass
class BuildError:
    file: str|None; line: int|None; col: int|None; message: str; kind: str="unknown"
    def to_dict(self): return asdict(self)

@dataclass
class BuildResult:
    ok: bool; cmd: list[str]; returncode: int; stdout: str; stderr: str
    errors: list[BuildError] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    def short_summary(self):
        if self.ok: return "build ok"
        if self.errors: return f"{self.errors[0].kind}: {self.errors[0].message[:200]}"
        return (self.stderr or self.stdout)[:200]
    def to_dict(self):
        return {"ok":self.ok,"cmd":self.cmd,"returncode":self.returncode,
                "stdout":self.stdout,"stderr":self.stderr,
                "errors":[e.to_dict() for e in self.errors],"warnings":self.warnings}

@dataclass
class ProofTemplate:
    name: str; proof_text: str; tags: list[str] = field(default_factory=list)
