from __future__ import annotations
import re
from dataclasses import dataclass
from pathlib import Path

DECL_START = re.compile(r"^\s*(theorem|lemma|def|noncomputable def|axiom)\s+([A-Za-z0-9_'.]+)\b")

@dataclass
class LeanDecl:
    kind: str; name: str; start_line: int; end_line: int; text: str

def iter_declarations(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    starts = [(i, m) for i, l in enumerate(lines) if (m := DECL_START.match(l))]
    decls = []
    for idx, (s, m) in enumerate(starts):
        e = starts[idx+1][0]-1 if idx+1 < len(starts) else len(lines)-1
        decls.append(LeanDecl(kind=m.group(1), name=m.group(2), start_line=s+1, end_line=e+1, text="\n".join(lines[s:e+1])))
    return decls

def find_declaration_by_name(path, name):
    for d in iter_declarations(path):
        if d.name == name: return d
    return None

def theorem_contains_sorry(path, name):
    d = find_declaration_by_name(path, name)
    return d is not None and "sorry" in d.text
