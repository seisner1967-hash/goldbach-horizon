from __future__ import annotations
import subprocess
from pathlib import Path

def _git(repo, args):
    p = subprocess.run(["git",*args], cwd=str(repo), capture_output=True, text=True, encoding="utf-8", errors="replace")
    return p.returncode, p.stdout, p.stderr

def git_is_repo(r): c,o,e = _git(r,["rev-parse","--is-inside-work-tree"]); return c==0
def git_is_dirty(r): c,o,e = _git(r,["status","--porcelain"]); return bool(o.strip())
def git_commit_all(r, msg): _git(r,["add","-A"]); c,o,e = _git(r,["commit","-m",msg]); return c==0
def git_create_tag(r, tag, msg=None):
    args = ["tag","-a",tag,"-m",msg] if msg else ["tag",tag]
    c,o,e = _git(r, args); return c==0
