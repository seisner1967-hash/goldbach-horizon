from __future__ import annotations
import re
from pf.models import BuildError

ERR_RE = re.compile(r"^(?P<file>.*?):(?P<line>\d+):(?P<col>\d+):\s*(error|warning):\s*(?P<msg>.*)$")

def classify_error(msg):
    low = msg.lower()
    for k,v in [("unknown identifier","unknown_identifier"),("type mismatch","type_mismatch"),
                ("unsolved goals","unsolved_goals"),("linarith","linarith_failed"),
                ("nlinarith","nlinarith_failed"),("norm_num","norm_num_failed"),
                ("simp made no progress","simp_no_progress"),("rewrite","rewrite_failed")]:
        if k in low: return v
    return "unknown"

def parse_lean_build_output(stdout, stderr):
    errors, warnings = [], []
    for line in (stdout+"\n"+stderr).splitlines():
        m = ERR_RE.match(line.strip())
        if m:
            msg = m.group("msg").strip()
            if "warning:" in line: warnings.append(line)
            else: errors.append(BuildError(file=m.group("file"),line=int(m.group("line")),col=int(m.group("col")),message=msg,kind=classify_error(msg)))
    return errors, warnings
