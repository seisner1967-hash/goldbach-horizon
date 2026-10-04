"""Metadata-only freeze. Does not invoke Lean or perform mathematical evaluation."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
from datetime import datetime, timezone

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
OWN = BASE / "round22" / "role4"
PACKAGES = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
NAMES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0")


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_new(name, value):
    with (OWN / name).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def imports(path):
    text = path.read_text(encoding="utf-8-sig")
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return [module for match in re.finditer(r"^import\s+([^\n]+)", text, re.MULTILINE)
            for module in match.group(1).split("--", 1)[0].split()]


def resolve(module):
    rel = Path(*module.split("."))
    for name in NAMES:
        root = PACKAGES / name
        source = root / rel.with_suffix(".lean")
        olean = root / ".lake" / "build" / "lib" / rel.with_suffix(".olean")
        if source.exists() or olean.exists():
            return source, olean
    for root in (LEAN_ROOT / "src" / "lean", LEAN_ROOT / "src" / "lean" / "lake"):
        source = root / rel.with_suffix(".lean")
        olean = LEAN_ROOT / "lib" / "lean" / rel.with_suffix(".olean")
        if source.exists() or olean.exists():
            return source, olean
    return None, None


def main():
    stamp = datetime.now(timezone.utc).isoformat()
    source = OWN / "GammaPrerequisites22.lean"
    queue = imports(source)
    closure = []
    seen = set()
    unresolved = []
    inputs = {}
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        seen.add(module)
        src, obj = resolve(module)
        if src is None or not src.exists() or not obj.exists():
            unresolved.append({"module": module, "source": str(src), "olean": str(obj)})
            continue
        item = {"module": module, "source": str(src), "source_sha256": sha(src),
                "olean": str(obj), "olean_sha256": sha(obj), "scope": "import metadata only"}
        closure.append(item)
        inputs[str(src)] = item["source_sha256"]
        inputs[str(obj)] = item["olean_sha256"]
        queue.extend(imports(src))
    closure.sort(key=lambda item: item["module"])
    write_new("gamma_import_bindings1.json", {"schema": "ROUND22_ROLE4_GAMMA_IMPORT_BINDINGS_1",
        "time_utc": stamp, "module_count": len(closure), "unresolved": unresolved,
        "entries": closure, "numeric_invocations": 0, "compiler_invocations": 0})
    m = PACKAGES / "mathlib" / "Mathlib"
    read_list = [
        (BASE / "round22" / "USER_DIRECTIVE.md", "FULL", "52af9f"),
        (BASE / "round22" / "PROBE_BLOCK.md", "FULL", "30d6af"),
        (BASE / "round22" / "agent1_continuous.md", "FULL", "1243fc"),
        (BASE / "round22" / "role1" / "real_trace_annex.md", "FULL", "576b61"),
        (BASE / "round22" / "role1" / "lean_contract.md", "FULL", "32aeb0"),
        (BASE / "round22" / "role1" / "numeric_contract.md", "FULL", "d04b4d"),
        (BASE / ".arbor" / "sessions" / "parity" / "experiments" / "15.2" / "executor_prompt.md", "FULL", "9e37ea"),
        (Path(r"C:\Users\Utilisateur\.codex\skills\arbor-agent-executor\SKILL.md"), "FULL", "initial executor read"),
        (Path(r"C:\Users\Utilisateur\.codex\skills\arbor-agent-merge-eval\SKILL.md"), "FULL", "200c8b"),
        (m / "Analysis" / "SpecialFunctions" / "Gamma" / "Basic.lean", "FULL", "f5b876"),
        (m / "Analysis" / "SpecialFunctions" / "Gamma" / "BohrMollerup.lean", "FULL", "871d5f"),
        (m / "Analysis" / "SpecialFunctions" / "Log" / "Monotone.lean", "FULL", "5fb0ce"),
        (m / "Analysis" / "SpecialFunctions" / "ImproperIntegrals.lean", "FULL", "5d1d12"),
        (m / "Analysis" / "Calculus" / "ParametricIntegral.lean", "TARGETED lines45-73 and248-310", "75c75c, cb51c3"),
        (m / "Analysis" / "Analytic" / "IsolatedZeros.lean", "TARGETED lines250-277", "9ca58f"),
        (m / "Analysis" / "Complex" / "CauchyIntegral.lean", "TARGETED lines561-587", "0146b3"),
        (m / "MeasureTheory" / "Integral" / "IntegralEqImproper.lean", "TARGETED lines1141-1179 and declarations", "b698ee, f1f332"),
        (m / "Analysis" / "SpecialFunctions" / "Pow" / "Deriv.lean", "TARGETED lines27-61,99-165,183-196", "bbfeb6, 1ce0ef, 708aa8"),
        (m / "Analysis" / "SpecialFunctions" / "Pow" / "Real.lean", "TARGETED lines175-191,281-301 and declarations", "bbfeb6, 0e9906, 77168c"),
        (m / "Analysis" / "Complex" / "Basic.lean", "TARGETED lines241-266 and declarations", "708aa8, c80986"),
        (m / "Analysis" / "RCLike" / "Basic.lean", "DECLARATIONS ONLY norm_conj518", "c3967e"),
        (m / "Analysis" / "SpecialFunctions" / "ExpDeriv.lean", "DECLARATIONS ONLY complex/real derivative and analytic APIs", "cb51c3"),
        (m / "Analysis" / "SpecialFunctions" / "Exp.lean", "DECLARATIONS ONLY Continuous.cexp108-116", "1cbdb5"),
        (m / "Analysis" / "SpecialFunctions" / "Pow" / "Complex.lean", "DECLARATIONS ONLY cpow,neg,inv", "f4e4d6"),
        (m / "Analysis" / "SpecialFunctions" / "Trigonometric" / "Basic.lean", "DECLARATIONS ONLY cos positivity and quarter-angle", "2949f7"),
        (m / "Analysis" / "Convex" / "Basic.lean", "TARGETED lines229-259 and declarations", "0e9906"),
        (m / "Analysis" / "Convex" / "Topology.lean", "DECLARATIONS ONLY convex preconnected", "bbfeb6"),
        (m / "Analysis" / "SpecificLimits" / "Basic.lean", "TARGETED lines19-63", "708aa8"),
        (m / "Topology" / "Basic.lean", "TARGETED lines1281-1296", "708aa8"),
        (m / "Data" / "Complex" / "Basic.lean", "DECLARATIONS ONLY ofReal_eq_one164", "1cbdb5"),
        (OWN / "GammaPrerequisites22.lean", "FULL final draft", "5db356"),
        (OWN / "run_gamma_once22.py", "FULL final draft", "084589"),
    ]
    reads = [{"path": str(path), "sha256": sha(path), "scope": scope, "output_chunk": chunk}
             for path, scope, chunk in read_list]
    write_new("gamma_read_receipts1.json", {"schema": "ROUND22_ROLE4_GAMMA_READ_RECEIPTS_1",
        "time_utc": stamp, "local_reads": reads,
        "web_reads": [{"url": "https://dlmf.nist.gov/5.9.E1", "scope": "TARGETED equation5.9.1 and domain lines39-51", "response": "turn156view0"}],
        "tool_errors_metadata_only": ["numeric_contract.json nonexistent; rg found actual numeric_contract.md",
            "ParametricIntegral initially searched under MeasureTheory; actual file under Analysis/Calculus",
            "Bochner initially searched as directory; actual Bochner.lean"],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0})
    for path, _, _ in read_list:
        inputs[str(path)] = sha(path)
    for name in ("gamma_import_bindings1.json", "gamma_read_receipts1.json", "gamma_preparation1.md", "prepare_gamma_metadata1.py"):
        path = OWN / name
        inputs[str(path)] = sha(path)
    for path in (BASE / "round22" / "previous_artifacts_sha256.json", LEAN_ROOT / "bin" / "lean.exe",
                 Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")):
        inputs[str(path)] = sha(path)
    source_text = source.read_text(encoding="utf-8")
    declarations = re.findall(r"^(?:theorem|def)\s+(\w+)", source_text, re.MULTILINE)
    prints = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", source_text, re.MULTILINE)
    manifest = {"schema": "ROUND22_ROLE4_GAMMA_PREPARED_MANIFEST_1", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED" if not unresolved and declarations == prints else "PREPARATION_DEPENDENCY_OPEN",
        "node": "15.2", "source_sha256": sha(source), "launcher_sha256": sha(OWN / "run_gamma_once22.py"),
        "import_module_count": len(closure), "unresolved_modules": unresolved,
        "declarations": declarations, "qualified_prints_exact": declarations == prints,
        "theorem_count": len(re.findall(r"^theorem\s+", source_text, re.MULTILINE)),
        "definition_count": len(re.findall(r"^def\s+", source_text, re.MULTILINE)),
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(inputs.items())],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0,
        "epstein_G0_not_authorizing": True, "own_Gamma_bank_required": True,
        "weil_certified": False, "zero_count_certified": False, "D_N_paid": False, "win": False}
    write_new("gamma_prepared_manifest1.json", manifest)
    print(json.dumps({"status": manifest["status"], "modules": len(closure), "unresolved": unresolved,
        "source_sha256": manifest["source_sha256"], "manifest_sha256": sha(OWN / "gamma_prepared_manifest1.json"),
        "launcher_sha256": manifest["launcher_sha256"], "compiler_invocations": 0,
        "mathematical_numeric_invocations": 0}, ensure_ascii=False))


if __name__ == "__main__":
    main()
