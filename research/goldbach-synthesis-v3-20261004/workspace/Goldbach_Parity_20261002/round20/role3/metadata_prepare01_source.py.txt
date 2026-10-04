"""Metadata preparation only: no compiler, mathematical test or old producer."""
import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
B = W.parents[1]
CACHE = B.parent / "q356-canonical-binding-replay" / ".lake" / "packages"
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PREFIX = "GoldbachRound20.SwitchedComposite."
MODULES = ["OddBonferroniArithmetic", "LeastFactorComposite", "SwitchedSelbergWeight",
           "PhysicalCompositeSubtraction", "CompositeAPConductor", "SwitchedIncidenceEstimator"]
HIST_DIRS = [B / "round19/judge/build", B / "round18/judge/build",
             B / "round17/judge/build", B / "round16/judge/build",
             B / "round13/role4/dependencies"]
PACKAGES = ["aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib",
            "plausible", "proofwidgets", "Qq"]
DECL = re.compile(r"^(def|theorem|lemma|structure)\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide|trustMe)\b")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def relative(path):
    return path.relative_to(B).as_posix()

def imports(text):
    return [item for line in re.findall(r"^import\s+(.+)$", text, re.M)
            for item in line.split()]

def metadata(normalize):
    written, edges, closure = [], {}, {}
    def visit(module):
        if module == "Mathlib" or module.startswith("Mathlib."):
            return
        if module in MODULES:
            return
        if module in closure:
            return
        candidates = [directory / (module.replace(".", "/") + ".lean") for directory in HIST_DIRS]
        present = [p for p in candidates if p.is_file()]
        if len(present) != 1:
            raise RuntimeError(f"historical module must resolve uniquely: {module}: {present}")
        source = present[0]
        olean = source.with_suffix(".olean")
        if not olean.is_file():
            raise RuntimeError(f"missing historical olean: {olean}")
        deps = imports(source.read_text(encoding="utf-8-sig"))
        closure[module] = {"source": relative(source), "source_sha256": sha(source),
                           "olean": relative(olean), "olean_sha256": sha(olean), "imports": deps}
        for dep in deps:
            visit(dep)

    for module in MODULES:
        path = W / f"{module}.lean"
        text = path.read_text(encoding="utf-8-sig")
        declarations = DECL.findall(text)
        if len({name for _, name in declarations}) != len(declarations):
            raise RuntimeError(f"duplicate declaration: {module}")
        if normalize:
            text = re.sub(r"^#print axioms[^\r\n]*(?:\r?\n)?", "", text, flags=re.M)
            tail = "end GoldbachRound20.SwitchedComposite"
            if text.count(tail) != 1:
                raise RuntimeError(f"namespace tail mismatch: {module}")
            code = text.split(tail)[0].rstrip()
            audit = "\n\n-- AXIOM_AUDIT_BEGIN\n" + "\n".join(
                f"#print axioms {PREFIX}{name}" for _, name in declarations)
            text = code + audit + "\n\n" + tail + "\n"
            path.write_text(text, encoding="utf-8", newline="\n")
        code = text.split("-- AXIOM_AUDIT_BEGIN")[0]
        if FORBIDDEN.search(code):
            raise RuntimeError(f"forbidden proof token: {module}")
        prints = re.findall(r"^#print axioms\s+(\S+)\s*$", text, re.M)
        expected = [PREFIX + name for _, name in declarations]
        if prints != expected:
            raise RuntimeError(f"missing or unordered declaration audit: {module}")
        deps = imports(text)
        edges[module] = deps
        for dep in deps:
            visit(dep)
        written.append({"module": module, "path": relative(path), "sha256": sha(path),
                        "bytes": path.stat().st_size, "definitions": sum(k == "def" for k, _ in declarations),
                        "theorems": sum(k in ("theorem", "lemma") for k, _ in declarations),
                        "axiom_prints": len(prints), "declarations": expected, "imports": deps})
    libs = [CACHE / package / ".lake/build/lib" for package in PACKAGES]
    if any(not path.is_dir() for path in libs):
        raise RuntimeError("missing cached library directory")
    mathlib = CACHE / "mathlib"
    bind = {}
    for detail in closure.values():
        bind[detail["source"]] = detail["source_sha256"]
        bind[detail["olean"]] = detail["olean_sha256"]
    return {
        "status": "SOURCE_AND_LAUNCHER_PREPARATION_ONLY_NO_LEAN_EXECUTION",
        "node_id": "13.12", "round": 20, "role": 3,
        "prepared_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "actual_lean_invocations": 0, "actual_numeric_producer_invocations": 0,
        "old_lean_rebuilds": 0, "old_PASS_replays": 0, "victory": False,
        "written_modules": written, "new_module_order": MODULES,
        "module_namespace": PREFIX[:-1], "historical_module_closure": closure,
        "historical_dependencies_sha256": bind,
        "historical_library_dirs": [str(p) for p in HIST_DIRS],
        "cache_library_dirs": [str(p) for p in libs],
        "lean_executable": str(LEAN), "lean_sha256": sha(LEAN),
        "python_executable": str(PYTHON), "python_sha256": sha(PYTHON),
        "mathlib_HEAD_path": str(mathlib / ".git/HEAD"),
        "mathlib_HEAD_sha256": sha(mathlib / ".git/HEAD"),
        "mathlib_root_source_sha256": sha(mathlib / "Mathlib.lean"),
        "mathlib_root_olean_sha256": sha(mathlib / ".lake/build/lib/Mathlib.olean"),
        "launcher_sha256": sha(W / "build_once.py"),
        "metadata_freezer_sha256": sha(Path(__file__)),
        "selection_sha256": sha(B / ".arbor/sessions/parity/.coordinator/messages/round20_role1_selection.json"),
        "executor_prompt_sha256": sha(B / ".arbor/sessions/parity/experiments/13.12/executor_prompt.md"),
        "paper_inputs_sha256": {
            "round20/PROBE_BLOCK.md": sha(B / "round20/PROBE_BLOCK.md"),
            "round20/agent1_switched_composite.md": sha(B / "round20/agent1_switched_composite.md"),
            "round20/role3/mathematical_preparation.md": sha(W / "mathematical_preparation.md")
        },
        "original_documents_sha256": {
            str(path): sha(path) for path in [
                Path(r"D:\Users\Utilisateur\Downloads\goldbach_synthesis.pdf"),
                Path(r"D:\Users\Utilisateur\Downloads\Goldbach_Continuation_Cofacteur_Court_2026-10-01.zip")]
        },
        "canonical_bank_and_root_compile_authorization_required": True,
        "semantic_limits": [
            "All source theorems remain uncompiled; declaration counts are not PASS counts.",
            "Bonferroni uses actual primorial divisors and all signed p/h/d/e cells, with p=minFac and p^2 admissible.",
            "Physical masks, theta/rawLambda difference, nonunits, floor caps, slack and composite tail remain literal.",
            "Shared-factor AP conductors use actual lcm/gcd; arithmetic principal uses phi(lcm).",
            "Actual remainder is physical AP mass minus its constructed main, without any assumed small Gamma.",
            "Ordinary AP endpoint/source bridge, B6 bounds, BV constants, SD, total reference price and full ledger target remain open.",
            "The canonical p0 branch has an explicit zero case and phi factor, but its net compensated gain is not credited.",
            "Source onset remains log N >= 10^24; the finite bank does not establish this onset."
        ],
        "authorization_schema": {
            "compile_authorization_token": "ROOT20_FORMAL3_COMPILE",
            "node_id": "13.12", "formal3_candidate_compilation_authorized": True,
            "root_full_read_current_formal3_sources_and_launcher_confirmed": True,
            "canonical_numeric_pass": True, "actual_identity_false": False,
            "actual_numeric_exit_code": 0,
            "authorized_new_modules": MODULES,
            "checked_inputs_sha256": "Nonempty root-verified project-relative bank producer/result/receipt bindings",
            "initial_sources_sha256": "Project-relative bindings for each of the six source modules",
            "launcher_sha256": "Root-reviewed current build_once.py SHA256",
            "preparation_sha256": "Root-reviewed current preparation.json SHA256",
            "allow_source_changed_repairs_after_actual_failure": "Boolean; never permits unchanged FAIL or PASS replay"
        }
    }

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--normalize-prints", action="store_true")
    args = parser.parse_args()
    started = W / "metadata_prepare01_started.json"
    with started.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps({"operation": "metadata_preparation_only",
                                 "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
                                 "actual_command": [sys.executable, "-B", str(Path(__file__)), *sys.argv[1:]],
                                 "metadata_script_sha256": sha(Path(__file__)),
                                 "launcher_sha256": sha(W / "build_once.py"),
                                 "source_sha256_before_normalization": {
                                     f"{m}.lean": sha(W / f"{m}.lean") for m in MODULES},
                                 "lean_invocations": 0, "numeric_invocations": 0}, indent=2) + "\n")
    with (W / "metadata_prepare01_source.py.txt").open("xb") as stream:
        stream.write(Path(__file__).read_bytes())
    manifest = metadata(args.normalize_prints)
    destination = W / "preparation.json"
    if destination.exists():
        raise RuntimeError("preparation.json already exists; preserve it and choose an explicitly new preparation")
    destination.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    with (W / "metadata_prepare01_receipt.json").open("x", encoding="utf-8") as stream:
        stream.write(json.dumps({"status": "METADATA_PREPARATION_COMPLETE",
                                 "finished_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
                                 "started_sha256": sha(started),
                                 "metadata_source_capture_sha256": sha(W / "metadata_prepare01_source.py.txt"),
                                 "preparation_sha256": sha(destination),
                                 "lean_invocations": 0, "numeric_invocations": 0}, indent=2) + "\n")
    print(json.dumps({"operation": "metadata_and_source_audit_normalization_only",
                      "preparation_sha256": sha(destination), "modules": len(MODULES),
                      "historical_modules": len(manifest["historical_module_closure"]),
                      "lean_invocations": 0, "numeric_invocations": 0,
                      "sources_sha256": {m["path"]: m["sha256"] for m in manifest["written_modules"]}}, indent=2))
