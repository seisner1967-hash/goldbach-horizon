"""Exclusive Judge19 launcher. Its presence does not authorize execution.

Only ROOT19_JUDGE_CANONICAL_ATTEMPT01, issued after the frozen FINAL review,
permits one real audit. No author producer or historical Lean is invoked.
"""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
TOKEN = "ROOT19_JUDGE_CANONICAL_ATTEMPT01"


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def exclusive(path, obj):
    with Path(path).open("x", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(obj, ensure_ascii=False, sort_keys=True, indent=2) + "\n")


def bound(relative):
    p = (BASE / relative).resolve()
    assert p.is_relative_to(BASE.resolve()) and p.is_file(), ("unsafe_or_missing_input", relative)
    return p


def main():
    auth_path = HERE / "authorization.json"
    assert auth_path.exists(), "PREPARATION ONLY: separate root authorization absent"
    auth = load(auth_path)
    assert auth["authorization"] == TOKEN and auth["root_authorized"] is True
    assert auth["round"] == 19 and auth["role"] == 5
    assert auth["all_required_FINALs_inspected"] is True
    assert auth["independent_new_module_compile_authorized"] is True
    assert auth["canonical_NEW_numeric_results_inspected"] is True
    assert not (HERE / "audit_started.json").exists(), "Actual audit already started; no automatic rerun"
    prep_path = HERE / "preparation.json"
    assert sha(prep_path) == auth["preparation_sha256"]
    prep = load(prep_path)
    assert prep["status"] == "READY_AFTER_FROZEN_FINALS_NOT_EXECUTED"
    assert prep["round"] == 19 and prep["role"] == 5
    assert prep["all_required_FINALs_frozen"] is True
    assert set(auth["judge_code_sha256"]) == {"audit.py", "run_once.py"}
    for name, digest in auth["judge_code_sha256"].items():
        assert sha(HERE / name) == digest == prep["judge_code_sha256"][name]
    assert sha(PYTHON) == PYTHON_SHA == prep["python_sha256"]
    assert sha(LEAN) == LEAN_SHA == prep["lean_sha256"]
    for relative, digest in prep["final_input_sha256"].items():
        assert sha(bound(relative)) == digest, ("frozen_FINAL_input_changed", relative)
    for relative, digest in prep["historical_dependencies_sha256"].items():
        assert sha(bound(relative)) == digest, ("historical_dependency_changed", relative)
    modules = prep["new_module_source_order"]
    assert len(modules) == len(set(modules)) == prep["new_module_count"]
    assert set(modules) == set(prep["new_module_sources_sha256"])
    for relative in modules:
        p = bound(relative)
        assert p.suffix == ".lean" and p.parent in (ROUND / "role3", ROUND / "role4")
        assert sha(p) == prep["new_module_sources_sha256"][relative]
    preexec = HERE / "preexec"
    preexec.mkdir(exist_ok=False)
    captures = {}
    for p in (HERE / "audit.py", Path(__file__), auth_path, prep_path):
        target = preexec / (p.name + ".txt")
        with target.open("xb") as f:
            f.write(p.read_bytes())
        captures[p.name] = {"original": str(p), "snapshot": str(target), "sha256": sha(target)}
    for relative in modules:
        p = bound(relative)
        target = preexec / (p.parent.name + "__" + p.name + ".txt")
        with target.open("xb") as f:
            f.write(p.read_bytes())
        captures[relative] = {"original": str(p), "snapshot": str(target), "sha256": sha(target)}
    inputs = dict(prep, status="FROZEN_PREEXEC_AFTER_EXPLICIT_ROOT_GATE", frozen_utc=now(),
                  authorization_sha256=sha(auth_path), preparation_sha256=sha(prep_path),
                  PREEXEC_captures=captures)
    exclusive(HERE / "input_manifest.json", inputs)
    command = [str(PYTHON), "-B", "-X", "utf8", str(HERE / "audit.py")]
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONUTF8"] = "1"
    started = {"round": 19, "role": 5, "phase": "PREEXEC", "started_at_utc": now(),
               "root_authorization": TOKEN, "command": command, "cwd": str(HERE),
               "environment_changes": {"PYTHONDONTWRITEBYTECODE": "1", "PYTHONUTF8": "1"},
               "input_manifest_sha256": sha(HERE / "input_manifest.json"),
               "authorization_sha256": sha(auth_path), "preparation_sha256": sha(prep_path),
               "audit_source_sha256": sha(HERE / "audit.py"), "launcher_sha256": sha(Path(__file__)),
               "python_executable": str(PYTHON), "python_sha256": sha(PYTHON),
               "python_version_actual": sys.version, "lean_executable": str(LEAN),
               "lean_sha256": sha(LEAN), "compiler_version_metadata": prep["compiler_version_metadata"],
               "PREEXEC_captures": captures, "old_producer_Lean_kernel_PDF_executed": False}
    exclusive(HERE / "audit_started.json", started)
    emit = {"status": "ACTUAL_UNIQUE_JUDGE19_STARTED", "started_at_utc": started["started_at_utc"],
            "new_modules": len(modules), "input_manifest_sha256": started["input_manifest_sha256"]}
    print(json.dumps(emit), flush=True)
    launch_error = None
    try:
        with (HERE / "audit.log").open("xb") as f:
            run = subprocess.run(command, cwd=HERE, env=env, stdout=f, stderr=subprocess.STDOUT)
        exit_code = run.returncode
    except BaseException as exc:
        launch_error = repr(exc)
        exit_code = 1
        if not (HERE / "audit.log").exists():
            with (HERE / "audit.log").open("xb") as f:
                f.write((launch_error + "\n").encode("utf-8"))
    result = dict(started, phase="FINISHED", finished_at_utc=now(), exit_code=exit_code,
                  subprocess_launch_error=launch_error, log_sha256=sha(HERE / "audit.log"))
    if (HERE / "audit_receipt.json").exists():
        result["audit_receipt_sha256"] = sha(HERE / "audit_receipt.json")
    exclusive(HERE / "launch_receipt.json", result)
    print(json.dumps({"exit_code": exit_code, "log_sha256": result["log_sha256"]}), flush=True)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
