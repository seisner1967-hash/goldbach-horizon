"""Unique Judge20 launcher, inert without the separate reviewed root gate."""
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
TOKEN = "ROOT20_JUDGE_AUTHORIZED"


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


def exclusive(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n")


def resolve(name):
    return Path(name) if Path(name).is_absolute() else BASE / name


def verify(bindings):
    for name, digest in bindings.items():
        assert sha(resolve(name)) == digest, ("frozen_input_changed", name)


def main():
    auth_path, prep_path = HERE / "authorization.json", HERE / "preparation.json"
    assert auth_path.is_file(), "PREPARATION ONLY: ROOT20_JUDGE_AUTHORIZED gate absent"
    auth = load(auth_path)
    assert auth["authorization"] == TOKEN and auth["root_authorized"] is True
    assert auth["round"] == 20 and auth["role"] == 5
    assert auth["all_required_FINALs_inspected"] is True
    assert auth["independent_new_module_compile_authorized"] is True
    assert auth["root_FULL_judge_sources_and_preparation_read"] is True
    assert auth["canonical_NEW_numeric_results_inspected"] is True
    assert not any((HERE / name).exists() for name in
                   ("audit_started.json", "input_manifest.json", "preexec", "audit")), "No audit replay"
    assert sha(prep_path) == auth["preparation_sha256"]
    prep = load(prep_path)
    assert prep["status"] == "READY_AFTER_ALL_FROZEN_FINALS_NOT_EXECUTED"
    assert prep["all_required_FINALs_frozen"] is True and prep["new_module_count"] == 16
    assert set(auth["judge_code_sha256"]) == set(prep["judge_code_sha256"]) == {
        "audit.py", "run_once.py", "prepare.py"}
    for name, digest in auth["judge_code_sha256"].items():
        assert sha(HERE / name) == digest == prep["judge_code_sha256"][name]
    assert sha(PYTHON) == PYTHON_SHA == prep["python_sha256"]
    assert sha(LEAN) == LEAN_SHA == prep["lean_sha256"]
    groups = ("final_input_sha256", "historical_dependencies_sha256", "new_module_sources_sha256",
              "numeric_frozen_sha256", "previous_artifacts_sha256", "original_documents_sha256",
              "runtime_bindings_sha256")
    for group in groups:
        verify(prep[group])
    modules = prep["new_module_source_order"]
    assert len(modules) == len(set(modules)) == 16
    assert set(modules) == set(prep["new_module_sources_sha256"])
    for relative in modules:
        p = resolve(relative).resolve()
        assert p.parent in {(ROUND / name).resolve() for name in ("role3", "role4", "role4_geometry")}
        assert p.suffix == ".lean"
    preexec = HERE / "preexec"
    preexec.mkdir(exist_ok=False)
    captures = {}
    paths = [(name, HERE / name) for name in prep["judge_code_sha256"]]
    paths += [("authorization.json", auth_path), ("preparation.json", prep_path)]
    paths += [(relative, resolve(relative)) for relative in modules]
    for label, p in paths:
        target = preexec / (label.replace("/", "__").replace("\\", "__") + ".txt")
        with target.open("xb") as f:
            f.write(p.read_bytes())
        assert sha(p) == sha(target)
        captures[label] = {"original": str(p), "snapshot": str(target), "sha256": sha(target)}
    inputs = dict(prep, status="FROZEN_PREEXEC_AFTER_ROOT_GATE", frozen_utc=now(), authorization=TOKEN,
                  authorization_sha256=sha(auth_path), preparation_sha256=sha(prep_path),
                  PREEXEC_captures=captures)
    exclusive(HERE / "input_manifest.json", inputs)
    command = [str(PYTHON), "-B", "-X", "utf8", str(HERE / "audit.py")]
    env = dict(os.environ)
    env.update(PYTHONDONTWRITEBYTECODE="1", PYTHONUTF8="1", PYTHONIOENCODING="utf-8")
    started = {"round": 20, "role": 5, "phase": "PREEXEC", "started_utc": now(),
               "authorization": TOKEN, "command": command, "cwd": str(HERE),
               "input_manifest_sha256": sha(HERE / "input_manifest.json"),
               "authorization_sha256": sha(auth_path), "preparation_sha256": sha(prep_path),
               "judge_code_sha256": prep["judge_code_sha256"], "PREEXEC_captures": captures,
               "python_executable": str(PYTHON), "python_sha256": sha(PYTHON),
               "python_version_actual": sys.version, "lean_executable": str(LEAN),
               "lean_sha256": sha(LEAN), "compiler_version_metadata": prep["compiler_version_metadata"],
               "environment_changes": {"PYTHONDONTWRITEBYTECODE": "1", "PYTHONUTF8": "1",
                                       "PYTHONIOENCODING": "utf-8"},
               "old_math_Lean_producer_PDF_executed": False}
    exclusive(HERE / "audit_started.json", started)
    print(json.dumps({"status": "ACTUAL_UNIQUE_JUDGE20_STARTED", "started_utc": started["started_utc"],
                      "new_modules": 16, "input_manifest_sha256": started["input_manifest_sha256"]}), flush=True)
    launch_error = None
    try:
        with (HERE / "audit.log").open("xb") as f:
            run = subprocess.run(command, cwd=HERE, env=env, stdout=f, stderr=subprocess.STDOUT)
        code = run.returncode
    except BaseException as exc:
        launch_error, code = repr(exc), None
        if not (HERE / "audit.log").exists():
            with (HERE / "audit.log").open("xb") as f:
                f.write((launch_error + "\n").encode("utf-8"))
    result = dict(started, phase="FINISHED_RAW", finished_utc=now(), actual_exit_code=code,
                  launch_error=launch_error, audit_log_sha256=sha(HERE / "audit.log"))
    if (HERE / "audit_receipt.json").exists():
        result["audit_receipt_sha256"] = sha(HERE / "audit_receipt.json")
    exclusive(HERE / "launch_receipt.json", result)
    changed = []
    for group in groups:
        for name, digest in prep[group].items():
            if not resolve(name).is_file() or sha(resolve(name)) != digest:
                changed.append({"group": group, "path": name})
    assert sha(auth_path) == inputs["authorization_sha256"]
    assert sha(prep_path) == inputs["preparation_sha256"]
    for name, digest in prep["judge_code_sha256"].items():
        assert sha(HERE / name) == digest
    exclusive(HERE / "launch_post_integrity.json", {"finished_utc": now(), "changed_inputs": changed,
                                                   "all_frozen_bindings_unchanged": not changed,
                                                   "credited_pass": code == 0 and not changed})
    print(json.dumps({"actual_exit_code": code, "changed_inputs": len(changed),
                      "audit_log_sha256": result["audit_log_sha256"]}), flush=True)
    return code if code is not None and not changed else 1


if __name__ == "__main__":
    sys.exit(main())
