"""Round19 preflight: byte conservation only, never mathematical execution."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import sys

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
ROUND = BASE / "round19"
REGISTRY = ROUND / "previous_artifacts_sha256.json"
PROBE = ROUND / "PROBE_BLOCK.md"
RESULT = ROUND / "conservation.json"
EXPECTED_REGISTRY = "8c0abf930ee8c47b64d335ed286af4566fc674b573216f82f12b05c4ec877150"
EXPECTED_PROBE = "5f9e429bc264002044da60139f3942e7c3de909116d41e6cc52f70afb9a5a12d"
EXPECTED_CONTROLLER = "ce00517b1df6f4fc89f27667be44dd7f2c4d3331c8022fd14e4c505392175c5c"
CONTROLLER_REL = "round18/controller_manifest.json"
EXCLUDED_DIRECTORIES = {
    ".git", ".lake", ".arbor", "__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache",
}
ORIGINALS = {
    r"D:\Users\Utilisateur\Downloads\goldbach_synthesis.pdf":
        "bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24",
    r"D:\Users\Utilisateur\Downloads\Goldbach_Continuation_Cofacteur_Court_2026-10-01.zip":
        "32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd",
}


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def exclusive_json(path: Path, value: dict) -> str:
    text = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        handle.write(text)
    return text


def independent_inventory() -> list[str]:
    result = []
    base_real = BASE.resolve(strict=True)
    for current, dirs, files in os.walk(BASE, followlinks=False):
        current_path = Path(current)
        kept = []
        for name in dirs:
            if name in EXCLUDED_DIRECTORIES:
                continue
            if current_path == BASE:
                match = re.fullmatch(r"round(\d+)", name)
                if match and int(match.group(1)) >= 19:
                    continue
            child = current_path / name
            if child.is_symlink():
                raise RuntimeError(f"Unexpected directory symlink in protected inventory: {child}")
            kept.append(name)
        dirs[:] = sorted(kept)
        for name in sorted(files):
            path = current_path / name
            relative = path.relative_to(BASE).as_posix()
            if relative == "REPORT.md":
                continue
            if path.is_symlink():
                raise RuntimeError(f"Unexpected file symlink in protected inventory: {relative}")
            path.resolve(strict=True).relative_to(base_real)
            result.append(relative)
    if len(result) != len(set(result)):
        raise RuntimeError("Duplicate names in independent protected inventory")
    return sorted(result)


def main() -> int:
    if RESULT.exists():
        raise RuntimeError("Round19 conservation result already exists; no routine replay permitted")
    if sha256(REGISTRY) != EXPECTED_REGISTRY:
        raise RuntimeError("Round19 registry SHA mismatch before inspection")
    if sha256(PROBE) != EXPECTED_PROBE:
        raise RuntimeError("Round19 PROBE SHA mismatch before inspection")
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    expected = registry["sha256"]
    if registry["file_count"] != 1361 or len(expected) != 1361:
        raise RuntimeError("Round19 expected inventory must contain exactly 1361 bindings")
    if registry["previous997"] != 997 or registry["round18_with_controller364"] != 364:
        raise RuntimeError("Round19 historical union metadata mismatch")
    if registry["controller18_sha256"] != EXPECTED_CONTROLLER:
        raise RuntimeError("Round18 controller binding mismatch")
    if expected.get(CONTROLLER_REL) != EXPECTED_CONTROLLER:
        raise RuntimeError("Round18 controller missing from protected inventory")
    if registry["source_previous_registry_sha256"] != "05212665afffecade91134e1533f93d11eba8058179198e4420eef1fe252f2bc":
        raise RuntimeError("Inherited round18 registry identity mismatch")
    for relative, digest in expected.items():
        parts = Path(relative).parts
        if Path(relative).is_absolute() or ".." in parts or "\\" in relative:
            raise RuntimeError(f"Unsafe registry-relative path: {relative}")
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise RuntimeError(f"Malformed SHA binding: {relative}")
    actual_names = independent_inventory()
    expected_names = sorted(expected)
    missing = sorted(set(expected_names) - set(actual_names))
    extra = sorted(set(actual_names) - set(expected_names))
    changed = []
    observed = {}
    for relative in expected_names:
        path = BASE / relative
        if not path.is_file():
            continue
        digest = sha256(path)
        observed[relative] = digest
        if digest != expected[relative]:
            changed.append({"path": relative, "expected": expected[relative], "actual": digest})
    original_input_map = json.loads((BASE / "INPUT_HASHES.json").read_text(encoding="utf-8-sig"))
    if original_input_map != ORIGINALS:
        raise RuntimeError("Original PDF/ZIP declared SHA map differs from fixed inputs")
    original_observed = {}
    original_mismatches = []
    for name, expected_digest in ORIGINALS.items():
        path = Path(name)
        digest = sha256(path)
        original_observed[name] = {"sha256": digest, "expected": expected_digest, "equal": digest == expected_digest}
        if digest != expected_digest:
            original_mismatches.append(name)
    if sha256(REGISTRY) != EXPECTED_REGISTRY or sha256(PROBE) != EXPECTED_PROBE:
        raise RuntimeError("Preflight inputs changed during byte inspection")
    passed = not missing and not extra and not changed and not original_mismatches
    result = {
        "status": "PASS_EXACT_CONSERVATION" if passed else "FAIL_EXACT_CONSERVATION",
        "round": 19,
        "registry_sha256": EXPECTED_REGISTRY,
        "probe_sha256": EXPECTED_PROBE,
        "controller18_sha256": observed.get(CONTROLLER_REL),
        "expected_file_count": 1361,
        "actual_file_count": len(actual_names),
        "checked_sha256_count": len(observed),
        "historical_union": {"previous": 997, "round18_files": 363, "controller18": 1, "total": 1361},
        "missing": missing,
        "extra": extra,
        "changed": changed,
        "original_mismatches": original_mismatches,
        "originals": original_observed,
        "exact_inventory_names": actual_names,
        "observed_sha256": observed,
        "inventory_exclusions": sorted(EXCLUDED_DIRECTORIES) + ["root REPORT.md", "top-level round>=19"],
        "cache_directory_not_silently_excluded": True,
        "mathematical_execution": False,
        "old_preflight_executions": 0,
        "bank_W_D_log_sign_Lean_PDF_executions": 0,
        "original_files_hashed_only": True,
        "protected_files_written": 0,
        "victory": False,
    }
    text = exclusive_json(RESULT, result)
    sys.stdout.write(text)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
