"""New round20 preflight: exact byte conservation only, no mathematical execution."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import sys

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
ROUND = BASE / "round20"
REGISTRY = ROUND / "previous_artifacts_sha256.json"
PROBE = ROUND / "PROBE_BLOCK.md"
RESULT = ROUND / "conservation.json"
EXPECTED_REGISTRY = "9f238497b57a2dc7e46e26a67cb5e6a468be8f4e6a73525449a87406304a36b5"
EXPECTED_PROBE = "69df06d7abc3619ba51465b74912f6bf32a2f49f901d72533c4ba9945777685e"
EXPECTED_CONTROLLER = "299a605efaa7cf6721e3b65bfea8af976bcbfcdbb1bc841eee6f4a0d9d9d4d08"
CONTROLLER_REL = "round19/controller_manifest.json"
EXPECTED_PREVIOUS_REGISTRY = "8c0abf930ee8c47b64d335ed286af4566fc674b573216f82f12b05c4ec877150"
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
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def exclusive_json(path: Path, value: dict) -> str:
    text = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        handle.write(text)
    return text


def independent_inventory() -> list[str]:
    names = []
    base_real = BASE.resolve(strict=True)
    for current, dirs, files in os.walk(BASE, followlinks=False):
        current_path = Path(current)
        kept = []
        for name in dirs:
            if name in EXCLUDED_DIRECTORIES:
                continue
            if current_path == BASE:
                match = re.fullmatch(r"round(\d+)", name)
                if match and int(match.group(1)) >= 20:
                    continue
            child = current_path / name
            if child.is_symlink() or (hasattr(child, "is_junction") and child.is_junction()):
                raise RuntimeError(f"Unexpected linked directory in protected inventory: {child}")
            child.resolve(strict=True).relative_to(base_real)
            kept.append(name)
        dirs[:] = sorted(kept)
        for name in sorted(files):
            path = current_path / name
            relative = path.relative_to(BASE).as_posix()
            if relative == "REPORT.md":
                continue
            if path.is_symlink():
                raise RuntimeError(f"Unexpected linked file in protected inventory: {relative}")
            path.resolve(strict=True).relative_to(base_real)
            names.append(relative)
    if len(names) != len(set(names)):
        raise RuntimeError("Duplicate names in independent protected inventory")
    return sorted(names)


def inspect_stage(expected: dict[str, str]) -> dict:
    names = independent_inventory()
    expected_names = sorted(expected)
    missing = sorted(set(expected_names) - set(names))
    extra = sorted(set(names) - set(expected_names))
    observed = {}
    changed = []
    for relative in expected_names:
        path = BASE / relative
        if not path.is_file():
            continue
        digest = sha256(path)
        observed[relative] = digest
        if digest != expected[relative]:
            changed.append({"path": relative, "expected": expected[relative], "actual": digest})
    original_hash_map = json.loads((BASE / "INPUT_HASHES.json").read_text(encoding="utf-8-sig"))
    original_map_equal = original_hash_map == ORIGINALS
    original_observed = {}
    original_mismatches = []
    for name, expected_digest in ORIGINALS.items():
        digest = sha256(Path(name))
        original_observed[name] = {
            "sha256": digest, "expected": expected_digest, "equal": digest == expected_digest,
        }
        if digest != expected_digest:
            original_mismatches.append(name)
    registry_digest = sha256(REGISTRY)
    probe_digest = sha256(PROBE)
    passed = (not missing and not extra and not changed and not original_mismatches
              and original_map_equal and registry_digest == EXPECTED_REGISTRY
              and probe_digest == EXPECTED_PROBE)
    return {
        "passed": passed,
        "actual_file_count": len(names),
        "checked_sha256_count": len(observed),
        "missing": missing, "extra": extra, "changed": changed,
        "original_hash_map_equal": original_map_equal,
        "original_mismatches": original_mismatches,
        "originals": original_observed,
        "registry_sha256": registry_digest, "probe_sha256": probe_digest,
        "exact_inventory_names": names, "observed_sha256": observed,
    }


def main() -> int:
    if RESULT.exists():
        raise RuntimeError("Round20 result already exists; no routine preflight replay permitted")
    if sha256(REGISTRY) != EXPECTED_REGISTRY or sha256(PROBE) != EXPECTED_PROBE:
        raise RuntimeError("Round20 registry or PROBE SHA mismatch before inspection")
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    expected = registry["sha256"]
    if registry["file_count"] != 1808 or len(expected) != 1808:
        raise RuntimeError("Round20 expected inventory must contain exactly 1808 bindings")
    if registry["previous1361"] != 1361 or registry["round19_with_controller447"] != 447:
        raise RuntimeError("Round20 historical union metadata mismatch")
    if registry["controller19_sha256"] != EXPECTED_CONTROLLER:
        raise RuntimeError("Round19 controller binding mismatch")
    if expected.get(CONTROLLER_REL) != EXPECTED_CONTROLLER:
        raise RuntimeError("Round19 controller missing from protected inventory")
    if registry["source_previous_registry_sha256"] != EXPECTED_PREVIOUS_REGISTRY:
        raise RuntimeError("Inherited round19 registry identity mismatch")
    for relative, digest in expected.items():
        parts = Path(relative).parts
        if Path(relative).is_absolute() or ".." in parts or "\\" in relative:
            raise RuntimeError(f"Unsafe registry-relative path: {relative}")
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise RuntimeError(f"Malformed SHA binding: {relative}")
    before = inspect_stage(expected)
    after = inspect_stage(expected)
    unchanged_between_stages = (before["exact_inventory_names"] == after["exact_inventory_names"]
                               and before["observed_sha256"] == after["observed_sha256"]
                               and before["originals"] == after["originals"])
    passed = before["passed"] and after["passed"] and unchanged_between_stages
    result = {
        "status": "PASS_EXACT_CONSERVATION" if passed else "FAIL_EXACT_CONSERVATION",
        "round": 20,
        "registry_sha256": EXPECTED_REGISTRY, "probe_sha256": EXPECTED_PROBE,
        "controller19_sha256": after["observed_sha256"].get(CONTROLLER_REL),
        "expected_file_count": 1808,
        "historical_union": {"previous": 1361, "round19_files": 446, "controller19": 1, "total": 1808},
        "before": before, "after": after,
        "unchanged_between_stages": unchanged_between_stages,
        "inventory_exclusions": sorted(EXCLUDED_DIRECTORIES) + ["root REPORT.md", "top-level round>=20"],
        "cache_directory_not_silently_excluded": True,
        "mathematical_execution": False,
        "old_preflight_executions": 0,
        "bank_W_D_log_sign_Lean_PDF_executions": 0,
        "original_files_hashed_only": True,
        "protected_files_written": 0,
        "victory": False,
    }
    sys.stdout.write(exclusive_json(RESULT, result))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
