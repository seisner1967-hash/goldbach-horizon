"""Round21 unique metadata-only inventory and byte conservation. No mathematics."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import sys

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
ROUND = BASE / "round21"
REGISTRY = ROUND / "previous_artifacts_sha256.json"
PROBE = ROUND / "PROBE_BLOCK.md"
RESULT = ROUND / "conservation.json"
EXPECTED_REGISTRY = "5c1c372a2a723a1a06224c6531c2e0775978bbe902f02cf910450a583772896c"
EXPECTED_PROBE = "015cccf57d59c53abd34f4b6623b891199fdb61a9f8acafcd4f352df0b8fd7de"
EXPECTED_CONTROLLER = "815d2ce77851a01d9addfa4202a17edb787a42f7f080d4e41cab18aa7b002b04"
EXPECTED_PREVIOUS_REGISTRY = "9f238497b57a2dc7e46e26a67cb5e6a468be8f4e6a73525449a87406304a36b5"
CONTROLLER_REL = "round20/controller_manifest.json"
EXCLUDED_DIRECTORIES = {
    ".git", ".lake", ".arbor", "cache", "__pycache__", ".pytest_cache",
    ".mypy_cache", ".ruff_cache",
}
ORIGINALS = {
    r"D:\Users\Utilisateur\Downloads\goldbach_synthesis.pdf":
        "bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24",
    r"D:\Users\Utilisateur\Downloads\Goldbach_Continuation_Cofacteur_Court_2026-10-01.zip":
        "32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd",
}


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def original_observation() -> dict:
    return {name: {"expected": expected, "actual": digest(Path(name))}
            for name, expected in ORIGINALS.items()}


def inventory() -> list[str]:
    base_real = BASE.resolve(strict=True)
    names = []
    for current, directories, files in os.walk(BASE, followlinks=False):
        current_path = Path(current)
        retained = []
        for name in sorted(directories):
            if name in EXCLUDED_DIRECTORIES:
                continue
            match = re.fullmatch(r"round(\d+)", name)
            if current_path == BASE and match and int(match.group(1)) >= 21:
                continue
            path = current_path / name
            if path.is_symlink() or (hasattr(path, "is_junction") and path.is_junction()):
                raise RuntimeError(f"Protected directory link rejected: {path}")
            path.resolve(strict=True).relative_to(base_real)
            retained.append(name)
        directories[:] = retained
        for name in sorted(files):
            path = current_path / name
            relative = path.relative_to(BASE).as_posix()
            if relative == "REPORT.md":
                continue
            if path.is_symlink():
                raise RuntimeError(f"Protected file link rejected: {relative}")
            path.resolve(strict=True).relative_to(base_real)
            names.append(relative)
    if len(names) != len(set(names)):
        raise RuntimeError("Duplicate protected inventory names")
    return sorted(names)


def observe(expected: dict[str, str]) -> dict:
    names = inventory()
    missing = sorted(set(expected) - set(names))
    extra = sorted(set(names) - set(expected))
    actual = {}
    changed = []
    for name in sorted(expected):
        path = BASE / name
        if not path.is_file():
            continue
        actual[name] = digest(path)
        if actual[name] != expected[name]:
            changed.append({"path": name, "expected": expected[name], "actual": actual[name]})
    originals = original_observation()
    original_map_equal = json.loads((BASE / "INPUT_HASHES.json").read_text(
        encoding="utf-8-sig")) == ORIGINALS
    registry_sha = digest(REGISTRY)
    probe_sha = digest(PROBE)
    originals_equal = all(entry["actual"] == entry["expected"] for entry in originals.values())
    passed = (not missing and not extra and not changed and original_map_equal
              and originals_equal and registry_sha == EXPECTED_REGISTRY
              and probe_sha == EXPECTED_PROBE)
    return {
        "passed": passed, "actual_file_count": len(names),
        "checked_sha256_count": len(actual), "missing": missing,
        "extra": extra, "changed": changed, "originals": originals,
        "original_hash_map_equal": original_map_equal,
        "registry_sha256": registry_sha, "probe_sha256": probe_sha,
        "exact_inventory_names": names, "observed_sha256": actual,
    }


def main() -> int:
    if RESULT.exists():
        raise RuntimeError("Round21 result exists: unique preflight replay rejected")
    if digest(REGISTRY) != EXPECTED_REGISTRY or digest(PROBE) != EXPECTED_PROBE:
        raise RuntimeError("Frozen registry/PROBE byte identity mismatch")
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    expected = registry["sha256"]
    if (registry.get("file_count") != 3028 or len(expected) != 3028
            or registry.get("previous1808") != 1808
            or registry.get("round20_with_controller1220") != 1220):
        raise RuntimeError("Protected union must equal 1808 + 1220 = 3028")
    if (registry.get("controller20_sha256") != EXPECTED_CONTROLLER
            or expected.get(CONTROLLER_REL) != EXPECTED_CONTROLLER
            or registry.get("source_previous_registry_sha256") != EXPECTED_PREVIOUS_REGISTRY):
        raise RuntimeError("Historical registry/controller chain mismatch")
    for name, value in expected.items():
        path = Path(name)
        if (path.is_absolute() or ".." in path.parts or "\\" in name
                or path.as_posix() != name or ":" in name):
            raise RuntimeError(f"Noncanonical protected relative path: {name}")
        if any(part in EXCLUDED_DIRECTORIES for part in path.parts):
            raise RuntimeError(f"Exclusion cannot hide a protected binding: {name}")
        if name == "REPORT.md":
            raise RuntimeError("Mutable REPORT must not belong to frozen registry")
        if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value):
            raise RuntimeError(f"Malformed SHA256 binding: {name}")
    before = observe(expected)
    after = observe(expected)
    stable = (before["exact_inventory_names"] == after["exact_inventory_names"]
              and before["observed_sha256"] == after["observed_sha256"]
              and before["originals"] == after["originals"])
    passed = before["passed"] and after["passed"] and stable
    result = {
        "status": "PASS_EXACT_CONSERVATION" if passed else "FAIL_EXACT_CONSERVATION",
        "round": 21, "role": 6, "attempt": 1,
        "expected_file_count": 3028,
        "historical_union": {"previous": 1808, "round20_files": 1219,
                             "controller20": 1, "total": 3028},
        "registry_sha256": EXPECTED_REGISTRY, "probe_sha256": EXPECTED_PROBE,
        "controller20_sha256": after["observed_sha256"].get(CONTROLLER_REL),
        "before": before, "after": after, "unchanged_between_stages": stable,
        "inventory_exclusions": sorted(EXCLUDED_DIRECTORIES)
                                + ["root REPORT.md", "top-level round>=21"],
        "exclusions_cannot_hide_protected_bindings": True,
        "metadata_only": True, "mathematical_execution": False,
        "old_preflight_executions": 0, "Lean_executions": 0,
        "bank_W_D_log_sign_kernel_PDF_executions": 0,
        "original_files_hashed_only": True, "protected_files_written": 0,
        "victory": False,
    }
    with RESULT.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2, ensure_ascii=False, sort_keys=True)
        handle.write("\n")
    print(json.dumps({"status": result["status"], "result": str(RESULT),
                      "result_sha256": digest(RESULT), "before_count": before["actual_file_count"],
                      "after_count": after["actual_file_count"], "mathematical_execution": False,
                      "victory": False}, indent=2, sort_keys=True))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
