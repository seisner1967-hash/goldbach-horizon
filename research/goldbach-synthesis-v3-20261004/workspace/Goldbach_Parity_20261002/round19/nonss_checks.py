"""NEW non-SS19 producer, callable only from the explicitly gated launcher.

The canonical invocation runs this PREEXEC capture and imports only captured
NEW bank/arithmetic helpers.  Importing the original file runs no mathematics.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    sys.dont_write_bytecode = True
    sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-authorization", required=True)
    parser.add_argument("--captured-manifest", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    if not args.root_authorization.startswith("ROOT19_NONSS"):
        raise RuntimeError("Distinct ROOT19_NONSS authorization required")
    if os.environ.get("ROOT19_NONSS_PREEXEC_GATE") != args.root_authorization:
        raise RuntimeError("Missing actual gated PREEXEC environment")
    manifest_path = Path(args.captured_manifest).resolve()
    snapshot_dir = manifest_path.parent
    if Path(__file__).resolve().parent != snapshot_dir or snapshot_dir.parent.name != "canonical_attempt01":
        raise RuntimeError("Only the NEW canonical PREEXEC producer capture may run")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    for name, item in manifest["captures"].items():
        if digest(item["snapshot"]) != item["sha256"]:
            raise RuntimeError(f"PREEXEC capture changed: {name}")
    contract = json.loads(Path(manifest["captures"]["contract"]["snapshot"]).read_text(encoding="utf-8"))
    assert contract["N"] == 100000000 and contract["window"] == {
        "left": 1600100, "right": 1601100, "endpoints_inclusive": True, "all_integer_positions": 1001}
    assert contract["fixed_parameters"] == {"alpha": 100, "a": 3163, "Q": 999999, "M": 1000000, "p0": 3, "Z": 100}
    assert contract["auxiliary_identity_scale"]["B_test"] == 2048
    assert contract["source_onset_logN"] == "10^24 unchanged"
    output = Path(args.output).resolve()
    expected_output = Path(manifest["result"]).resolve()
    assert output == expected_output and not output.exists()
    sys.path.insert(0, str(snapshot_dir))
    import bank
    import arithmetic
    assert Path(bank.__file__).resolve() == snapshot_dir / "bank.py"
    assert Path(arithmetic.__file__).resolve() == snapshot_dir / "arithmetic.py"
    result = bank.run_bank()
    result["root_authorization"] = args.root_authorization
    result["input_manifest_sha256"] = digest(manifest_path)
    result["captured_inputs_binding"] = manifest["captures"]
    with output.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, separators=(",", ":"), sort_keys=True, ensure_ascii=False)
        handle.write("\n")
    print(json.dumps({"status": result["status"], "counts": result["counts"],
                      "falsifier_statuses": {k: v["status"] for k, v in result["falsifiers"].items()},
                      "kernel_sign_positions_counts": result["kernel_sign_positions_counts"],
                      "result_sha256": digest(output), "victory": False}, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
