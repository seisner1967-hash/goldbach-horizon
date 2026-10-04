"""NEW all-rank19 producer; only a ROOT19_RANK PREEXEC capture may execute."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys


def digest(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as handle:
        for block in iter(lambda:handle.read(1024*1024),b""):
            h.update(block)
    return h.hexdigest()


def main():
    sys.dont_write_bytecode=True
    sys.set_int_max_str_digits(0)
    parser=argparse.ArgumentParser()
    parser.add_argument("--root-authorization",required=True)
    parser.add_argument("--captured-manifest",required=True)
    parser.add_argument("--output",required=True)
    args=parser.parse_args()
    if not args.root_authorization.startswith("ROOT19_RANK"):
        raise RuntimeError("Distinct explicit ROOT19_RANK authorization required")
    if os.environ.get("ROOT19_RANK_PREEXEC_GATE")!=args.root_authorization:
        raise RuntimeError("Missing actual gated PREEXEC environment")
    manifest_path=Path(args.captured_manifest).resolve()
    snapshot_dir=manifest_path.parent
    if Path(__file__).resolve().parent!=snapshot_dir or snapshot_dir.parent.name!="canonical_attempt01":
        raise RuntimeError("Only NEW canonical PREEXEC capture may run")
    manifest=json.loads(manifest_path.read_text(encoding="utf-8"))
    for name,item in manifest["captures"].items():
        if digest(item["snapshot"])!=item["sha256"]:
            raise RuntimeError(f"PREEXEC capture changed: {name}")
    contract=json.loads(Path(manifest["captures"]["contract"]["snapshot"]).read_text(encoding="utf-8"))
    assert contract["N"]==100000000 and contract["candidate_left_exclusive"]==12000000
    assert contract["candidate_right_inclusive"]==24000000 and contract["candidate_integer_positions"]==12000000
    assert contract["R_source"]==2 and contract["R_test"]==17
    assert contract["acquired_S_box"]==["2541/1536","11011/6144"]
    output=Path(args.output).resolve()
    assert output==Path(manifest["result"]).resolve() and not output.exists()
    artifacts=Path(manifest["artifacts_directory"]).resolve()
    assert artifacts==snapshot_dir.parent/"outputs" and artifacts.is_dir() and not list(artifacts.iterdir())
    sys.path.insert(0,str(snapshot_dir))
    import strict_rank
    import rank_bank
    assert Path(strict_rank.__file__).resolve()==snapshot_dir/"strict_rank.py"
    assert Path(rank_bank.__file__).resolve()==snapshot_dir/"rank_bank.py"
    result=rank_bank.run_bank(artifacts)
    result["captured_inputs_binding"]=manifest["captures"]
    result["input_manifest_sha256"]=digest(manifest_path)
    result["root_authorization"]=args.root_authorization
    with output.open("x",encoding="utf-8",newline="\n") as handle:
        json.dump(result,handle,separators=(",",":"),sort_keys=True,ensure_ascii=False)
        handle.write("\n")
    print(json.dumps({"status":result["status"],"counts":result["counts"],
        "global_signs":{measure:{name:value["whole_box_sign"] for name,value in functions.items()}
                        for measure,functions in result["global_actual_affine_functionals_theta_raw_PP"].items()},
        "falsifier_statuses":{name:value["status"] for name,value in result["falsifiers"].items()},
        "result_sha256":digest(output),"victory":False},indent=2,sort_keys=True),flush=True)
    return 0


if __name__=="__main__":
    raise SystemExit(main())
