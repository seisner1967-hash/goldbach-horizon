"""NEW one-shot all-rank19 launcher, explicit separate ROOT19_RANK gate.

Captures sources and inputs BEFORE the only subprocess; preserves binary
catalogs, result, command, log and exit even on failure.  No replay logic.
"""
import argparse
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

BASE=Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
ROUND=BASE/"round19"
OWN=ROUND/"role6_rank"
SOURCE=ROUND/"allrang_checks.py"
LAUNCHER=OWN/"run_rank_once.py"
PREPARATION=OWN/"preparation.json"
PYTHON=Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")


def utc():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as handle:
        for block in iter(lambda:handle.read(1024*1024),b""):
            h.update(block)
    return h.hexdigest()


def write_json(path,value):
    with path.open("x",encoding="utf-8",newline="\n") as handle:
        json.dump(value,handle,indent=2,sort_keys=True,ensure_ascii=False)
        handle.write("\n")


def capture(path,target):
    data=path.read_bytes()
    with target.open("xb") as handle:
        handle.write(data)
    return {"original":str(path),"snapshot":str(target),"sha256":hashlib.sha256(data).hexdigest(),"bytes":len(data)}


def main():
    sys.dont_write_bytecode=True
    sys.set_int_max_str_digits(0)
    parser=argparse.ArgumentParser()
    parser.add_argument("--root-authorization",required=True)
    parser.add_argument("--source-sha256",required=True)
    parser.add_argument("--launcher-sha256",required=True)
    parser.add_argument("--preparation-sha256",required=True)
    args=parser.parse_args()
    if not args.root_authorization.startswith("ROOT19_RANK"):
        raise RuntimeError("Distinct ROOT19_RANK authorization after full root read is required")
    if Path(sys.executable).resolve()!=PYTHON.resolve():
        raise RuntimeError("Unexpected Python runtime")
    for path,expected in ((SOURCE,args.source_sha256),(LAUNCHER,args.launcher_sha256),(PREPARATION,args.preparation_sha256)):
        if digest(path)!=expected:
            raise RuntimeError(f"Prepared SHA mismatch: {path}")
    preparation=json.loads(PREPARATION.read_text(encoding="utf-8"))
    bindings=preparation["bindings"]
    for name,item in bindings.items():
        if digest(item["path"])!=item["sha256"]:
            raise RuntimeError(f"Prepared input changed: {name}")
    attempt=OWN/"canonical_attempt01"
    result=ROUND/"allrang.json"
    if attempt.exists() or result.exists():
        raise RuntimeError("NEW all-rank canonical attempt already reserved, no routine replay")
    attempt.mkdir()
    inputs,outputs=attempt/"inputs",attempt/"outputs"
    inputs.mkdir()
    outputs.mkdir()
    reserved,started,receipt=(attempt/name for name in ("reserved.json","started.json","receipt.json"))
    log,input_manifest=attempt/"producer.log",inputs/"input_manifest.json"
    write_json(reserved,{"reserved_at_utc":utc(),"round":19,"node":"13.11","attempt":1,
                         "root_authorization":args.root_authorization,"subprocess_started":False})
    filenames={"producer":"producer.py","strict_rank":"strict_rank.py","rank_bank":"rank_bank.py",
               "launcher":"launcher.py.txt","contract":"contract.json","FINAL1":"FINAL1.md","probe":"probe.md",
               "prompt":"executor_prompt.md","role1_manifest":"role1_manifest.json","role1_receipt":"role1_receipt.json",
               "registry1361":"registry1361.json","preflight19_receipt":"preflight19_final_receipt.json"}
    captures={}
    for name,item in bindings.items():
        captures[name]=capture(Path(item["path"]),inputs/filenames[name])
        if captures[name]["sha256"]!=item["sha256"]:
            raise RuntimeError(f"Input changed between validation and immutable PREEXEC capture: {name}")
    captures["preparation"]=capture(PREPARATION,inputs/"preparation.json")
    if captures["preparation"]["sha256"]!=args.preparation_sha256:
        raise RuntimeError("Preparation changed before its capture")
    write_json(input_manifest,{"round":19,"node":"13.11","attempt":1,"captured_at_utc":utc(),
                               "captures":captures,"result":str(result),"artifacts_directory":str(outputs)})
    command=[str(PYTHON),"-B","-X","utf8",captures["producer"]["snapshot"],
             "--root-authorization",args.root_authorization,"--captured-manifest",str(input_manifest),"--output",str(result)]
    started_value={"started_at_utc":utc(),"round":19,"role":6,"node":"13.11","attempt":1,
        "root_authorization":args.root_authorization,"subprocess_command":command,
        "launcher_command":[str(PYTHON),"-B","-X","utf8",str(LAUNCHER),"--root-authorization",args.root_authorization,
                            "--source-sha256",args.source_sha256,"--launcher-sha256",args.launcher_sha256,
                            "--preparation-sha256",args.preparation_sha256],
        "cwd":str(attempt),"python_sha256":digest(PYTHON),"PREEXEC_captures":captures,
        "input_manifest_sha256":digest(input_manifest),"result":str(result),"log":str(log),
        "artifacts_directory":str(outputs),"environment_changes":{"PYTHONDONTWRITEBYTECODE":"1","PYTHONUTF8":"1",
                                                                "ROOT19_RANK_PREEXEC_GATE":args.root_authorization},
        "W_D_kernel_parent_or_old_preflight_Lean_PDF_execution":False,"victory":False}
    write_json(started,started_value)
    print(json.dumps({"actual_START":started_value["started_at_utc"],"started_receipt":str(started),
                      "started_receipt_sha256":digest(started),"subprocess_command":command}),flush=True)
    environment=os.environ.copy()
    environment.update(started_value["environment_changes"])
    exit_code,launch_error=None,None
    with log.open("xb") as handle:
        try:
            completed=subprocess.run(command,cwd=attempt,env=environment,stdout=handle,stderr=subprocess.STDOUT,check=False)
            exit_code=completed.returncode
        except OSError as error:
            launch_error={"type":type(error).__name__,"message":str(error)}
            handle.write((repr(error)+"\n").encode("utf-8"))
    produced={str(path.relative_to(attempt)).replace("\\","/"):{"sha256":digest(path),"bytes":path.stat().st_size}
              for path in sorted(outputs.rglob("*")) if path.is_file()}
    post={**started_value,"finished_at_utc":utc(),"exit_code":exit_code,"subprocess_launch_error":launch_error,
          "started_receipt_sha256":digest(started),"log_sha256":digest(log),
          "result_sha256":digest(result) if result.is_file() else None,
          "result_bytes":result.stat().st_size if result.is_file() else None,"produced_binary_or_compressed_catalogs":produced,
          "captured_binding_hashes_unchanged_after_execution":all(digest(v["snapshot"])==v["sha256"] for v in captures.values()),
          "prepared_original_binding_hashes_unchanged_after_execution":all(digest(v["path"])==v["sha256"] for v in bindings.values()),
          "new_canonical_invocations":1,"automatic_replay":False,"victory":False}
    write_json(receipt,post)
    print(json.dumps({"actual_FINISH":post["finished_at_utc"],"exit_code":exit_code,"launch_error":launch_error,
        "receipt_sha256":digest(receipt),"log_sha256":post["log_sha256"],"result_sha256":post["result_sha256"],
        "produced_binary_or_compressed_catalogs":produced},indent=2),flush=True)
    return 2 if launch_error else int(exit_code)


if __name__=="__main__":
    raise SystemExit(main())
