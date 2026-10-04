"""DRAFT SOURCE metadata launcher, not invoked; exactly one future math child.

No mathematical source is imported by this controller. It verifies a distinct
ROOT gate, immutable preparation/review bytes,3090 registry+archive objects,
and conservative bundled Python runtime bindings. No retry or resume path.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import uuid

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[3]
PREPARATION = HERE/"preparation22.json"
ACTUAL = HERE/"actual_attempt01"
GATE = BASE/".arbor/sessions/parity/.coordinator/messages/round22_global_thermal_h1_authorization02.json"
SCOPE = "ROUND22_GLOBAL_THERMAL_H1_NUMERIC_ONLY"
BANK = "THERMAL_GLOBAL_H1_22_SOURCEPACK02"
EVALUATION_LEVEL = "PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER"
ANALYTIC_LEVEL = "PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION"
REGISTRY = BASE/"round22/previous_artifacts_sha256.json"
REGISTRY_SHA = "875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99"
CLOSED = BASE/"round22/role4/h1_global_numeric/launch_prepare02/actual_attempt01"
SOURCE_MANIFEST_SHA = "914c210931fb8029f59727a58b473402f8ec28c8e3e86328144e350d0fec362f"
FIXED_LIMITS = dict(max_children=1,retry_count=0,max_wall_seconds=10800,
                   max_artifact_bytes=2147483648,expected_vertical_nodes=204800,
                   expected_arch_nodes=12288,expected_arithmetic_integers=999999,
                   catalogue_parameter_change_allowed=False)


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def create_json(path, data):
    with path.open("x", encoding="utf-8", newline="\n") as target:
        json.dump(data, target, indent=2, sort_keys=True)
        target.write("\n")


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def safe_sha(path):
    try:
        return sha(path)
    except BaseException:
        return None


def bytes_used():
    return sum(path.stat().st_size for path in ACTUAL.rglob("*") if path.is_file())


def archives():
    if sha(REGISTRY) != REGISTRY_SHA:
        raise RuntimeError("protected archive registry bytes changed")
    registry = read(REGISTRY)
    if registry["file_count"] != 3089 or len(registry["sha256"]) != 3089:
        raise RuntimeError("protected archive count changed")
    for name, expected in registry["sha256"].items():
        path = (BASE/name).resolve()
        if not path.is_relative_to(BASE.resolve()) or sha(path) != expected:
            raise RuntimeError("protected archive changed:"+name)
    return dict(file_count=3089, unchanged=True, registry_sha256=REGISTRY_SHA)


def inspect_binding(binding):
    path = Path(binding["path"]).resolve()
    try:
        actual = sha(path)
        size = path.stat().st_size
        good = actual == binding["sha256"] and size == binding["bytes"]
        return dict(path=str(path), expected_sha256=binding["sha256"],
                    actual_sha256=actual, bytes=size, unchanged=good)
    except BaseException as error:
        return dict(path=str(path), unchanged=False, error=type(error).__name__+":"+str(error))


def closed_attempt():
    """Integrity only; no old numerical value is used by the evaluator."""
    known={"receipt.json":"2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93",
           "FIN.json":"2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93",
           "PREEXEC.json":"b3734e005f391ddeef49c2342a8775218640c2c0e42e9146077008bb47dda4e3",
           "POSTEXEC.json":"3465bc934e6cab3dd204c3d0f3a939704a392b0beac32f123b081f3c6199eacf",
           "START.json":"7ccb60ee859d294902753afbb0cc939d5f5911d0c1ed7f81a3cef2c488d15683",
           "child_START.json":"119fa6abf5b4783c5fa0f8dec7322eb6aafdc125e2beeebf5eb181902413d730",
           "child_context.json":"902ab13f6ca89da54ca6a5fe41a28896e32d32ea8894c9cfe687ee9d7521cf9b"}
    known["attempt_reservation.json"]="aa506752807f540c48deead34c52a03e938d45315f8d7f39c1f1d692600325a7"
    for name,expected in known.items():
        if sha(CLOSED/name)!=expected:
            raise RuntimeError("closed attempt metadata changed:"+name)
    receipt,pre=read(CLOSED/"receipt.json"),read(CLOSED/"PREEXEC.json")
    if (receipt["resource_failure"]!="MAX_WALL_SECONDS" or receipt["mathematical_children_started"]!=1
            or receipt["retries"]!=0 or len(pre["bindings"])!=1003 or len(pre["captures"])!=1005):
        raise RuntimeError("wrong closed numerical provenance")
    for item in pre["bindings"]:
        path=Path(item["path"])
        if sha(path)!=item["expected_sha256"] or path.stat().st_size!=item["bytes"]:
            raise RuntimeError("closed input changed")
    for item in pre["captures"]:
        path=Path(item["copy"])
        if sha(path)!=item["sha256"] or path.stat().st_size!=item["bytes"]:
            raise RuntimeError("closed capture changed")
        original=Path(item["original"])
        if sha(original)!=item["sha256"] or original.stat().st_size!=item["bytes"]:
            raise RuntimeError("closed capture original/preparation/gate changed")
    for item in receipt["outputs"]:
        if not inspect_binding(item)["unchanged"]:
            raise RuntimeError("closed output changed")
    return dict(bindings=1003,captures=1005,outputs=len(receipt["outputs"]),unchanged=True,
                receipt_sha256=known["receipt.json"],numeric_values_reused=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-authorization", required=True)
    parser.add_argument("--root-authorization-sha256", required=True)
    args = parser.parse_args()
    gate_path = Path(args.root_authorization).resolve()
    if gate_path != GATE.resolve() or sha(gate_path) != args.root_authorization_sha256:
        raise RuntimeError("exact new ROOT global thermal gate/hash required")
    prep_sha = sha(PREPARATION)
    prep, gate = read(PREPARATION), read(gate_path)
    if (prep["schema"] != "ROUND22_GLOBAL_THERMAL_PREPARATION_22" or prep["scope"] != SCOPE or prep["bank_id"] != BANK
            or prep["actor"] != "ROLE6" or prep["metadata_owner"] != "ROLE3"
            or prep["future_evaluation_level"] != EVALUATION_LEVEL
            or prep["analytic_certification_level"] != ANALYTIC_LEVEL
            or prep["structural_PASS_is_enclosure_PASS"] is not False):
        raise RuntimeError("wrong immutable preparation scope")
    if (prep["source_manifest_sha256"]!=SOURCE_MANIFEST_SHA or prep["limits"]!=FIXED_LIMITS
            or prep["source_packet_bindings"]!=21 or prep["runtime_files"]!=972
            or prep["runtime_flags"]!=["-I","-S","-B","-X","utf8"]
            or Path(prep["future_actual_directory"]).resolve()!=ACTUAL.resolve()
            or Path(prep["root_gate_path"]).resolve()!=GATE.resolve()
            or Path(prep["closed_attempt_directory"]).resolve()!=CLOSED.resolve()):
        raise RuntimeError("exact candidate/resources/output/provenance contract changed")
    if (gate.get("status") != "AUTHORIZED" or gate.get("actor") != "ROLE6"
            or gate.get("scope") != SCOPE or gate.get("bank_id") != BANK
            or gate.get("preparation_sha256") != prep_sha or gate.get("bindings") != prep["bindings"]
            or gate.get("limits") != prep["limits"]
            or gate.get("independent_review_receipt_sha256") != prep["independent_review_receipt_sha256"]
            or gate.get("independent_review_report_sha256") != prep["independent_review_report_sha256"]
            or gate.get("independent_domain_addendum_sha256") != prep["independent_domain_addendum_sha256"]
            or gate.get("resource_addendum_sha256") != prep["resource_addendum_sha256"]
            or gate.get("future_evaluation_level") != EVALUATION_LEVEL
            or gate.get("analytic_certification_level") != ANALYTIC_LEVEL
            or gate.get("structural_PASS_is_enclosure_PASS") is not False):
        raise RuntimeError("ROOT has not authorized this exact preparation/review/limits")
    if (prep["limits"]["max_children"] != 1 or prep["limits"]["retry_count"] != 0
            or prep["structural_checker_alone_authorizes_PASS"] is not False
            or prep["enclosure_review_required"] is not True or prep["actual_boxtail_guard_required"] is not True):
        raise RuntimeError("sole-child/no-retry/enclosure boundary changed")
    bindings=prep["bindings"]
    if (len(bindings)!=prep["binding_count"] or len(bindings)<30
            or len({binding["path"].casefold() for binding in bindings})!=len(bindings)
            or sum(binding.get("source_packet") is True for binding in bindings)!=21
            or sorted(binding["path"].casefold() for binding in bindings if binding.get("source_packet") is True)
               !=sorted(path.casefold() for path in prep["source_packet_paths"])
            or sorted(binding["module_alias"] for binding in bindings if binding.get("module_alias"))
               !=sorted(prep["runtime_alias_order"])):
        raise RuntimeError("final exact binding/source/alias counts changed")
    runtime = Path(prep["runtime_path"]).resolve()
    if (Path(sys.executable).resolve() != runtime or not sys.flags.isolated
            or not sys.flags.no_site or sys.flags.utf8_mode != 1 or not sys.dont_write_bytecode):
        raise RuntimeError("canonical Python -I -S -B -X utf8 required")
    metadata_pre_start=utc()
    before = [inspect_binding(binding) for binding in prep["bindings"]]
    if not all(item["unchanged"] for item in before):
        raise RuntimeError("prelaunch source/review/runtime bytes changed")
    before_archives = archives()
    before_closed = closed_attempt()
    ACTUAL.mkdir(exist_ok=False)  # consumes attempt, even before a math child
    token = uuid.uuid4().hex
    create_json(ACTUAL/"attempt_reservation.json", dict(time_utc=utc(),token=token,
                gate_sha256=args.root_authorization_sha256,scope=SCOPE,math_children_started=0))
    stdout, stderr = ACTUAL/"child.stdout.log", ACTUAL/"child.stderr.log"
    process = None
    exit_code = None
    start = None
    control_error = resource_failure = None
    captures = []
    context_sha = None
    monitor_start = time.monotonic()
    try:
        capture_dir = ACTUAL/"PREEXEC"
        capture_dir.mkdir()
        for index,binding in enumerate(prep["bindings"]):
            source = Path(binding["path"]).resolve()
            destination = capture_dir/(f"{index:05d}_"+source.name)
            shutil.copyfile(source,destination)
            if sha(destination) != binding["sha256"] or destination.stat().st_size != binding["bytes"]:
                raise RuntimeError("PREEXEC source byte-copy mismatch")
            captures.append(dict(original=str(source),copy=str(destination),sha256=binding["sha256"],
                                 bytes=binding["bytes"],kind=binding["kind"],module_alias=binding.get("module_alias","")))
        for label,source in (("preparation",PREPARATION),("root_gate",gate_path)):
            destination = capture_dir/(label+".json")
            shutil.copyfile(source,destination)
            if sha(destination) != sha(source):
                raise RuntimeError("PREEXEC preparation/gate copy mismatch")
            captures.append(dict(original=str(source),copy=str(destination),sha256=sha(destination),
                                 bytes=destination.stat().st_size,kind=label,module_alias=""))
        review_copies = [item for item in captures if item["kind"]=="INDEPENDENT_SOURCE_REVIEW_RECEIPT"]
        child_copies = [item for item in captures if item["original"]==str(Path(prep["child_path"]).resolve())]
        if len(review_copies)!=1 or len(child_copies)!=1:
            raise RuntimeError("exact review and child captures required")
        review = read(Path(review_copies[0]["copy"]))
        if (review["status"]!="SOURCE_REVIEW_NUMERICAL_ENCLOSURES_CLOSED" or review["unresolved_blockers"]
                or review["primitive_enclosures_source_audited"] is not True
                or review["analytic_remainders_source_audited"] is not True
                or review["global_h1_formal_proof"] is not False
                or review["source_manifest_sha256"]!=prep["source_manifest_sha256"]
                or review["reviewer_distinct_from_SOURCE_AUTHOR"] is not True
                or review["review_report_sha256"]!=prep["independent_review_report_sha256"]
                or review["domain_addendum_sha256"]!=prep["independent_domain_addendum_sha256"]
                or review["future_evaluation_level"]!=EVALUATION_LEVEL
                or review["analytic_certification_level"]!=ANALYTIC_LEVEL
                or review["structural_checker_is_interval_certificate"] is not False
                or review["structural_PASS_is_enclosure_PASS"] is not False):
            raise RuntimeError("independent numerical enclosure source review not closed")
        if (review["schema"]!="ROUND22_PERFORMANCE_SOURCEPACK02_INDEPENDENT_REVIEW22"
                or review["reviewer"]!="ROLE5" or review["source_author"]!="ROLE3"
                or review["resource_addendum_sha256"]!=prep["resource_addendum_sha256"]
                or not all(review[name] is True for name in
                    ("integer_endpoint_equivalence_source_audited","Gamma_value_projection_source_audited",
                     "fresh_constant_cache_source_audited","launch_tools_source_audited",
                     "resource_addendum_source_audited","same_math_parameters"))):
            raise RuntimeError("candidate equivalence/constant/tool/resource review not closed")
        packet_copies=[item for item in captures if item["kind"]=="SOURCE_MANIFEST"]
        if len(packet_copies)!=1 or sha(Path(packet_copies[0]["copy"]))!=SOURCE_MANIFEST_SHA:
            raise RuntimeError("exact candidate manifest capture missing")
        source_packet=read(Path(packet_copies[0]["copy"]))
        source_entries=source_packet["core_bindings"]+source_packet["support_bindings"]
        if (len(source_entries)!=21 or sorted(item["path"].casefold() for item in source_entries)
                !=sorted(path.casefold() for path in prep["source_packet_paths"])):
            raise RuntimeError("21 exact source-manifest paths changed")
        by_original={item["original"].casefold():item for item in captures}
        for item in source_entries+review["tool_bindings"]:
            captured=by_original.get(str(Path(item["path"]).resolve()).casefold())
            if captured is None or captured["sha256"]!=item["sha256"] or captured["bytes"]!=item["bytes"]:
                raise RuntimeError("candidate/review-tool exact captured bytes missing")
        context = dict(schema="ROUND22_GLOBAL_THERMAL_CHILD_CONTEXT_22",token=token,
                       scope=SCOPE,bank_id=BANK,actual_directory=str(ACTUAL),
                       actor="ROLE6",metadata_owner="ROLE3",future_evaluation_level=EVALUATION_LEVEL,
                       analytic_certification_level=ANALYTIC_LEVEL,structural_PASS_is_enclosure_PASS=False,
                       data_directory=str(ACTUAL/"numeric_data"),captures=captures,
                       runtime_path=str(runtime),limits=prep["limits"],
                       runtime_alias_order=prep["runtime_alias_order"],
                       source_manifest_sha256=prep["source_manifest_sha256"],
                       independent_review_receipt_sha256=prep["independent_review_receipt_sha256"],
                       independent_review_report_sha256=prep["independent_review_report_sha256"],
                       independent_domain_addendum_sha256=prep["independent_domain_addendum_sha256"],
                       resource_addendum_sha256=prep["resource_addendum_sha256"],
                       preparation_sha256=prep_sha,root_gate_sha256=args.root_authorization_sha256)
        context_path = ACTUAL/"child_context.json"
        create_json(context_path,context)
        context_sha=sha(context_path)
        create_json(ACTUAL/"PREEXEC.json",dict(time_utc=utc(),metadata_pre_start=metadata_pre_start,captures=captures,bindings=before,
                    archives=before_archives,context_sha256=context_sha,token=token,
                    closed_attempt=before_closed,
                    math_children_started=0,all_captures_verified=True))
        if bytes_used()>prep["limits"]["max_artifact_bytes"]:
            raise RuntimeError("resource byte budget exceeded before math START")
        command = [str(runtime),"-I","-S","-B","-X","utf8",child_copies[0]["copy"],
                   "--context",str(context_path),"--context-sha256",context_sha]
        start = utc()
        create_json(ACTUAL/"START.json",dict(time_utc=start,token=token,command=command,
                    max_children=1,no_retry=True,PREEXEC_complete=True,context_sha256=context_sha))
        print(json.dumps(dict(actual_START=start,token=token,command=command),sort_keys=True),flush=True)
        with stdout.open("xb") as out, stderr.open("xb") as err:
            flags = subprocess.CREATE_NO_WINDOW if os.name=="nt" else 0
            process = subprocess.Popen(command,cwd=str(ACTUAL),stdout=out,stderr=err,creationflags=flags)
            monitor_start = time.monotonic()
            while True:
                remaining = prep["limits"]["max_wall_seconds"]-(time.monotonic()-monitor_start)
                if remaining<=0:
                    resource_failure="MAX_WALL_SECONDS"
                    break
                if bytes_used()>prep["limits"]["max_artifact_bytes"]:
                    resource_failure="MAX_ARTIFACT_BYTES"
                    break
                try:
                    exit_code=process.wait(timeout=min(5,remaining))
                    break
                except subprocess.TimeoutExpired:
                    pass
            if resource_failure:
                process.kill()
                exit_code=process.wait(timeout=30)
    except BaseException as error:
        control_error=type(error).__name__+":"+str(error)
        if process is not None and process.poll() is None:
            process.kill()
            try:
                exit_code=process.wait(timeout=30)
            except BaseException as stop_error:
                control_error+=";stop:"+type(stop_error).__name__+":"+str(stop_error)
    finish=utc()
    after=[inspect_binding(binding) for binding in prep["bindings"]]
    capture_integrity=[]
    for item in captures:
        copy_binding=dict(path=item["copy"],sha256=item["sha256"],bytes=item["bytes"])
        capture_integrity.append(inspect_binding(copy_binding))
    archive_error=None
    try:
        after_archives=archives()
    except BaseException as error:
        after_archives=dict(unchanged=False,file_count=3089)
        archive_error=type(error).__name__+":"+str(error)
    closed_error=None
    try:
        after_closed=closed_attempt()
    except BaseException as error:
        after_closed=dict(unchanged=False)
        closed_error=type(error).__name__+":"+str(error)
    prep_intact=safe_sha(PREPARATION)==prep_sha
    gate_intact=safe_sha(gate_path)==args.root_authorization_sha256
    intact=(all(item["unchanged"] for item in after) and all(item["unchanged"] for item in capture_integrity)
            and after_archives["unchanged"] and after_closed["unchanged"] and prep_intact and gate_intact)
    child_fin_path=ACTUAL/"child_FIN.json"
    child_fin=None
    if child_fin_path.exists():
        try:
            child_fin=read(child_fin_path)
        except BaseException as error:
            control_error=(control_error or "")+";child_FIN:"+type(error).__name__+":"+str(error)
    context_intact=context_sha is not None and safe_sha(ACTUAL/"child_context.json")==context_sha
    success=(exit_code==0 and control_error is None and resource_failure is None and intact and context_intact
             and isinstance(child_fin,dict) and child_fin.get("status")=="NUMERICAL_AGREEMENT_PENDING_POSTCHECK"
             and child_fin.get("token")==token and child_fin.get("actual_all_guard_checks") is True
             and child_fin.get("structural_checker_PASS") is True
             and child_fin.get("independent_enclosure_source_review_bound") is True
             and child_fin.get("future_evaluation_level")==EVALUATION_LEVEL
             and child_fin.get("analytic_certification_level")==ANALYTIC_LEVEL
             and child_fin.get("structural_PASS_is_enclosure_PASS") is False
             and bytes_used()<=prep["limits"]["max_artifact_bytes"])
    postcheck_finish=utc()
    create_json(ACTUAL/"POSTEXEC.json",dict(time_utc=postcheck_finish,metadata_post_start=finish,bindings=after,captures=capture_integrity,
                archives=after_archives,archive_error=archive_error,all_intact=intact,
                closed_attempt=after_closed,closed_attempt_error=closed_error,
                preparation_intact=prep_intact,root_gate_intact=gate_intact,context_intact=context_intact))
    output_paths=[ACTUAL/"numeric_data/global_thermal_result.json",ACTUAL/"numeric_data/structural_checker_result.json",
                  ACTUAL/"numeric_data/new_nodes.ndjson",ACTUAL/"numeric_data/new_arithmetic.ndjson",stdout,stderr,child_fin_path]
    outputs=[]
    output_errors=[]
    for path in output_paths:
        if path.exists():
            try:
                outputs.append(dict(path=str(path),sha256=sha(path),bytes=path.stat().st_size))
            except BaseException as error:
                output_errors.append(dict(path=str(path),error=type(error).__name__+":"+str(error)))
    if output_errors:
        success=False
    # Reserve two1MiB closure receipts AFTER the potentially large POST log.
    # This is a declared controller bound, not an estimate of mathematical work.
    if bytes_used()+2097152>prep["limits"]["max_artifact_bytes"]:
        resource_failure=resource_failure or "MAX_ARTIFACT_BYTES_CLOSURE_RESERVE"
        success=False
    status="THERMAL_TRACE_NUMERICAL_AUX_PASS_SOURCE_AUDITED" if success else "GLOBAL_THERMAL_ATTEMPT_FAIL"
    receipt=dict(schema="ROUND22_GLOBAL_THERMAL_ACTUAL_RECEIPT_22",scope=SCOPE,bank_id=BANK,status=status,
                 actor="ROLE6",metadata_owner="ROLE3",future_evaluation_level=EVALUATION_LEVEL,
                 analytic_certification_level=ANALYTIC_LEVEL,structural_PASS_is_enclosure_PASS=False,
                 structural_checker_alone_is_primitive_certificate=False,
                 token=token,actual_START=start,actual_FINISH=utc(),child_process_FINISH=finish,
                 metadata_pre_start=metadata_pre_start,postcheck_finish=postcheck_finish,child_exit_code=exit_code,
                 mathematical_children_started=1 if process is not None else 0,control_error=control_error,
                 resource_failure=resource_failure,post_integrity=intact,outputs=outputs,output_errors=output_errors,
                 preparation_sha256=prep_sha,root_gate_sha256=args.root_authorization_sha256,
                 independent_review_receipt_sha256=prep["independent_review_receipt_sha256"],
                 independent_review_report_sha256=prep["independent_review_report_sha256"],
                 independent_domain_addendum_sha256=prep["independent_domain_addendum_sha256"],
                 resource_addendum_sha256=prep["resource_addendum_sha256"],
                 closed_attempt_integrity=after_closed["unchanged"],
                 resource_limits=prep["limits"],artifact_bytes_observed=bytes_used(),
                 cost_previously_measured=False,retries=0,old_bank_replays=0,Lean_invocations=0,
                 horizontal_volet="UNIMPLEMENTED",formal_H1="OPEN",coefficient_N="OPEN",D_N="UNPAID",WIN=False)
    if len((json.dumps(receipt,indent=2,sort_keys=True)+"\n").encode("utf-8"))>1048576:
        raise RuntimeError("controller receipt exceeds declared1MiB limit; no PASS")
    create_json(ACTUAL/"FIN.json",receipt)
    create_json(ACTUAL/"receipt.json",receipt)
    print(json.dumps(receipt,sort_keys=True),flush=True)
    return 0 if success else 1


if __name__=="__main__":
    raise SystemExit(main())
