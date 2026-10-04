"""DRAFT SOURCE for the sole future numerical child; no invocation authorized.

Only standard-library imports occur before the byte-bound context is checked.
Nine reviewed source modules are compiled from their PREEXEC captured bytes,
under exact aliases, in dependency order. PYTHONPATH/site/user startup is unused.
The structural checker remains independent of mathematical evaluator imports;
it does not by itself certify primitives, remainders, or the H1 identity.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time
import traceback
from types import ModuleType

EVALUATION_LEVEL = "PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER"
ANALYTIC_LEVEL = "PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION"

def utc():
    return datetime.now(timezone.utc).isoformat()


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def create_json(path, data):
    with path.open("x",encoding="utf-8",newline="\n") as target:
        json.dump(data,target,indent=2,sort_keys=True)
        target.write("\n")


def artifact_bytes(actual):
    return sum(path.stat().st_size for path in actual.rglob("*") if path.is_file())


def load_captured_module(alias, binding):
    if alias in sys.modules:
        raise RuntimeError("runtime alias already imported:"+alias)
    path=Path(binding["copy"])
    source=path.read_bytes()
    if len(source)!=binding["bytes"] or sha_bytes(source)!=binding["sha256"]:
        raise RuntimeError("captured runtime source byte mismatch:"+alias)
    # Compilation/import is ONLY inside this authorized mathematical child.
    # Using the just-hashed byte buffer avoids a second source read race.
    module=ModuleType(alias)
    module.__file__=str(path)
    module.__package__=""
    sys.modules[alias]=module
    try:
        exec(compile(source,str(path),"exec"),module.__dict__)
    except BaseException:
        del sys.modules[alias]
        raise
    return module


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--context",required=True)
    parser.add_argument("--context-sha256",required=True)
    args=parser.parse_args()
    context_path=Path(args.context).resolve()
    context_bytes=context_path.read_bytes()
    if sha_bytes(context_bytes)!=args.context_sha256:
        raise RuntimeError("immutable child context changed")
    context=json.loads(context_bytes)
    if context["schema"]!="ROUND22_GLOBAL_THERMAL_CHILD_CONTEXT_22" or context["scope"]!="ROUND22_GLOBAL_THERMAL_H1_NUMERIC_ONLY":
        raise RuntimeError("wrong global thermal scope")
    if (context["bank_id"]!="THERMAL_GLOBAL_H1_22_SOURCEPACK02"
            or context["source_manifest_sha256"]!="914c210931fb8029f59727a58b473402f8ec28c8e3e86328144e350d0fec362f"):
        raise RuntimeError("exact distinct performance source bank required")
    if (context["actor"]!="ROLE6" or context["metadata_owner"]!="ROLE3"
            or context["future_evaluation_level"]!=EVALUATION_LEVEL
            or context["analytic_certification_level"]!=ANALYTIC_LEVEL
            or context["structural_PASS_is_enclosure_PASS"] is not False):
        raise RuntimeError("wrong paper-audited interval execution level")
    actual=Path(context["actual_directory"]).resolve()
    data=Path(context["data_directory"]).resolve()
    if context_path.parent!=actual or data!=actual/"numeric_data":
        raise RuntimeError("child outputs outside exact reserved attempt")
    if Path(sys.executable).resolve()!=Path(context["runtime_path"]).resolve() or not sys.flags.isolated or not sys.flags.no_site or not sys.dont_write_bytecode or sys.flags.utf8_mode!=1:
        raise RuntimeError("canonical isolated Python -I -S -B -X utf8 required")
    token=context["token"]
    limits=context["limits"]
    if limits["max_children"]!=1 or limits["retry_count"]!=0 or limits["catalogue_parameter_change_allowed"] is not False:
        raise RuntimeError("one-child/no-retry/fixed-catalogue contract invalid")
    if limits["max_wall_seconds"]!=10800 or limits["max_artifact_bytes"]!=2147483648:
        raise RuntimeError("exact future reviewed10800s/2GiB resources required")
    if (limits["expected_vertical_nodes"],limits["expected_arch_nodes"],limits["expected_arithmetic_integers"])!=(204800,12288,999999):
        raise RuntimeError("thermal source catalogue changed")
    start=utc()
    monitor_start=time.monotonic()
    create_json(actual/"child_START.json",dict(time_utc=start,token=token,
                context_sha256=args.context_sha256,source_imports_started=0))
    print(json.dumps(dict(child_START=start,token=token,scope=context["scope"]),sort_keys=True),flush=True)
    result=checker=None
    control_error=None
    status="CHILD_SOURCE_ERROR"
    exit_code=1
    loaded=[]
    review_bound=False
    try:
        alias_order=["dyadic_r01","analytic_r01","kernel_r01","unit_transport_source22",
                     "arithmetic_catalogue_source22","transport_catalogue_source22",
                     "envelopes_source22","producer_source22","structural_checker_source22"]
        if context["runtime_alias_order"]!=alias_order:
            raise RuntimeError("exact9alias dependency order required")
        capture_aliases={}
        for item in context["captures"]:
            alias=item.get("module_alias","")
            if alias:
                if alias in capture_aliases:
                    raise RuntimeError("duplicate runtime alias")
                capture_aliases[alias]=item
        if set(capture_aliases)!=set(alias_order):
            raise RuntimeError("exact9runtime aliases required")
        reviews=[item for item in context["captures"] if item["kind"]=="INDEPENDENT_SOURCE_REVIEW_RECEIPT"]
        if len(reviews)!=1:
            raise RuntimeError("single actual independent source review required")
        review_bytes=Path(reviews[0]["copy"]).read_bytes()
        if sha_bytes(review_bytes)!=context["independent_review_receipt_sha256"]:
            raise RuntimeError("independent review receipt changed")
        review=json.loads(review_bytes)
        review_bound=(review["status"]=="SOURCE_REVIEW_NUMERICAL_ENCLOSURES_CLOSED"
                      and review["schema"]=="ROUND22_PERFORMANCE_SOURCEPACK02_INDEPENDENT_REVIEW22"
                      and review["reviewer"]=="ROLE5" and review["source_author"]=="ROLE3"
                      and not review["unresolved_blockers"]
                      and review["primitive_enclosures_source_audited"] is True
                      and review["analytic_remainders_source_audited"] is True
                      and review["global_h1_formal_proof"] is False
                      and review["reviewer_distinct_from_SOURCE_AUTHOR"] is True
                      and review["source_manifest_sha256"]==context["source_manifest_sha256"]
                      and review["review_report_sha256"]==context["independent_review_report_sha256"]
                      and review["domain_addendum_sha256"]==context["independent_domain_addendum_sha256"]
                      and review["future_evaluation_level"]==EVALUATION_LEVEL
                      and review["analytic_certification_level"]==ANALYTIC_LEVEL
                      and review["structural_checker_is_interval_certificate"] is False
                      and review["structural_PASS_is_enclosure_PASS"] is False)
        review_bound=(review_bound
                      and review["resource_addendum_sha256"]==context["resource_addendum_sha256"]
                      and all(review[name] is True for name in
                          ("integer_endpoint_equivalence_source_audited","Gamma_value_projection_source_audited",
                           "fresh_constant_cache_source_audited","launch_tools_source_audited",
                           "resource_addendum_source_audited","same_math_parameters")))
        if not review_bound:
            raise RuntimeError("numerical enclosure source review not concretely bound/closed")
        for alias in alias_order:
            load_captured_module(alias,capture_aliases[alias])
            loaded.append(alias)
        data.mkdir(exist_ok=False)
        def progress(record):
            elapsed=time.monotonic()-monitor_start
            size=artifact_bytes(actual)
            if elapsed>limits["max_wall_seconds"]:
                raise RuntimeError("MAX_WALL_SECONDS at actual progress checkpoint")
            if size>limits["max_artifact_bytes"]:
                raise RuntimeError("MAX_ARTIFACT_BYTES at actual progress checkpoint")
            print(json.dumps(dict(time_utc=utc(),elapsed_ms=int(1000*elapsed),artifact_bytes=size,
                                  progress=record),sort_keys=True),flush=True)
        producer=sys.modules["producer_source22"]
        result=producer.new_global_thermal_source(data,progress)
        checker=sys.modules["structural_checker_source22"].verify_global_source(data)
        create_json(data/"structural_checker_result.json",checker)
        if result["status"]!="THERMAL_TRACE_NUMERIC_AGREEMENT" or checker["numerical_decision"]!=result["status"] or checker["structural_checker_PASS"] is not True:
            status="CHILD_NUMERICAL_DISAGREEMENT_OR_NONINFORMATIVE"
            exit_code=2
        elif (result["WIN"] is not False or result["H1_FORMAL"]!="OPEN" or result["COEFFICIENT_N"]!="OPEN"
              or result["D_N"]!="UNPAID" or result["CONTOUR_BOUNDARY"]!="UNIMPLEMENTED"
              or checker["primitives_recomputed"] is not False):
            raise RuntimeError("unpaid formal/horizontal/primitive scope promoted")
        elif (result["performance_source_packet"]!="SOURCEPACK02_EXACT_ENDPOINTS_AND_ENVELOPES"
              or result["performance_counts"]!=dict(half_log_two_pi_constructions=1,
                   f1_constructions=1,gamma_value_only=204800)
              or checker["performance_source_guards_verified"] is not True):
            raise RuntimeError("performance source identity/counter guards not actually paid")
        else:
            # Producer rejects any actual nodal, divisor, weight, sum, constant
            # or total-envelope guard failure; checker independently refolds
            # those emitted boxes/budgets and decides all mandatory mutants.
            status="NUMERICAL_AGREEMENT_PENDING_POSTCHECK"
            exit_code=0
        progress(dict(volet="closed_global_comparison",numerical_status=result["status"],
                      structural_checker_PASS=checker["structural_checker_PASS"]))
    except BaseException as error:
        control_error=type(error).__name__+":"+str(error)
        status="CHILD_SOURCE_OR_GUARD_ERROR"
        exit_code=1
        traceback.print_exc(file=sys.stderr)
    finish=utc()
    receipt=dict(schema="ROUND22_GLOBAL_THERMAL_CHILD_FIN_22",token=token,status=status,
                 actor="ROLE6",metadata_owner="ROLE3",future_evaluation_level=EVALUATION_LEVEL,
                 analytic_certification_level=ANALYTIC_LEVEL,structural_PASS_is_enclosure_PASS=False,
                 actual_START=start,actual_FINISH=finish,exit_code=exit_code,control_error=control_error,
                 loaded_runtime_aliases=loaded,independent_enclosure_source_review_bound=review_bound,
                 actual_all_guard_checks=(exit_code==0),
                 structural_checker_PASS=checker is not None and checker["structural_checker_PASS"] is True,
                 structural_checker_alone_is_primitive_certificate=False,
                 context_sha256=args.context_sha256,artifact_bytes=artifact_bytes(actual),
                 mathematical_children=1,retries=0,old_bank_replays=0,Lean_invocations=0,
                 horizontal_volet="UNIMPLEMENTED",formal_H1="OPEN",coefficient_N="OPEN",D_N="UNPAID",WIN=False)
    create_json(actual/"child_FIN.json",receipt)
    print(json.dumps(receipt,sort_keys=True),flush=True)
    return exit_code


if __name__=="__main__":
    raise SystemExit(main())
