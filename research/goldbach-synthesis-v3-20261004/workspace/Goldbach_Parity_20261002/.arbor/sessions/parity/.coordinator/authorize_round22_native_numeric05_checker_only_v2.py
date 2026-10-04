"""ROOT metadata gate only; no candidate import or numerical evaluation."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
P = B / "round22/role3/native_numeric_checker_only_consumer_source05_revision02"
M = P / "metadata_source05"
R = B / "round22/role4/native_numeric05_checker_only_consumer_review_source02"
OLD = B / "round22/role3/native_numeric_consumer_source01"
OLD_ACTUAL = OLD / "actual_numeric04_attempt01"
OLD_CLOSURE = B / "round22/role3/native_numeric_closure_source01"

def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            h.update(block)
    return h.hexdigest()

def read(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def key(path):
    return str(Path(path).resolve()).casefold()

def check(path, digest, size=None):
    assert path.is_file() and sha(path) == digest, str(path)
    assert size is None or path.stat().st_size == size, str(path)

def main():
    parser = argparse.ArgumentParser()
    for name in ("prep-sha", "manifest-sha", "metadata-receipt-sha", "metadata-reads-sha",
                 "conservation-sha", "review-sha", "trust-sha", "ROOT-full-reads"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--prior-modules", required=True, type=int)
    parser.add_argument("--prior-declarations", required=True, type=int)
    args = parser.parse_args()
    fixed = dict(scope="NATIVE_NUMERIC05_CHECKER_ONLY_N1E8", fixed_N=100000000,
        fixed_M=100000000, fixed_K=134217728, fixed_S="288230376151711744",
        max_children=1, max_retries=0, wall_seconds=3600,
        checker_deadline_parent_offset_seconds=3300, FIN_POST_reserve_seconds=300, last_parent_deadline_check_before_backend=True, expired_at_last_parent_deadline_check_creates_no_child=True, backend_checks_deadline_before_resume=True, atomic_OS_CreateProcess_deadline_guarantee=False,
        output_bytes=2147483648, commit_job_bytes=2147483648,
        rss_per_process_monitor_bytes=2147483648, sampled_job_rss_cap_bytes=4294967296,
        max_active_job_processes=16, max_total_job_processes=32,
        job_limit_flags_requested=8968, working_set_limit_flag_requested=False,
        rss_os_enforced=False, rss_control="SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM",
        log_bytes=1048576, metadata_bytes=16777216, capture_bytes=33554432,
        compiler_invocations=0, producer_invocations=0)
    locked = {
        P / "run_native05_checker_only_once22.py": "c1e116f0467aa0d9a5e54c80f8db560887379ce82bf4dee825ec63531421d7b1",
        P / "prepare_native05_checker_only_metadata22.ps1": "0dedf40be1d10b39f8e7d44b7826d55de4bf634d0872a187f6524a4dfb33e57f",
        P / "numeric_checker_only_execution_plan22.json": "e39443a771e40829aee31dab2662d26026fe0d59e85ac8b4c42197b118fcc844",
        P / "numeric_checker_only_trust_policy22.json": "2da30d086338b3801f4ecc234eedf99b7afa563d94357c07a461740ea52ace9b",
        P / "source_contract22.txt": "b992f9aab48c3741445266828a3ea461dd5976c86f3ae3cd9051ea05105071bb",
        P / "read_receipts22.json": "65e84cea034fb9e3815711ba16eb4d178568bac755aa234703094ce89bfccc54",
        P / "source_handoff22.json": "9b721db7eff5bd27936be11937350f9811f8c7c2f0126eab066e57b6647478cf",
        OLD / "numeric_manifest22.json": "43d746dee55a02c6fc49032be240badf315e9525d67e12fe05a0d6c52cb5bcad",
        C / "messages/round22_native_numeric04_authorization.json": "b5dc57f1afa98304645f9e62505026c805c7a536946a15eedec399922aeba932",
        OLD_ACTUAL / "PRE.json": "2263e2fa6b54445a31ac910e213a417b07cee7468c103726f12f8736e46d1d6d",
        OLD_CLOSURE / "numeric_execution_closure22.json": "a99a5e58768d09a16c7a1ae248448be41016cac228fc57c69372d6abb2774df3",
        OLD_CLOSURE / "closure_evidence_bindings22.json": "ad229461cba2a9b411801c024e443148b9ba2673508107e868a173b42c0ea184",
        OLD_CLOSURE / "quiescence_evidence22.json": "2763645031ab61fdbeae88a8cd5d699d4a11b60381f132dd8e5c5da2ba94402a",
        C / "messages/round22_native_numeric04_closed_observation.json": "9097721eee09dea1c30c73a2285713b5a72f98c754781b40d8ab8c977d2f75a3",
        OLD_ACTUAL / "producer_FIN.json": "fdbb8187fb1ab37ac19d301d0b475da3ee9e48df004732bd60d930905280a520",
        OLD_ACTUAL / "producer_payload_hashes.json": "470441f9e6af30a1be7c4c27999c6498ef6b66509521abdb4ac5cb1a2229d50e",
        OLD_ACTUAL / "WATCHDOG_TERMINATION_REQUEST.json": "cd559e4e5a3355639dfe3d46d358537ee3ee9984d29206efa1781fc7f7e1f706",
        B / "round22/role4/native_numeric05_checker_only_contract_source02/checker_only_contract22.md": "ea1273af14d4c020aae5f2bb5462b89924e3ba3f0419460a50a2962288c270fb",
        R / "source_review22.json": args.review_sha,
        R / "trust_review22.json": args.trust_sha,
    }
    for path, digest in locked.items():
        check(path, digest)
    prep_path = P / "numeric_checker_only_preparation22.json"
    manifest_path = P / "numeric_checker_only_manifest22.json"
    controls = [(prep_path, args.prep_sha), (manifest_path, args.manifest_sha),
        (M / "metadata_execution_receipt22.json", args.metadata_receipt_sha),
        (P / "prepare_native05_checker_only_metadata22.ps1", locked[P / "prepare_native05_checker_only_metadata22.ps1"]),
        (M / "metadata_read_receipts22.json", args.metadata_reads_sha)]
    for path, digest in controls + [(M / "metadata_conservation22.json", args.conservation_sha)]:
        check(path, digest)
    check(M / "numeric_checker_only_manifest22.json", args.manifest_sha)
    check(M / "numeric_checker_only_preparation22.json", args.prep_sha)
    prep, manifest = read(prep_path), read(manifest_path)
    plan = read(P / "numeric_checker_only_execution_plan22.json")
    assert prep["status"] == "NATIVE_NUMERIC05_CHECKER_ONLY_METADATA_PREPARED"
    for name, value in fixed.items():
        assert type(prep[name]) is type(value) and prep[name] == value, name
        assert type(plan[name]) is type(value) and plan[name] == value, name
    assert key(prep["manifest_path"]) == key(manifest_path) and prep["manifest_sha256"] == args.manifest_sha
    assert prep["parent_sha256"] == locked[P / "run_native05_checker_only_once22.py"]
    assert prep["source_handoff_sha256"] == locked[P / "source_handoff22.json"]
    assert prep["numeric_execution_plan_sha256"] == locked[P / "numeric_checker_only_execution_plan22.json"]
    assert prep["numeric_trust_policy_sha256"] == locked[P / "numeric_checker_only_trust_policy22.json"]
    assert prep["payload_bytes_mathematically_validated"] is False and prep["numeric_authorization"] is False
    review, trust = read(R / "source_review22.json"), read(R / "trust_review22.json")
    assert review["status"] == "NUMERIC05_CHECKER_ONLY_SOURCE_REVIEW_CLOSED_WITH_NATIVE_REFINEMENT_OPEN"
    assert trust["status"] == "NUMERIC05_CHECKER_ONLY_FIXED_IMAGE_REVIEWED_WITH_EXPLICIT_WINDOWS_NATIVE_TRUST"
    for doc in (review, trust):
        assert doc["reviewer"] == "ROLE4" and doc["scope"] == fixed["scope"]
        assert doc["unresolved_execution_blockers"] == []
        assert doc["numeric_authorization"] is False and doc["produced_binary_invocations"] == 0
        for name in ("job_limit_flags_requested", "working_set_limit_flag_requested", "rss_os_enforced", "rss_control",
                     "wall_seconds", "checker_deadline_parent_offset_seconds", "FIN_POST_reserve_seconds", "last_parent_deadline_check_before_backend", "expired_at_last_parent_deadline_check_creates_no_child", "backend_checks_deadline_before_resume", "atomic_OS_CreateProcess_deadline_guarantee"):
            assert type(doc[name]) is type(fixed[name]) and doc[name] == fixed[name], name
    assert review["parent_sha256"] == locked[P / "run_native05_checker_only_once22.py"]
    assert review["source_handoff_sha256"] == locked[P / "source_handoff22.json"]
    assert review["old04_producer_payloads_mathematically_validated"] is False
    assert trust["policy_sha256"] == locked[P / "numeric_checker_only_trust_policy22.json"]
    assert trust["installed_Windows_and_frozen_native_runtime_trusted"] is True
    for name in ("effective_loads_observed", "universal_loader_closure_verified", "all_non_OS_imports_bound"):
        assert trust[name] is False
    checker_sha = "2e7e095c2972fea09ee26500df9dae207ff52497d0f61f2052d76d464ebe6990"
    backend_sha = "88d857ce33eece8f90906bc5088d5cac905b868e60ede1b6439b1a3af3126cc3"
    build_receipt_sha = "04ce22f9ee05215ee9c7c335b41755b1da4e001a82fa20085cfe7dccca1a7fc8"
    assert trust["checker_binary_sha256"] == checker_sha and trust["backend_sha256"] == backend_sha
    assert prep["checker_binary_sha256"] == checker_sha and prep["build_receipt_sha256"] == build_receipt_sha
    expected = {}
    def add(path, digest, size=None, capture=False):
        path = Path(path)
        size = path.stat().st_size if size is None else size
        k = key(path)
        old = expected.get(k)
        assert old is None or (old["sha256"], old["bytes"]) == (digest, size), str(path)
        expected[k] = dict(path=str(path), sha256=digest, bytes=size,
            capture=capture or (old is not None and old["capture"]))
    links = [path for path in locked if path in (OLD / "numeric_manifest22.json", OLD_ACTUAL / "PRE.json")
        or path.is_relative_to(OLD_CLOSURE) or path.is_relative_to(OLD_ACTUAL)
        or path.name in ("round22_native_numeric04_authorization.json", "round22_native_numeric04_closed_observation.json", "checker_only_contract22.md")]
    assert len(links) == 11
    for path in links:
        add(path, locked[path], capture=True)
    old_manifest = read(OLD / "numeric_manifest22.json")
    assert old_manifest["binding_count"] == len(old_manifest["bindings"]) == 6456
    for row in old_manifest["bindings"]:
        add(row["path"], row["sha256"], row["bytes"], row.get("capture", False))
    closed = read(OLD_CLOSURE / "numeric_execution_closure22.json")
    assert closed["status"] == "CLOSED_STOP_NO_MATHEMATICAL_VERDICT" and closed["parent_exit_code"] == 1
    assert len(closed["output_bindings"]) == 83
    for row in closed["output_bindings"]:
        add(row["path"], row["sha256"], row["bytes"])
    captures = read(OLD_ACTUAL / "PRE.json")["captures"]
    assert len(captures) == 66
    for row in captures:
        add(row["original"], row["sha256"], capture=True)
        add(row["copy"], row["sha256"])
    old_controls = read(C / "messages/round22_native_numeric04_authorization.json")["metadata_control_bindings"]
    assert len(old_controls) == 5
    for row in old_controls:
        add(row["path"], row["sha256"], capture=True)
    handoff = read(P / "source_handoff22.json")
    assert handoff["binding_count"] == len(handoff["bindings"]) == 57
    for row in handoff["bindings"]:
        add(row["path"], row["sha256"], row["bytes"], row.get("capture", False))
    for path in (P / "source_handoff22.json", R / "source_review22.json", R / "trust_review22.json"):
        add(path, locked[path], capture=True)
    rows = manifest["bindings"]
    observed = {key(row["path"]): row for row in rows}
    assert len(rows) == len(observed) == len(expected) == prep["binding_count"]
    assert observed.keys() == expected.keys()
    for k, row in expected.items():
        got = observed[k]
        assert (got["sha256"], got["bytes"]) == (row["sha256"], row["bytes"])
        assert not row["capture"] or got.get("capture", False)
        check(Path(got["path"]), got["sha256"], got["bytes"])
    assert {key(p) for p in OLD_ACTUAL.rglob("*") if p.is_file()} == {key(row["path"]) for row in closed["output_bindings"]}
    for name in ("receipt.json", "POST.json", "checker_FIN.json", "coefficient_result.json"):
        assert not (OLD_ACTUAL / name).exists()
    registry_path = B / "round22/previous_artifacts_sha256.json"
    check(registry_path, "875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99")
    registry = read(registry_path)["sha256"]
    assert len(registry) == 3089
    for relative, digest in registry.items():
        path = (B / relative).resolve()
        assert path.is_relative_to(B.resolve())
        check(path, digest)
    conservation = read(M / "metadata_conservation22.json")
    receipt = read(M / "metadata_execution_receipt22.json")
    assert conservation["all_inputs_intact"] is True and conservation["binding_count"] == len(rows)
    assert receipt["status"] == prep["status"] and receipt["preparation_sha256"] == args.prep_sha and receipt["manifest_sha256"] == args.manifest_sha
    assert receipt["conservation_sha256"] == args.conservation_sha and receipt["reads_sha256"] == args.metadata_reads_sha
    assert receipt["numeric_calls"] == receipt["compiler_calls"] == 0 and receipt["retry_count"] == 0
    assert not (P / "actual_numeric05_checker_only_attempt01").exists()
    cp = read(C / "checkpoint.json")["official_auxiliary_validation"]
    assert (cp["modules"], cp["declarations"]) == (args.prior_modules, args.prior_declarations)
    gate = dict(fixed, schema="ROUND22_ROOT_NATIVE_NUMERIC05_CHECKER_ONLY_AUTHORIZATION", status="AUTHORIZED",
        utc=datetime.now(timezone.utc).isoformat(), actor="ROLE6", attempt="actual_numeric05_checker_only_attempt01",
        preparation_sha256=args.prep_sha, manifest_sha256=args.manifest_sha,
        source_handoff_sha256=locked[P / "source_handoff22.json"],
        numeric_execution_plan_sha256=locked[P / "numeric_checker_only_execution_plan22.json"],
        numeric_trust_policy_sha256=locked[P / "numeric_checker_only_trust_policy22.json"],
        checker_binary_sha256=checker_sha, build_receipt_sha256=build_receipt_sha,
        old04_external_closure_sha256=locked[OLD_CLOSURE / "numeric_execution_closure22.json"],
        independent_numeric_source_review_path=str(R / "source_review22.json"), independent_numeric_source_review_sha256=args.review_sha,
        numeric_trust_review_path=str(R / "trust_review22.json"), numeric_trust_review_sha256=args.trust_sha,
        accept_installed_Windows_and_frozen_native_runtime_trust=True, reuse_unvalidated_producer04_payload_bytes=True,
        metadata_control_bindings=[dict(path=str(path), sha256=digest) for path, digest in controls],
        ROOT_full_reads=args.ROOT_full_reads, inputs_verified=len(rows), archives_verified=3089,
        official_modules=args.prior_modules, official_auxiliary_declarations=args.prior_declarations,
        ROOT_compiler_invocations=0, ROOT_numeric_invocations=0,
        effective_loads_observed=False, universal_loader_closure_verified=False, all_non_OS_imports_bound=False,
        native_Lean_refinement=False, D_N=False, WIN=False)
    gate_path = C / "messages/round22_native_numeric05_checker_only_authorization.json"
    with gate_path.open("x", encoding="utf-8") as stream:
        json.dump(gate, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    print(json.dumps(dict(gate=str(gate_path), gate_sha256=sha(gate_path), inputs=len(rows), archives=3089,
        max_native_checker_children=1, producer=0, compiler=0, retry=0, ROOT_numeric=0, WIN=False)))

if __name__ == "__main__":
    main()
