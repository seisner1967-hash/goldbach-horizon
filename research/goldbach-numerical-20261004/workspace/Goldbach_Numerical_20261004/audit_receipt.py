"""Independent exact arithmetic audit of the complete native run outputs."""

import argparse
from decimal import Decimal, localcontext
import hashlib
import json
from pathlib import Path
import re
import struct
import sys


N = 100000000
K = 1 << 27
S = 1 << 58
PRIMES = (2013265921, 2281701377, 3221225473, 3489660929, 3892314113)
COFACTORS = (15, 17, 24, 26, 29)
BASES = (31, 3, 5, 3, 3)
PRODUCER_BINARY_SHA256 = "44d2d571a0190f7dbbb975225559d16a012693bda4197738e6311c14892cadb0"
SUCCESS_MARKER = "EXACT_INTEGER_PROJECTION_CHECKED_PENDING_PRIMITIVE_PROOF"
FALSE_MARKERS = ("FORMAL_PRIMITIVES false", "SPECTRAL_H1 false", "D_N false", "WIN false")
INTEGER_PATTERN = re.compile(r"0|[1-9][0-9]*")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical_integer(text, max_digits=60):
    require(len(text) <= max_digits and INTEGER_PATTERN.fullmatch(text) is not None,
            "NONCANONICAL_INTEGER")
    return int(text)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def small_prime(value):
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return value >= 2


def fixed_constants():
    require(N < K and 2 * N < N + K, "TARGET_COEFFICIENT_ALIAS")
    modulus_product = 1
    for prime, cofactor, base in zip(PRIMES, COFACTORS, BASES):
        require(prime == cofactor * K + 1 and small_prime(prime), "INVALID_PRIME_MODULUS")
        root = pow(base, cofactor, prime)
        require(pow(root, K, prime) == 1 and pow(root, K // 2, prime) != 1,
                "INVALID_ROOT_ORDER")
        modulus_product *= prime
    coefficient_upper = (N + 1) * (32 * S) ** 2
    require(coefficient_upper < 1 << 153 and modulus_product > 1 << 154,
            "CRT_COVERAGE_FAILED")
    primary_numerator = (N + 1) * (64 * S + 1)
    denominator = S * S
    require(2 * primary_numerator * 1000000 <= denominator, "QUANTIZATION_BUDGET_FAILED")
    return modulus_product, coefficient_upper, primary_numerator, denominator


def reconstruct_crt(residues):
    modulus_product = 1
    for prime in PRIMES:
        modulus_product *= prime
    value = 0
    for prime, residue in zip(PRIMES, residues):
        require(0 <= residue < prime, "NONCANONICAL_RESIDUE")
        basis = modulus_product // prime
        inverse = pow(basis % prime, -1, prime)
        require(basis * inverse % prime == 1, "CRT_INVERSE_FAILED")
        value += residue * basis * inverse
    value %= modulus_product
    require(all(value % prime == residue for prime, residue in zip(PRIMES, residues)),
            "CRT_RECHECK_FAILED")
    return value


def read_producer(payload):
    raw = (payload / "producer.txt").read_bytes()
    require(len(raw) <= 4096, "PRODUCER_REPORT_TOO_LARGE")
    parts = raw.decode("ascii").split()
    require(len(parts) == 11 and parts[:4] == ["ROUND22_NATIVE_DIT_OUTPUT", str(N), str(K), str(S)]
            and parts[-1] == "NO_INDEPENDENT_CHECKER_VERDICT", "PRODUCER_REPORT_SCHEMA")
    residues = [canonical_integer(part, 10) for part in parts[4:9]]
    coefficient = canonical_integer(parts[9], 47)
    return residues, coefficient


def read_checker(path):
    raw = path.read_bytes()
    require(len(raw) <= 65536, "CHECKER_REPORT_TOO_LARGE")
    lines = raw.decode("ascii").splitlines()
    require(lines.count(SUCCESS_MARKER) == 1, "CHECKER_SUCCESS_MARKER_MISSING_OR_DUPLICATED")
    begin = lines.index(SUCCESS_MARKER)
    final_lines = lines[begin + 1:]
    require(begin == 0 and len(final_lines) == 11 and tuple(final_lines[-4:]) == FALSE_MARKERS,
            "CHECKER_REPORT_SCHEMA")
    fields = {}
    expected = {"C_A", "DIRECT_A", "C_B", "ERROR_NUMERATOR", "ERROR_DENOMINATOR", "RECORD_COUNT", "RESIDUES"}
    for line in final_lines[:-4]:
        parts = line.split(" ")
        require(parts[0] in expected and parts[0] not in fields,
                "CHECKER_RESULT_FIELD_SCHEMA")
        if parts[0] == "RESIDUES":
            require(len(parts) == 6, "CHECKER_RESIDUE_COUNT")
            fields[parts[0]] = [canonical_integer(part, 10) for part in parts[1:]]
        else:
            require(len(parts) == 2, "CHECKER_RESULT_FIELD_SCHEMA")
            fields[parts[0]] = canonical_integer(parts[1])
    require(set(fields) == expected, "CHECKER_RESULT_FIELDS_MISSING")
    return fields


def payload_manifest(payload):
    require({path.name for path in payload.iterdir()} == {"factors.bin", "records.bin", "producer.txt"},
            "UNEXPECTED_PAYLOAD_FILE")
    factors = payload / "factors.bin"
    records = payload / "records.bin"
    require(factors.stat().st_size == 16 + 4 * (N + 1), "FACTOR_FILE_SIZE")
    with factors.open("rb") as source:
        require(source.read(8) == b"GBCAT22\0" and struct.unpack("<Q", source.read(8))[0] == N,
                "FACTOR_HEADER")
    with records.open("rb") as source:
        require(source.read(8) == b"GBREC22\0" and struct.unpack("<Q", source.read(8))[0] == N,
                "RECORD_HEADER")
        prime_count = struct.unpack("<Q", source.read(8))[0]
    require(prime_count <= N // 2 + 1 and records.stat().st_size == 24 + 16 * prime_count,
            "RECORD_FILE_SIZE")
    bindings = {name: {"bytes": (payload / name).stat().st_size, "sha256": sha256(payload / name)}
                for name in ("factors.bin", "records.bin", "producer.txt")}
    return prime_count, bindings


def decimal_ratio(numerator, denominator):
    with localcontext() as context:
        context.prec = 70
        return str(Decimal(numerator) / Decimal(denominator))


def compare_bindings(recorded, actual):
    require(isinstance(recorded, dict) and set(recorded) == set(actual), "RECEIPT_PAYLOAD_PATH_SET")
    for name, binding in actual.items():
        require(recorded[name]["bytes"] == binding["bytes"]
                and recorded[name]["sha256"] == binding["sha256"], "RECEIPT_PAYLOAD_HASH:" + name)


def validate_execution(path, label, bindings, checker_stdout=None):
    require(path.stat().st_size <= 1 << 20, "EXECUTION_RECEIPT_SIZE")
    receipt = json.loads(path.read_text(encoding="utf-8"))
    expected_status = ("NUMERICAL_CRT_DIRECT_A32_AND_ERROR_BUDGET_VALIDATED" if label == "checker"
                       else "FRESH_PRODUCER_EXIT0_EXPECTED_PAYLOAD_BYTES")
    require(receipt["status"] == expected_status and receipt["label"] == label
            and receipt["error"] is None and receipt["input_bytes_conserved"] is True,
            "EXECUTION_RECEIPT_NOT_SUCCESS:" + label)
    child = receipt["child"]
    require(child["created_suspended"] is True and child["resumed"] is True
            and child["exit_code"] == 0 and child["wait_signalled"] is True
            and child["job_empty_confirmed"] is True and child["termination_reason"] is None
            and child["api_or_control_error"] is None and child["pipe_faults"] == [],
            "EXECUTION_CHILD_NOT_SUCCESS:" + label)
    run = path.parent.resolve()
    require(Path(receipt["run_directory"]).resolve() == run, "EXECUTION_RUN_DIRECTORY")
    if checker_stdout is not None:
        require(checker_stdout == run / "checker.stdout.log", "CHECKER_STDOUT_NOT_RECEIPT_LOG")
    pre = json.loads((run / "PRE.json").read_text(encoding="utf-8"))
    post = json.loads((run / "POST.json").read_text(encoding="utf-8"))
    require(pre["label"] == label and pre["retry_count"] == 0 and post["input_bytes_conserved"] is True,
            "EXECUTION_PRE_POST_SCHEMA")
    require(pre["working_set_limit_requested"] is False
            and sha256(Path(__file__).parent / "infrastructure/windows_numeric_job.py") == pre["backend_sha256"],
            "EXECUTION_BACKEND_CHANGED_OR_PRIVILEGED_WORKING_SET_REQUESTED")
    require(sha256(Path(pre["checker"])) == pre["checker_sha256"], "EXECUTED_BINARY_CHANGED")
    if label == "checker":
        for key in ("payload_original", "payload_copy"):
            compare_bindings(post[key], bindings)
            require(pre[key] == post[key], "EXECUTION_PRE_POST_INPUT_CHANGED")
        build = json.loads((Path(__file__).parent / "checker_build_receipt.json").read_text(encoding="utf-8"))
        require(build["build_exit_code"] == 0 and build["self_test_exit_code"] == 0
                and build["executable_sha256"] == pre["checker_sha256"]
                and sha256(Path(build["source_operational"])) == build["source_operational_sha256"],
                "CHECKER_BUILD_PROVENANCE_CHANGED")
    else:
        require(pre["checker_sha256"] == PRODUCER_BINARY_SHA256, "PRODUCER_BINARY_NOT_FROZEN_BUILD04")
        compare_bindings(post["fresh_payload"], bindings)
        require(post["matches_archived_producer_payload_sha256"] is True, "FRESH_PRODUCER_HASH_MISMATCH")
    return {"receipt_sha256": sha256(path), "wall_seconds": receipt["wall_seconds"],
            "cpu_user_seconds": child["cpu_user_seconds"], "cpu_kernel_seconds": child["cpu_kernel_seconds"],
            "cpu_total_seconds": child["cpu_total_seconds"], "peak_rss_bytes": child["peak_rss_bytes"],
            "peak_job_committed_bytes": child["peak_job_committed_bytes"],
            "execution_and_POST_validated": True}


def audit(payload, checker_stdout, execution_receipt=None, producer_receipt=None):
    modulus_product, coefficient_upper, primary_numerator, denominator = fixed_constants()
    residues, producer_coefficient = read_producer(payload)
    fields = read_checker(checker_stdout)
    require(fields["RESIDUES"] == residues, "DIT_DIF_EXPLICIT_RESIDUES_DISAGREE")
    coefficient = fields["C_A"]
    independent_crt = reconstruct_crt(residues)
    require(independent_crt == producer_coefficient == coefficient == fields["DIRECT_A"],
            "CRT_PRODUCER_DIRECT_A32_DISAGREEMENT")
    require(0 <= coefficient <= coefficient_upper and coefficient < 1 << 153,
            "PRIMARY_COEFFICIENT_RANGE")
    reference = fields["C_B"]
    require(0 <= reference <= coefficient_upper, "REFERENCE_COEFFICIENT_RANGE")
    joint_numerator = 2 * primary_numerator
    require(fields["ERROR_NUMERATOR"] == joint_numerator and fields["ERROR_DENOMINATOR"] == denominator,
            "WRONG_ERROR_ENVELOPE")
    difference = abs(coefficient - reference)
    require(difference <= joint_numerator and joint_numerator * 1000000 <= denominator,
            "FINAL_EXACT_ERROR_GUARD")
    prime_count, bindings = payload_manifest(payload)
    require(fields["RECORD_COUNT"] == prime_count, "CHECKER_RECORD_COUNT_DISAGREES")
    checker_execution = validate_execution(execution_receipt, "checker", bindings, checker_stdout) if execution_receipt else None
    producer_execution = validate_execution(producer_receipt, "producer", bindings) if producer_receipt else None
    result = {
        "schema": "GOLDBACH_INDEPENDENT_NUMERICAL_AUDIT_20261004",
        "status": "EXACT_NUMERICAL_ARITHMETIC_VALIDATED",
        "N": N, "K": K, "S": str(S), "prime_moduli": list(PRIMES),
        "modular_residues": residues, "CRT_product": str(modulus_product),
        "independent_CRT_integer": str(independent_crt), "C_A_integer": str(coefficient),
        "direct_A32_integer": str(fields["DIRECT_A"]), "C_B40_integer": str(reference),
        "CRT_equals_producer_equals_direct_A32": True,
        "coefficient_denominator": str(denominator),
        "coefficient_decimal": decimal_ratio(coefficient, denominator),
        "actual_difference_numerator": str(difference),
        "actual_difference_decimal": decimal_ratio(difference, denominator),
        "primary_E_log_numerator": str(primary_numerator),
        "primary_E_log_decimal": decimal_ratio(primary_numerator, denominator),
        "joint_2E_log_numerator": str(joint_numerator),
        "joint_2E_log_decimal": decimal_ratio(joint_numerator, denominator),
        "joint_radius_le_1e_minus6": True,
        "primary_interval_numerators": [str(coefficient - primary_numerator), str(coefficient + primary_numerator)],
        "prime_record_count": prime_count, "payload_bindings": bindings,
        "checker_stdout_sha256": sha256(checker_stdout),
        "execution_receipt_path": str(execution_receipt) if execution_receipt else None,
        "checker_execution": checker_execution, "fresh_producer_execution": producer_execution,
        "independent_full_catalogue_replay": False,
        "catalogue_and_A32_words_checked_by_native_checker": True,
        "native_Lean_refinement": False, "B40_real_log_refinement_Lean": False,
        "Mellin_coefficient_truncation_chain_compiled": False,
        "spectral_H1": False, "D_N": False, "WIN": False,
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--payload", type=Path, required=True)
    parser.add_argument("--checker-stdout", type=Path, required=True)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--producer-receipt", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = audit(args.payload.resolve(), args.checker_stdout.resolve(),
                       args.receipt.resolve() if args.receipt else None,
                       args.producer_receipt.resolve() if args.producer_receipt else None)
    except (OSError, ValueError, UnicodeError, struct.error, KeyError, TypeError) as error:
        result = {"status": "NUMERICAL_AUDIT_FAILED", "error": str(error)}
        print(json.dumps(result, ensure_ascii=True), file=sys.stderr)
        return 1
    serialized = json.dumps(result, indent=2, ensure_ascii=True) + "\n"
    if args.output:
        args.output.write_text(serialized, encoding="utf-8")
    print(serialized, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
