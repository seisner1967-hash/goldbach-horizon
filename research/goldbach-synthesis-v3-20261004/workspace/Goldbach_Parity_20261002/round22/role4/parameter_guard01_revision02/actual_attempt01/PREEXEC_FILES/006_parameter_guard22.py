"""SOURCE ONLY. Future bounded auxiliary parameter/sample evaluation, no NTT."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

MODEL_SHA = "80718ee9c1306a974554a70322ad36648897216890f6747ed2ddede840421d98"
SAMPLES = (2, 3, 4, 99999989, 100000000)
N, K, S = 100000000, 134217728, 288230376151711744


def demand(ok, why):
    if not ok:
        raise ArithmeticError(why)


def expected_rejection(name, message, action):
    try:
        action()
    except ArithmeticError as error:
        demand(str(error) == message, "UNEXPECTED_MUTATION_DIAGNOSTIC:" + name)
        return {"name": name, "rejected": True, "diagnostic": str(error)}
    raise ArithmeticError("MUTATION_NOT_REJECTED:" + name)


def tau_guard(scale):
    demand(scale > 0, "AUX_SCALE_DOMAIN")
    demand(2 * (N + 1) * (64 * scale + 1) * 1000000 <= scale * scale,
           "AUX_TAU_TOO_LARGE")


def main():
    started = time.monotonic()
    demand(len(sys.argv) == 2, "MODEL_ARGUMENT_REQUIRED")
    demand(sys.flags.isolated and sys.flags.no_site and sys.flags.utf8_mode == 1
           and sys.dont_write_bytecode, "CANONICAL_ISOLATED_NO_BYTECODE_REQUIRED")
    path = Path(sys.argv[1]).resolve()
    demand(hashlib.sha256(path.read_bytes()).hexdigest() == MODEL_SHA,
           "IMMUTABLE_MODEL_BYTES_CHANGED")
    spec = importlib.util.spec_from_file_location("fixed_parameter_model_guard01", path)
    demand(spec is not None and spec.loader is not None, "MODEL_LOADER_UNAVAILABLE")
    model = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(model)  # Future authorized child only; never executed in preparation.
    demand((model.N, model.K, model.S) == (N, K, S), "FIXED_INPUTS_CHANGED")
    constants = model.check_fixed_constants()
    tau_guard(S)
    samples = []
    for value in SAMPLES:
        point32 = model.quantized_log_point(value, 32)
        demand(model.verify_record_log_point(value, point32), "SAMPLE_LOG40_REJECTION")
        point40 = model.quantized_log_point(value, 40)
        demand(model.verify_record_log_point(value, point40), "SAMPLE_LOG40_SELF_REJECTION")
        demand(abs(point32 - point40) <= 2, "SAMPLE_JOINT_ENDPOINT_DIFFERENCE")
        samples.append({"argument": value, "point32": str(point32), "point40": str(point40),
                        "log40_endpoint_guards": True, "argument_primality_claimed": False})
        demand(time.monotonic() - started < 60, "AUX_WALL_LIMIT_NO_VERDICT")

    original = model.MODULI
    try:
        # Exact compositeness witness: K+1 = 134217729 = 3*44739243.
        demand(K + 1 == 3 * 44739243, "COMPOSITE_MUTATION_WITNESS")
        model.MODULI = ((K + 1, 1, 31),) + original[1:]
        composite = expected_rejection("COMPOSITE_3_TIMES_44739243",
            "INVALID_MODULAR_PARAMETER_COMPOSITE", model.check_fixed_constants)
    finally:
        model.MODULI = original
    try:
        # g=1 forces omega=1 and omega^(K/2)=1, which violates exact order K.
        p, c, _ = original[0]
        model.MODULI = ((p, c, 1),) + original[1:]
        root = expected_rejection("ROOT_ONE_ORDER_ONE", "ROOT_ORDER_FAILED",
                                  model.check_fixed_constants)
    finally:
        model.MODULI = original
    # log 2 < 1, whereas this stored point represents 32. No endpoint radius is supplied.
    point = expected_rejection("POINT_32_FOR_LOG_2", "RECORD_LOW_ENDPOINT_FAILED",
                               lambda: model.verify_record_log_point(2, 32 * S))
    # At scale=1 the displayed integer tau inequality is strictly false.
    scale = expected_rejection("SCALE_ONE_TAU_VIOLATION", "AUX_TAU_TOO_LARGE",
                               lambda: tau_guard(1))
    demand(model.MODULI == original and (model.N, model.K, model.S) == (N, K, S),
           "MODEL_MEMORY_RESTORATION_FAILED")
    demand(time.monotonic() - started < 60, "AUX_WALL_LIMIT_NO_VERDICT")
    result = {"schema": "ROUND22_PARAMETER_GUARD01_RESULT",
              "status": "PARAMETER_GUARDS_AND_FIVE_LOG_SAMPLES_AUX_PASS",
              "scope": "PARAMETER_GUARD01_ONLY", "N": N, "K": K, "S": str(S),
              "constants": constants, "samples": samples,
              "mutations": [composite, root, point, scale],
              "model_sha256": MODEL_SHA, "global_NTT_computed": False,
              "complete_catalogue_checked": False, "coefficient_N_computed": False,
              "log_primitive_Lean_certified": False, "spectral_H1": False,
              "D_N": False, "WIN": False}
    data = (json.dumps(result, sort_keys=True, indent=2) + "\n").encode("utf-8")
    demand(len(data) <= 32768, "AUX_RESULT_SIZE")
    sys.stdout.buffer.write(data)


if __name__ == "__main__":
    main()
