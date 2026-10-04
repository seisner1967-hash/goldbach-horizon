"""Join both completed native executions and write the numerical addendum."""
from datetime import datetime
import json
from pathlib import Path

from audit_receipt import audit, require, sha256


HERE = Path(__file__).resolve().parent


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def completed(receipt):
    child = receipt["child"]
    require(receipt["error"] is None and receipt["input_bytes_conserved"], "PARENT_NOT_SUCCESSFUL")
    require(child["exit_code"] == 0 and child["resumed"] and child["wait_signalled"]
            and child["job_empty_confirmed"] and child["termination_reason"] is None
            and child["api_or_control_error"] is None and not child["pipe_faults"],
            "NATIVE_CHILD_NOT_SUCCESSFUL")
    return child


def duration(seconds):
    minutes, rest = divmod(seconds, 60)
    return f"{int(minutes)} min {rest:.3f} s"


def main():
    producer_dir = HERE / "producer_run02"
    checker_dir = HERE / "checker_run01"
    producer = read_json(producer_dir / "receipt.json")
    checker = read_json(checker_dir / "receipt.json")
    pc, cc = completed(producer), completed(checker)
    require(producer["status"] == "FRESH_PRODUCER_EXIT0_EXPECTED_PAYLOAD_BYTES", "PRODUCER_STATUS")
    require(checker["status"] == "NUMERICAL_CRT_DIRECT_A32_AND_ERROR_BUDGET_VALIDATED", "CHECKER_STATUS")
    fresh = Path(producer["payload_directory"])
    checked = Path(checker["payload_directory"])
    identity = {}
    for name in ("factors.bin", "records.bin", "producer.txt"):
        digest = sha256(fresh / name)
        require(digest == sha256(checked / name), "FRESH_CHECKED_BYTES_DIFFER:" + name)
        identity[name] = {"sha256": digest, "bytes": (fresh / name).stat().st_size}
    result = audit(fresh, checker_dir / "checker.stdout.log", checker_dir / "receipt.json",
                   producer_dir / "receipt.json")
    result["fresh_producer_matches_entire_checked_payload"] = True
    result["fresh_checked_payload_identity"] = identity
    result["producer_receipt_sha256"] = sha256(producer_dir / "receipt.json")
    result["checker_receipt_sha256"] = sha256(checker_dir / "receipt.json")
    result["checker_build_receipt_sha256"] = sha256(HERE / "checker_build_receipt.json")
    result["run_contract_sha256"] = sha256(HERE / "run_contract.json")
    result["executions"] = {
        "producer": {"parent_wall_seconds": producer["wall_seconds"], **pc},
        "checker": {"parent_wall_seconds": checker["wall_seconds"], **cc},
    }
    start = datetime.fromisoformat(read_json(producer_dir / "producer_START.json")["utc"])
    finish = max(datetime.fromisoformat(producer["utc"]), datetime.fromisoformat(checker["utc"]))
    result["parallel_total_wall_seconds"] = (finish - start).total_seconds()
    result["initial_infrastructure_stop_receipt"] = "producer_run01/receipt.json"
    result["initial_infrastructure_stop"] = "Auxiliary console process exceeded initial process-count monitor; fixed before completed executions."
    report = (
        "ADDENDUM NUMERIQUE - 4 OCTOBRE 2026\n"
        "Verdict : PASS numerique fini, N=100000000, K=134217728, S=2^58.\n"
        f"Catalogue : {result['prime_record_count']} premiers, couverture 0..N et poids A32 controles.\n"
        f"CRT independante = somme directe A32 : {result['C_A_integer']}\n"
        f"Residus : {', '.join(map(str, result['modular_residues']))}\n"
        f"Coefficient I_N/S^2 : {result['coefficient_decimal']}\n"
        f"Reference B40 : {result['C_B40_integer']}\n"
        f"Ecart entier A32/B40 : {result['actual_difference_numerator']}\n"
        f"Ecart normalise : {result['actual_difference_decimal']}\n"
        f"Budget fixe 2E_log : {result['joint_2E_log_decimal']} < 0.000001.\n"
        f"Rayon E_log autour du coefficient primaire : {result['primary_E_log_decimal']}.\n"
        f"Producteur : {duration(pc['wall_seconds'])}, CPU {pc['cpu_total_seconds']:.3f} s, RSS pic {pc['peak_rss_bytes']} octets.\n"
        f"Verificateur : {duration(cc['wall_seconds'])}, CPU {cc['cpu_total_seconds']:.3f} s, RSS pic {cc['peak_rss_bytes']} octets.\n"
        f"Duree totale parallele : {duration(result['parallel_total_wall_seconds'])}.\n"
        "Producteur historique inchange, relance sur dossier neuf; trois fichiers identiques par SHA-256 aux fichiers verifies.\n"
        "Verificateur : variante operationnelle exacte, Horner/cache log2; 128 comparaisons rationnelles avec la source originale PASS.\n"
        "Windows : aucune limite working-set privilegiee; commit Job 3 Gio, suivi CPU/RSS, sorties confirmees avec code 0.\n"
        "Portee : budget de quantification A32/B40 valide. Pas de calcul Mellin tronque ni validation de son raccord SOURCE; pas de nouvelle preuve Lean ou de resultat sur D_N.\n"
        "Recus : producer_run02/receipt.json, checker_run01/receipt.json, numerical_verdict.json.\n"
    )
    verdict_path = HERE / "numerical_verdict.json"
    report_path = HERE / "numerical_addendum.txt"
    require(not verdict_path.exists() and not report_path.exists(), "FINAL_OUTPUTS_ALREADY_EXIST")
    verdict_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    report_path.write_text(report, encoding="ascii")
    print(json.dumps({"status": result["status"], "report": str(report_path),
                      "verdict": str(verdict_path)}, indent=2))


if __name__ == "__main__":
    main()
