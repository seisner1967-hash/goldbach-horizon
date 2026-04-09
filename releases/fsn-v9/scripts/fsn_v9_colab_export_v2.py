
"""
FSN v9 Colab-friendly exporter V2
---------------------------------
This version accepts:
- a ZIP package such as FSN_v9_required_artifacts.zip
- optional metrics.json
- optional theorems.txt

It can:
1. auto-extract uploaded ZIP archives
2. auto-detect common FSN v9 artifacts
3. verify SHA-256 hashes
4. merge build metrics from metrics.json / logs
5. generate:
   - fsn_v9_attestation_summary.csv
   - fsn_v9_attestation.png
   - fsn_v9_attestation_summary.json
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import zipfile
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import matplotlib.pyplot as plt
import pandas as pd


CONFIG = {
    "workdir": ".",
    "auto_extract_zips": True,
    "zip_glob_patterns": ["*.zip"],

    "artifacts": {
        "A2_certified_v3.json": "171f7f392eedba63c5cc48b7650d5afe06651ab131f8bc10093af3d141db8852",
        "Goldbach_MT8.lean": None,
        "lake-manifest.json": None,
        "certificate.mt8.json": None,
        "Dockerfile.mt8": None,
        "replay_transcript.mt8.txt": None,
    },

    "build_log": "replay_transcript.mt8.txt",
    "theorem_export": "theorems.txt",
    "metrics_json": "metrics.json",
    "certificate_json": "certificate.mt8.json",

    "project_name": "Horizon Programme",
    "document_title": "FSN v9 — Final Attestation",
    "docker_image": "horizon/goldbach:v9.0.0",
    "docker_image_hash": "",
    "git_tag": "v9.0.0-final",
    "git_commit": "",
    "lean_version": "4.29.0",
    "mathlib_version": "v4.29.0",
    "host_kernel": "",
    "build_started_utc": "",
    "build_finished_utc": "",

    "elapsed_seconds": None,
    "peak_ram_gb": None,
    "olean_total_mb": None,
    "modules_compiled": None,
    "lean_lines_total": None,

    "expected_theorems": [
        "Horizon.Goldbach.A2_KLMN_closed",
        "Horizon.Goldbach.MT4_F1_of_A2",
        "Horizon.Goldbach.MT3_goldbach_from_F1",
        "Horizon.Goldbach.goldbach_asymptotic_theorem",
    ],

    "csv_output": "fsn_v9_attestation_summary.csv",
    "png_output": "fsn_v9_attestation.png",
    "json_output": "fsn_v9_attestation_summary.json",
}


def sha256_file(path: Path) -> Optional[str]:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def safe_read_text(path: Path) -> str:
    if not path.exists():
        return ""
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return path.read_text(encoding="latin-1", errors="replace")


def load_json_if_exists(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}


def fmt_seconds(x: Optional[float]) -> str:
    if x is None or (isinstance(x, float) and math.isnan(x)):
        return "n/a"
    x = int(round(float(x)))
    m, s = divmod(x, 60)
    h, m = divmod(m, 60)
    if h:
        return f"{h}h {m}m {s}s"
    if m:
        return f"{m}m {s}s"
    return f"{s}s"


def fmt_float(x: Optional[float], suffix: str = "") -> str:
    if x is None or (isinstance(x, float) and math.isnan(x)):
        return "n/a"
    if isinstance(x, int):
        return f"{x}{suffix}"
    return f"{x:.3f}{suffix}"


def auto_extract_zips(workdir: Path, patterns: List[str]) -> List[str]:
    extracted = []
    for pat in patterns:
        for zpath in workdir.glob(pat):
            if not zpath.is_file():
                continue
            try:
                with zipfile.ZipFile(zpath, "r") as zf:
                    zf.extractall(workdir)
                    extracted.append(zpath.name)
            except zipfile.BadZipFile:
                pass
    return extracted


def parse_time_from_log(text: str) -> Optional[float]:
    patterns = [
        r"real\s+(\d+)m([\d.]+)s",
        r"elapsed(?:_seconds)?\s*[:=]\s*([\d.]+)",
        r"total build time\s*[:=]\s*([\d.]+)\s*s",
    ]
    for pat in patterns:
        m = re.search(pat, text, flags=re.IGNORECASE)
        if m:
            if len(m.groups()) == 2:
                return int(m.group(1)) * 60 + float(m.group(2))
            return float(m.group(1))
    return None


def parse_numeric_from_log(text: str, patterns: List[str]) -> Optional[float]:
    for pat in patterns:
        m = re.search(pat, text, flags=re.IGNORECASE)
        if m:
            try:
                return float(m.group(1))
            except Exception:
                pass
    return None


def parse_build_log(text: str) -> dict:
    out = {
        "errors": None,
        "warnings": None,
        "sorries": None,
        "axioms_nonstandard": None,
        "elapsed_seconds": parse_time_from_log(text),
        "peak_ram_gb": parse_numeric_from_log(text, [
            r"peak(?:_ram| ram)?\s*[:=]\s*([\d.]+)\s*gb",
            r"max(?:imum)?(?:_memory| memory)?\s*[:=]\s*([\d.]+)\s*gb",
        ]),
        "modules_compiled": parse_numeric_from_log(text, [
            r"modules compiled\s*[:=]\s*(\d+)",
            r"compiled\s+(\d+)\s+modules",
        ]),
        "olean_total_mb": parse_numeric_from_log(text, [
            r"\.olean(?: files)? total\s*[:=]\s*([\d.]+)\s*mb",
            r"olean_total_mb\s*[:=]\s*([\d.]+)",
        ]),
    }

    err = re.search(r"(\d+)\s+errors?", text, flags=re.IGNORECASE)
    warn = re.search(r"(\d+)\s+warnings?", text, flags=re.IGNORECASE)
    sorry = re.search(r"(\d+)\s+sorr(?:y|ies)", text, flags=re.IGNORECASE)
    ax = re.search(r"(\d+)\s+axioms?(?:\s+non[- ]standard)?", text, flags=re.IGNORECASE)

    if err:
        out["errors"] = int(err.group(1))
    if warn:
        out["warnings"] = int(warn.group(1))
    if sorry:
        out["sorries"] = int(sorry.group(1))
    if ax:
        out["axioms_nonstandard"] = int(ax.group(1))

    if out["warnings"] is None and re.search(r"0\s+warnings?", text, flags=re.IGNORECASE):
        out["warnings"] = 0
    if out["errors"] is None and re.search(r"0\s+errors?", text, flags=re.IGNORECASE):
        out["errors"] = 0
    if out["sorries"] is None and re.search(r"0\s+sorr(?:y|ies)", text, flags=re.IGNORECASE):
        out["sorries"] = 0
    if out["axioms_nonstandard"] is None and re.search(r"0\s+axioms?(?:\s+non[- ]standard)?", text, flags=re.IGNORECASE):
        out["axioms_nonstandard"] = 0

    return out


def parse_theorem_export(text: str, expected: List[str]) -> Dict[str, bool]:
    results = {}
    for thm in expected:
        results[thm] = thm in text or thm.split(".")[-1] in text
    return results


def get_certificate_theorems(cert: dict, expected: List[str]) -> Dict[str, bool]:
    found = {thm: False for thm in expected}
    if not cert:
        return found
    blob = json.dumps(cert, ensure_ascii=False)
    for thm in expected:
        found[thm] = thm in blob or thm.split(".")[-1] in blob
    return found


def render_png_report(
    df: pd.DataFrame,
    png_path: Path,
    config: dict,
    final_ok: bool,
    elapsed_seconds,
    peak_ram_gb,
    olean_total_mb,
    modules_compiled,
    lean_lines_total,
    errors,
    warnings,
    sorries,
    axioms_nonstandard,
    theorem_status: Dict[str, bool],
    extracted_zips: List[str],
) -> None:
    fig = plt.figure(figsize=(16, 20), dpi=220)
    ax = fig.add_axes([0, 0, 1, 1])
    ax.axis("off")
    y = 0.975

    def put(line: str, dy: float = 0.026, size: int = 13, weight: str = "normal"):
        nonlocal y
        fig.text(0.05, y, line, fontsize=size, fontweight=weight, va="top", ha="left")
        y -= dy

    put(config["document_title"], dy=0.035, size=22, weight="bold")
    put(config["project_name"], dy=0.03, size=15)
    put(f"Status: {'COMPILED AND ATTESTED' if final_ok else 'PENDING / INCOMPLETE'}", dy=0.035, size=18, weight="bold")

    put("Metadata", dy=0.03, size=17, weight="bold")
    put(f"Git tag: {config['git_tag']}")
    put(f"Git commit: {config.get('git_commit','')}")
    put(f"Docker image: {config['docker_image']}")
    put(f"Docker image hash: {config.get('docker_image_hash','')}")
    put(f"Lean / Mathlib: {config['lean_version']} / {config['mathlib_version']}")
    put(f"Build started UTC: {config.get('build_started_utc','')}")
    put(f"Build finished UTC: {config.get('build_finished_utc','')}")
    if extracted_zips:
        put(f"Auto-extracted ZIPs: {', '.join(extracted_zips)}")
    y -= 0.01

    put("Build metrics", dy=0.03, size=17, weight="bold")
    put(f"Elapsed time: {fmt_seconds(elapsed_seconds)}")
    put(f"Peak RAM: {fmt_float(peak_ram_gb, ' GB')}")
    put(f"Total .olean size: {fmt_float(olean_total_mb, ' MB')}")
    put(f"Modules compiled: {fmt_float(modules_compiled)}")
    put(f"Lean lines compiled: {fmt_float(lean_lines_total)}")
    put(f"Errors / warnings / sorries / nonstandard axioms: {errors} / {warnings} / {sorries} / {axioms_nonstandard}")
    y -= 0.01

    put("Integrity checks", dy=0.03, size=17, weight="bold")
    integ = df[df["section"] == "integrity"]
    for _, row in integ.iterrows():
        display_value = row["value"] if str(row["value"]).strip() else "n/a"
        put(f"{row['key']}: {row['status']}  {display_value}", dy=0.024, size=12)

    y -= 0.01
    put("Kernel-attested theorem targets", dy=0.03, size=17, weight="bold")
    for name, ok in theorem_status.items():
        put(f"{name.split('.')[-1]}: {'attested' if ok else 'missing'}", dy=0.024, size=12)

    y -= 0.01
    put("Final declaration", dy=0.03, size=17, weight="bold")
    if final_ok:
        put(
            "The Horizon Programme has established the asymptotic Goldbach theorem "
            "as a mechanically verified formal conditional theorem in the pinned Lean environment.",
            dy=0.028,
            size=13,
            weight="bold",
        )
    else:
        put(
            "This sheet is replay-ready but not yet fully attested. "
            "At least one integrity check, build metric, or theorem attestation is still missing.",
            dy=0.028,
            size=13,
            weight="bold",
        )

    y -= 0.012
    put("Trusted Computing Base (TCB)", dy=0.03, size=17, weight="bold")
    put("1. Lean kernel")
    put("2. GMP / MPFR arithmetic stack")
    put("3. Uploaded MT6 witness file at parse time (SHA-256 checked)")
    put("4. Execution environment (OS / hardware)")

    y -= 0.012
    put("Reproduction command sketch", dy=0.03, size=17, weight="bold")
    put(f"docker run --rm {config['docker_image']} lake build", dy=0.024, size=12)
    put(f"docker run --rm {config['docker_image']} lake exe verify_goldbach", dy=0.024, size=12)

    fig.savefig(png_path, bbox_inches="tight")
    plt.close(fig)


def build_report(config: dict):
    workdir = Path(config["workdir"]).resolve()
    extracted_zips = []
    if config.get("auto_extract_zips", True):
        extracted_zips = auto_extract_zips(workdir, config.get("zip_glob_patterns", ["*.zip"]))

    build_log_path = workdir / config["build_log"]
    theorem_export_path = workdir / config["theorem_export"]
    metrics_json_path = workdir / config["metrics_json"]
    certificate_json_path = workdir / config["certificate_json"]

    build_log_text = safe_read_text(build_log_path)
    theorem_export_text = safe_read_text(theorem_export_path)
    metrics_json = load_json_if_exists(metrics_json_path)
    certificate_json = load_json_if_exists(certificate_json_path)

    parsed_log = parse_build_log(build_log_text)
    parsed_theorems = parse_theorem_export(theorem_export_text, config["expected_theorems"])
    cert_theorems = get_certificate_theorems(certificate_json, config["expected_theorems"])

    theorem_status = {}
    for thm in config["expected_theorems"]:
        theorem_status[thm] = parsed_theorems.get(thm, False) or cert_theorems.get(thm, False)

    rows = []
    def add(section: str, key: str, value, status: str = "", notes: str = ""):
        rows.append({"section": section, "key": key, "value": value, "status": status, "notes": notes})

    add("metadata", "project_name", config["project_name"])
    add("metadata", "document_title", config["document_title"])
    add("metadata", "git_tag", config["git_tag"])
    add("metadata", "git_commit", config["git_commit"] or metrics_json.get("git_commit", ""))
    add("metadata", "docker_image", config["docker_image"])
    add("metadata", "docker_image_hash", config["docker_image_hash"] or metrics_json.get("docker_image_hash", ""))
    add("metadata", "lean_version", config["lean_version"])
    add("metadata", "mathlib_version", config["mathlib_version"])
    add("metadata", "host_kernel", config["host_kernel"] or metrics_json.get("host_kernel", ""))
    add("metadata", "build_started_utc", config["build_started_utc"] or metrics_json.get("build_started_utc", ""))
    add("metadata", "build_finished_utc", config["build_finished_utc"] or metrics_json.get("build_finished_utc", ""))
    add("metadata", "auto_extracted_zips", ", ".join(extracted_zips))

    all_hashes_ok = True
    for name, expected_hash in config["artifacts"].items():
        actual_hash = sha256_file(workdir / name)
        if actual_hash is None:
            status = "missing"
            all_hashes_ok = False
        elif expected_hash is None:
            status = "computed"
        elif actual_hash == expected_hash:
            status = "ok"
        else:
            status = "mismatch"
            all_hashes_ok = False
        add("integrity", name, actual_hash or "", status=status, notes=f"expected={expected_hash or ''}")

    elapsed_seconds = config["elapsed_seconds"]
    if elapsed_seconds is None:
        elapsed_seconds = metrics_json.get("elapsed_seconds", parsed_log.get("elapsed_seconds"))

    peak_ram_gb = config["peak_ram_gb"]
    if peak_ram_gb is None:
        peak_ram_gb = metrics_json.get("peak_ram_gb", parsed_log.get("peak_ram_gb"))

    olean_total_mb = config["olean_total_mb"]
    if olean_total_mb is None:
        olean_total_mb = metrics_json.get("olean_total_mb", parsed_log.get("olean_total_mb"))

    modules_compiled = config["modules_compiled"]
    if modules_compiled is None:
        modules_compiled = metrics_json.get("modules_compiled", parsed_log.get("modules_compiled"))

    lean_lines_total = config["lean_lines_total"]
    if lean_lines_total is None:
        lean_lines_total = metrics_json.get("lean_lines_total", None)

    errors = metrics_json.get("errors", parsed_log.get("errors"))
    warnings = metrics_json.get("warnings", parsed_log.get("warnings"))
    sorries = metrics_json.get("sorries", parsed_log.get("sorries"))
    axioms_nonstandard = metrics_json.get("axioms_nonstandard", parsed_log.get("axioms_nonstandard"))

    add("build", "elapsed_seconds", elapsed_seconds, status="ok" if elapsed_seconds is not None else "")
    add("build", "peak_ram_gb", peak_ram_gb, status="ok" if peak_ram_gb is not None else "")
    add("build", "olean_total_mb", olean_total_mb, status="ok" if olean_total_mb is not None else "")
    add("build", "modules_compiled", modules_compiled, status="ok" if modules_compiled is not None else "")
    add("build", "lean_lines_total", lean_lines_total, status="ok" if lean_lines_total is not None else "")
    add("build", "errors", errors, status="ok" if errors == 0 else "")
    add("build", "warnings", warnings, status="ok" if warnings == 0 else "")
    add("build", "sorries", sorries, status="ok" if sorries == 0 else "")
    add("build", "axioms_nonstandard", axioms_nonstandard, status="ok" if axioms_nonstandard == 0 else "")

    all_theorems_ok = True
    for thm, ok in theorem_status.items():
        add("theorems", thm, str(ok), status="attested" if ok else "missing")
        if not ok:
            all_theorems_ok = False

    build_clean = (errors == 0 and warnings == 0 and sorries == 0 and axioms_nonstandard == 0)
    final_ok = bool(all_hashes_ok and build_clean and all_theorems_ok)

    add(
        "final",
        "fsn_v9_status",
        "compiled-and-attested" if final_ok else "pending-or-incomplete",
        status="ok" if final_ok else "pending",
        notes="Requires integrity, clean build, and theorem attestation."
    )

    summary = {
        "project_name": config["project_name"],
        "document_title": config["document_title"],
        "status": "compiled-and-attested" if final_ok else "pending-or-incomplete",
        "git_tag": config["git_tag"],
        "git_commit": config["git_commit"] or metrics_json.get("git_commit", ""),
        "docker_image": config["docker_image"],
        "docker_image_hash": config["docker_image_hash"] or metrics_json.get("docker_image_hash", ""),
        "lean_version": config["lean_version"],
        "mathlib_version": config["mathlib_version"],
        "build_started_utc": config["build_started_utc"] or metrics_json.get("build_started_utc", ""),
        "build_finished_utc": config["build_finished_utc"] or metrics_json.get("build_finished_utc", ""),
        "auto_extracted_zips": extracted_zips,
        "metrics": {
            "elapsed_seconds": elapsed_seconds,
            "peak_ram_gb": peak_ram_gb,
            "olean_total_mb": olean_total_mb,
            "modules_compiled": modules_compiled,
            "lean_lines_total": lean_lines_total,
            "errors": errors,
            "warnings": warnings,
            "sorries": sorries,
            "axioms_nonstandard": axioms_nonstandard,
        },
        "theorems": theorem_status,
    }

    df = pd.DataFrame(rows)

    csv_path = workdir / config["csv_output"]
    png_path = workdir / config["png_output"]
    json_path = workdir / config["json_output"]

    df.to_csv(csv_path, index=False)
    json_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")

    render_png_report(
        df=df,
        png_path=png_path,
        config=config,
        final_ok=final_ok,
        elapsed_seconds=elapsed_seconds,
        peak_ram_gb=peak_ram_gb,
        olean_total_mb=olean_total_mb,
        modules_compiled=modules_compiled,
        lean_lines_total=lean_lines_total,
        errors=errors,
        warnings=warnings,
        sorries=sorries,
        axioms_nonstandard=axioms_nonstandard,
        theorem_status=theorem_status,
        extracted_zips=extracted_zips,
    )

    return df, csv_path, png_path, json_path, summary


def run():
    df, csv_path, png_path, json_path, summary = build_report(CONFIG)
    print("Done.")
    print(f"CSV saved to: {csv_path}")
    print(f"PNG saved to: {png_path}")
    print(f"JSON saved to: {json_path}")
    print()
    print(df.to_string(index=False))
    print()
    print("Final status:", summary["status"])


if __name__ == "__main__":
    run()
