"""Compile the portable manuscript with an existing cached Tectonic engine.

This performs document compilation only. It never invokes Lean or a solver.
Pass an existing engine with --engine and optionally a read-only existing cache
with --cache-source. All newly written cache, temporary and intermediate files
stay in paper/_compile. No engine or package installation is attempted.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess


def digest(path):
    data = path.read_bytes()
    return {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", default=shutil.which("tectonic"))
    parser.add_argument("--cache-source", type=Path)
    args = parser.parse_args()
    if not args.engine or not Path(args.engine).is_file():
        parser.error("Supply an existing Tectonic executable; installation is not performed.")
    paper = Path(__file__).resolve().parent
    work = paper / "_compile"
    cache, tmp = work / "cache", work / "tmp"
    cache.mkdir(parents=True, exist_ok=True)
    tmp.mkdir(parents=True, exist_ok=True)
    if args.cache_source:
        shutil.copytree(args.cache_source, cache, dirs_exist_ok=True)
    serial = 1
    while (work / ("run" + str(serial))).exists():
        serial += 1
    run = work / ("run" + str(serial))
    run.mkdir()
    source_names = (sorted(path.name for path in paper.glob("*.tex")) +
                    sorted(path.name for path in paper.glob("*.bst")) + ["references.bib"])
    for name in source_names:
        shutil.copy2(paper / name, run / name)
    shutil.copytree(paper / "figures", run / "figures")
    env = os.environ.copy()
    env["TECTONIC_CACHE_DIR"] = str(cache)
    env["TEMP"] = str(tmp)
    env["TMP"] = str(tmp)
    # Confine fontconfig's newly written cache to the document work directory.
    fontconfig = work / "fontconfig"
    fontconfig.mkdir(exist_ok=True)
    (fontconfig / "cache").mkdir(exist_ok=True)
    font_data = [p for p in (cache / "bundles" / "data").iterdir() if p.is_dir()]
    font_dirs = "".join("<dir>" + p.as_posix() + "</dir>" for p in font_data)
    (fontconfig / "fonts.conf").write_text(
        "<fontconfig>" + font_dirs + "<cachedir>" +
        (fontconfig / "cache").as_posix() + "</cachedir></fontconfig>",
        encoding="utf8", newline="\n")
    env["FONTCONFIG_FILE"] = str(fontconfig / "fonts.conf")
    env["FONTCONFIG_PATH"] = str(fontconfig)
    version = subprocess.run([args.engine, "--version"], capture_output=True,
                             text=True, check=True).stdout.strip()
    command = [args.engine, "--only-cached", "--keep-intermediates", "--keep-logs",
               "--untrusted", "--color", "never", "main.tex"]
    result = subprocess.run(command, cwd=run, env=env, capture_output=True, text=True)
    (run / "compiler_stdout.txt").write_text(result.stdout, encoding="utf8", newline="\n")
    (run / "compiler_stderr.txt").write_text(result.stderr, encoding="utf8", newline="\n")
    summary = {"schema": "document-compile-run-v1", "engine": "Tectonic",
               "engine_version": version, "engine_basename": Path(args.engine).name,
               "pdflatex_available": shutil.which("pdflatex") is not None,
               "cached_resources_only": True, "untrusted_mode": True,
               "exit_code": result.returncode, "run_directory": run.relative_to(paper).as_posix(),
               "source_files": {name: digest(run / name) for name in source_names},
               "figure_files": {p.relative_to(run).as_posix(): digest(p)
                                for p in (run / "figures").rglob("*") if p.is_file()},
               "outputs": {}}
    if result.returncode == 0:
        for name in ["main.pdf", "main.bbl"]:
            output = run / name
            if not output.is_file() or not output.stat().st_size:
                raise RuntimeError("Compiler did not generate " + name)
            shutil.copy2(output, paper / name)
            summary["outputs"][name] = digest(output)
    (work / "latest_compile.json").write_text(json.dumps(summary, indent=2) + "\n",
                                             encoding="utf8", newline="\n")
    print("Document compile", version, "exit", result.returncode,
          "run", summary["run_directory"])
    for name, binding in summary["outputs"].items():
        print(name, binding["bytes"], "bytes; SHA256", binding["sha256"])
    # Raw diagnostic logs are temporary and may contain compiler-local paths.
    # Keep the console summary short, while retaining full logs under _compile.
    for line in (result.stdout + "\n" + result.stderr).splitlines():
        if "error:" in line or "Overfull" in line or "undefined" in line:
            print(line)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
