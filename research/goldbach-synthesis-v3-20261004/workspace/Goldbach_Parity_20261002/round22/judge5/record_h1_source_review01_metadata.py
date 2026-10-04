"""Read/copy/catalogue metadata only. No Lean, numeric bank, probe, or installation."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
B = OWN.parent.parent
ROLE4 = B / "round22" / "role4"
H1 = ROLE4 / "h1_contour"
OUT = OWN / "h1_source_review01"
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib\Mathlib")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_new(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def active_text(source):
    result, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif quoted:
            if source[index] == "\\":
                result.extend("  ")
                index += 2
            elif source[index] == '"':
                quoted = False
                result.append(" ")
                index += 1
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            result.extend(" " * (end - index))
            index = end
        elif source[index] == '"':
            quoted = True
            result.append(" ")
            index += 1
        else:
            result.append(source[index])
            index += 1
    if depth or quoted:
        raise RuntimeError("Unclosed comment/string in inspected source")
    return "".join(result)


def main():
    receipt_path = H1 / "read_receipts22_v3.json"
    author_receipt = json.loads(receipt_path.read_text(encoding="utf-8-sig"))
    expected = {Path(row["path"]): row["sha256"] for row in author_receipt["source_bindings"]}
    expected[H1 / "ZetaEulerDerivative22.lean"] = "fe51d8956fecabaa09063ce31543b91946cc3fae1fd2e3ffadd4fc639be39520"
    for row in author_receipt["candidate_gamma_dependencies_NOT_STAGED"]:
        expected[Path(row["path"])] = row["sha256"]
    records = [
        (H1 / "MellinThermal22.lean", "MAIN_H1_SOURCE", "5b86af", 12),
        (H1 / "MellinThermalInversion22.lean", "MAIN_H1_SOURCE", "9815ef", 4),
        (H1 / "ZetaEulerDirect22.lean", "MAIN_H1_SOURCE", "4ab649", 5),
        (H1 / "ZetaReflection22.lean", "MAIN_H1_SOURCE", "4797e1", 7),
        (H1 / "ZetaEulerDerivative22.lean", "MAIN_H1_SOURCE", "f04645", 14),
        (ROLE4 / "GammaDerivative22.lean", "PENDING_GAMMA_DEPENDENCY_SOURCE", "ff5858", 8),
        (ROLE4 / "GammaBoxBounds22.lean", "PENDING_GAMMA_DEPENDENCY_SOURCE", "23572f", 12),
        (ROLE4 / "GammaContourComponent22.lean", "PENDING_GAMMA_DEPENDENCY_SOURCE", "eb1c5c", 11),
        (ROLE4 / "revision02" / "GammaPrerequisites22.lean", "ALREADY_INDEPENDENT_BATCH02_PASS_DEPENDENCY", "21d3da", 23)
    ]
    for path, _, _, _ in records:
        if sha(path) != expected[path]:
            raise RuntimeError("Source changed since supplied binding: " + str(path))
    if sha(H1 / "api_plan22.md") != author_receipt["plan_sha256"]:
        raise RuntimeError("API plan changed since author v3 binding")
    OUT.mkdir(exist_ok=False)
    copies = OUT / "source_copies"
    copies.mkdir(exist_ok=False)
    rows = []
    for path, role, chunk, count in records:
        payload = path.read_bytes()
        capture = copies / path.name
        with capture.open("xb") as stream:
            stream.write(payload)
        text = active_text(payload.decode("utf-8-sig"))
        declarations = [{"kind": kind, "qualified_name": "GoldbachContinuous22." + name}
                        for kind, name in re.findall(r"(?m)^\s*(def|theorem)\s+([^\s({:]+)", text)]
        prints = re.findall(r"(?m)^\s*#print\s+axioms\s+(\S+)", text)
        forbidden = sorted(set(re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", text)))
        if len(declarations) != count or [r["qualified_name"] for r in declarations] != prints or forbidden:
            raise RuntimeError("Declaration/print/source-token review mismatch: " + str(path))
        rows.append({"source": str(path), "source_sha256": sha(path), "bytes": len(payload),
                     "review_copy": str(capture), "review_copy_sha256": sha(capture),
                     "source_scope": "FULL", "source_chunk": chunk, "role": role,
                     "imports": re.findall(r"(?m)^\s*import\s+(\S+)", text),
                     "declarations": declarations, "qualified_prints": prints,
                     "theorem_count": sum(r["kind"] == "theorem" for r in declarations),
                     "definition_count": sum(r["kind"] == "def" for r in declarations),
                     "forbidden_tokens": forbidden,
                     "actual_print_axioms_output_exists_for_this_review": False})
    docs = [
        (H1 / "api_plan22.md", "FULL", "c50c3e"),
        (receipt_path, "FULL", "53188b"),
        (H1 / "psi_c5_subcontract22.md", "FULL", "e54f65"),
        (B / "round22" / "role1_bridge" / "contour_formula22.md", "FULL", "cbb518"),
        (B / "round22" / "role1_bridge" / "lean_obligations22.md", "FULL", "60a438")
    ]
    apis = [
        ("NumberTheory/EulerProduct/ExpLog.lean", "FULL", "bc9f8c"),
        ("NumberTheory/LSeries/RiemannZeta.lean", "FULL", "f21b90"),
        ("Analysis/MellinInversion.lean", "FULL", "1b3e5b"),
        ("Analysis/MellinTransform.lean", "TARGETED_LINES_1_185", "1b710c"),
        ("Analysis/Calculus/SmoothSeries.lean", "TARGETED_LINES_70_95", "fe3bc8"),
        ("NumberTheory/EulerProduct/Basic.lean", "DECLARATION_SEARCH_AND_CONTEXT_ONLY_NOT_FULL", "3b5a98/ba3a5e"),
        ("Data/Complex/Abs.lean", "TARGETED_LINES_293_302", "9320dc"),
        ("Analysis/SpecialFunctions/Trigonometric/Complex.lean", "TARGETED_LINES_1_51", "6495d7"),
        ("Analysis/Calculus/Deriv/Basic.lean", "TARGETED_LINES_559_569", "4c4ece"),
        ("Analysis/SpecialFunctions/ExpDeriv.lean", "DECLARATION_SEARCH_LINES_115_123_NOT_FULL", "9de4ed")
    ]
    read_rows = [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk}
                 for path, scope, chunk in docs]
    api_rows = [{"path": str(CACHE / relative), "sha256": sha(CACHE / relative),
                 "scope": scope, "chunk": chunk} for relative, scope, chunk in apis]
    main_rows = [r for r in rows if r["role"] == "MAIN_H1_SOURCE"]
    pending_gamma = [r for r in rows if r["role"] == "PENDING_GAMMA_DEPENDENCY_SOURCE"]
    review = {
        "schema": "ROUND22_JUDGE5_H1_SOURCE_REVIEW01",
        "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": "SOURCE_REVIEW_ONLY_NOT_PREPARED_NOT_COMPILED",
        "sources": rows, "documents": read_rows, "independent_API_reads": api_rows,
        "author_API_read_receipts_reused_as_independent_reads": False,
        "author_v3_receipt_sha256": sha(receipt_path),
        "main_module_count": len(main_rows),
        "main_declaration_count": sum(len(r["declarations"]) for r in main_rows),
        "main_theorem_count": sum(r["theorem_count"] for r in main_rows),
        "main_definition_count": sum(r["definition_count"] for r in main_rows),
        "pending_gamma_dependency_module_count": len(pending_gamma),
        "pending_gamma_dependency_declaration_count": sum(len(r["declarations"]) for r in pending_gamma),
        "already_PASS_dependency": "GammaPrerequisites22, independent closed batch02, 23 declarations; no new credit",
        "source_lexical_scope": "Nested comments and ordinary strings excluded; exact future #print coverage for inspected sources. This is metadata parsing, not elaboration or generated axiom output.",
        "source_copies_scope": "Review evidence copies only; not compilation staging, not PREPARED, no complete transitive source/olean binding",
        "metadata_read_incidents": [
            "fa21b2 declaration-search packet was truncated and named absent guessed Log/Summable.lean; not FULL and not a compiler failure. Corrected actual ExpLog FULLbc9f8c, RiemannZeta FULLf21b90, MellinInversion FULL1b3e5b and targeted SmoothSeries fe3bc8."
        ],
        "transitive_import_graph_closed": False, "compiler_invocations": 0,
        "mathematical_numeric_invocations": 0, "numeric_bank_created_or_replayed": False,
        "gate_created": False, "compiler_PASS_awarded": False,
        "official_counter_changed": False, "H1_C3_certified": False,
        "global_trace_certified": False, "D_N_paid": False, "victory": False
    }
    write_new(OUT / "read_catalog_receipt.json", review)
    print(json.dumps({"status": review["status"], "main_modules": review["main_module_count"],
                      "main_declarations": review["main_declaration_count"],
                      "pending_gamma_declarations": review["pending_gamma_dependency_declaration_count"],
                      "review_copies": len(rows), "receipt_sha256": sha(OUT / "read_catalog_receipt.json"),
                      "compiler_invocations": 0, "mathematical_numeric_invocations": 0, "victory": False}))


if __name__ == "__main__":
    main()
