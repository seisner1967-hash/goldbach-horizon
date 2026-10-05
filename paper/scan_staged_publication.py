"""Check the explicitly staged publication for portable paths and secret patterns.

This is a publication gate, not a mathematical audit. It reads Git's index and
does not modify Git, source artifacts, credentials, or mathematical credit.
"""
from pathlib import Path
import argparse
import io
import json
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, check=True).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--forbidden-word", action="append", default=[])
    parser.add_argument("--report", action="store_true")
    args = parser.parse_args()
    paths = [x.decode("utf8") for x in git("diff", "--cached", "--name-only", "-z").split(b"\0") if x]
    findings = []
    author_email = "seisner1967@gmail.com"
    patterns = {
        "absolute_drive_path": r"(?i)(?<!\w)[a-z]:[\\/](?=[A-Za-z_.-])",
        "home_path": r"(?i)(?:[a-z]:[\\/]Users[\\/]|/(?:home|Users)/)[A-Za-z_.-]",
        "secret_pattern": r"(?:sk-[A-Za-z0-9_-]{20,}|gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|AKIA[A-Z0-9]{16}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----)",
    }
    text_suffixes = {".tex", ".bbl", ".bib", ".bst", ".json", ".csv", ".py", ".md", ".cff", ".toml", ".txt"}

    def scan_text(label, text):
        for kind, expression in patterns.items():
            if re.search(expression, text):
                findings.append({"path": label, "kind": kind})
        if any(word.lower() in text.lower() for word in args.forbidden_word):
            findings.append({"path": label, "kind": "forbidden_machine_identifier"})
        emails = set(re.findall(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b", text))
        if emails - {author_email}:
            findings.append({"path": label, "kind": "email_requires_review"})

    def scan_payload(label, raw):
        path = Path(label)
        if path.suffix.lower() == ".pdf":
            from pypdf import PdfReader
            reader = PdfReader(io.BytesIO(raw))
            text = "\n".join(page.extract_text() or "" for page in reader.pages)
            text += "\n" + str(dict(reader.metadata or {}))
            scan_text(label, text)
        elif label.endswith(".tar.gz"):
            with tarfile.open(fileobj=io.BytesIO(raw), mode="r:gz") as archive:
                for member in archive.getmembers():
                    if not member.isfile() or Path(member.name).is_absolute() or ".." in Path(member.name).parts:
                        findings.append({"path": label, "kind": "nonportable_archive_member"})
                        continue
                    scan_payload(label + "::" + member.name, archive.extractfile(member).read())
        elif path.suffix.lower() in text_suffixes or path.name == ".gitattributes":
            scan_text(label, raw.decode("utf8"))

    for name in paths:
        path = Path(name)
        if name not in {"README.md", "CITATION.cff", ".gitattributes", "AXIOMS.md"} and not name.startswith("paper/"):
            findings.append({"path": name, "kind": "outside_publication_scope"})
        if any(part in {"_compile", "_render", ".lake", "cache", "__pycache__", "build"} for part in path.parts):
            findings.append({"path": name, "kind": "build_or_cache_path"})
        if path.suffix in {".aux", ".log", ".out", ".blg", ".fls", ".fdb_latexmk", ".pyc", ".xdv"}:
            findings.append({"path": name, "kind": "build_intermediate"})
        raw = git("show", ":" + name)
        if len(raw) > 50_000_000:
            findings.append({"path": name, "kind": "oversize"})
        if raw != (ROOT / name).read_bytes():
            findings.append({"path": name, "kind": "index_worktree_byte_difference"})
        scan_payload(name, raw)
    if git("diff", "--cached", "--name-only", "--diff-filter=D").strip():
        findings.append({"kind": "deleted_existing_file"})
    original = git("show", "f7e1fda19a9781b6f4ae6ebcae1dfc81b1b41460:README.md")
    new = git("show", ":README.md")
    if not new.endswith(original) or len(new[:-len(original)].splitlines()) > 50:
        findings.append({"kind": "README_preservation_or_header_limit"})
    result = {"schema": "staged-publication-scan-v1", "status": "PASS" if not findings else "FAIL",
              "scope": "Index content, PDF text/metadata, archive members, additive paths, README bytes and size limits",
              "staged_file_count": len(paths), "maximum_file_bytes": 50_000_000,
              "allowed_author_email": author_email, "findings": findings,
              "limitations": "Pattern and document checks do not prove absence of every possible secret."}
    if args.report:
        (ROOT / "paper/STAGED_FILE_REVIEW.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf8", newline="\n")
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if not findings else 1)


if __name__ == "__main__":
    main()
