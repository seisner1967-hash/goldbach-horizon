"""Check the staged V3.1 publication and numerical archive without native runs."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path


LIMIT = 100 * 1024 * 1024
DIRECTORIES = [
    "publications/2026-10-goldbach-synthesis-v3-1",
    "research/goldbach-numerical-20261004",
]
FILES = [".gitattributes", "README.md", "verify_goldbach_v3_1_index.py"]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--git", default="git", help="Git executable path")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent

    def git(*arguments, stdin=None):
        return subprocess.run(
            [args.git, *arguments], cwd=repo, input=stdin,
            capture_output=True, check=True,
        ).stdout

    expected = set(FILES)
    for scope in DIRECTORIES:
        directory = repo / scope
        require(directory.is_dir(), "Missing publication directory: " + scope)
        for path in directory.rglob("*"):
            if path.is_file():
                require(not path.is_symlink(), "Unsupported symlink: " + str(path))
                expected.add(path.relative_to(repo).as_posix())
    for path in expected:
        require((repo / path).is_file(), "Missing publication file: " + path)

    entries = []
    records = git("-c", "core.excludesFile=", "ls-files", "--stage", "-z",
                  "--", *DIRECTORIES, *FILES)
    for record in records.split(b"\0"):
        if not record:
            continue
        header, raw_path = record.split(b"\t", 1)
        mode, oid, stage = header.decode("ascii").split()
        path = raw_path.decode("utf-8")
        require(mode in {"100644", "100755"} and stage == "0",
                "Non-regular or unresolved indexed file: " + path)
        require("\n" not in path and "\r" not in path,
                "Unsupported newline in publication path")
        entries.append((path, oid))
    tracked = {path for path, _ in entries}
    require(tracked == expected,
            "Index coverage differs from publication files: " + json.dumps({
                "not_indexed": sorted(expected - tracked),
                "indexed_but_absent": sorted(tracked - expected),
            }))

    path_input = "".join(path + "\n" for path, _ in entries).encode("utf-8")
    hashes = git("hash-object", "--no-filters", "--stdin-paths",
                 stdin=path_input).decode("ascii").splitlines()
    require(len(hashes) == len(entries), "Git returned an incomplete hash list")
    differences = [path for (path, oid), actual in zip(entries, hashes)
                   if oid != actual]
    require(not differences,
            "Indexed bytes differ from raw working files: " + json.dumps(differences))

    oid_input = "".join(oid + "\n" for _, oid in entries).encode("ascii")
    blob_rows = git("cat-file", "--batch-check=%(objectname) %(objecttype) %(objectsize)",
                    stdin=oid_input).decode("ascii").splitlines()
    require(len(blob_rows) == len(entries), "Git returned incomplete blob sizes")
    largest_blob = 0
    for (path, oid), row in zip(entries, blob_rows):
        actual_oid, kind, size = row.split()
        size = int(size)
        require(actual_oid == oid and kind == "blob", "Unexpected indexed object: " + path)
        require(size == (repo / path).stat().st_size,
                "Indexed size differs from working file: " + path)
        require(size < LIMIT, "Indexed file exceeds the GitHub size limit: " + path)
        largest_blob = max(largest_blob, size)

    archive_scope = DIRECTORIES[1]
    archive = repo / archive_scope
    manifest_path = archive / "ARCHIVE_MANIFEST.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    require(not manifest["omitted_files"], "Archive manifest declares omissions")
    require(manifest["file_count"] == len(manifest["files"]),
            "Archive manifest file count mismatch")
    require(manifest["original_bytes"] == sum(row["bytes"] for row in manifest["files"]),
            "Archive manifest original byte count mismatch")
    originals = [row["path"] for row in manifest["files"]]
    require(len(originals) == len(set(originals)), "Duplicate archive original paths")
    verified_storage = {}

    def check_storage(relative, expected_bytes, expected_sha256):
        path = (archive / relative).resolve(strict=True)
        require(path.is_relative_to(archive.resolve()),
                "Archive storage escapes its subtree: " + relative)
        require(archive_scope + "/" + relative in tracked,
                "Manifest storage is not indexed: " + relative)
        binding = (expected_bytes, expected_sha256)
        if relative in verified_storage:
            require(verified_storage[relative] == binding,
                    "Conflicting storage bindings: " + relative)
            return
        require(path.stat().st_size == expected_bytes and sha256(path) == expected_sha256,
                "Archive storage does not match manifest: " + relative)
        verified_storage[relative] = binding

    for row in manifest["files"] + manifest.get("companion_files", []):
        if row["storage"] == "direct":
            check_storage(row["published_path"], row["bytes"], row["sha256"])
        elif row["storage"] == "packed":
            payload = row["payload"]
            require(payload["original_bytes"] == row["bytes"]
                    and payload["original_sha256"] == row["sha256"],
                    "Packed original binding mismatch: " + row["path"])
            require(payload["encoding"] in {"gzip", "identity"} and payload["parts"],
                    "Unsupported or empty packed payload: " + row["path"])
            for part in payload["parts"]:
                check_storage(part["path"], part["bytes"], part["sha256"])
        else:
            raise RuntimeError("Unsupported archive storage: " + row["storage"])

    print(json.dumps({
        "schema": "GOLDBACH_V3_1_GIT_INDEX_BYTE_CHECK",
        "scopes": DIRECTORIES + FILES,
        "indexed_files_checked": len(entries),
        "all_publication_files_indexed": True,
        "all_indexed_bytes_match_without_filters": True,
        "all_indexed_blob_sizes_below_100_mib": True,
        "largest_indexed_blob_bytes": largest_blob,
        "original_numerical_files_covered": manifest["file_count"],
        "companion_files_covered": len(manifest.get("companion_files", [])),
        "original_numerical_bytes": manifest["original_bytes"],
        "all_manifest_storage_paths_indexed": True,
        "all_manifest_storage_sha256_match": True,
        "archive_manifest_sha256": sha256(manifest_path),
        "scientific_validation": "None; Git and archival byte checks only. No native calculation rerun.",
    }, indent=2))


if __name__ == "__main__":
    main()
