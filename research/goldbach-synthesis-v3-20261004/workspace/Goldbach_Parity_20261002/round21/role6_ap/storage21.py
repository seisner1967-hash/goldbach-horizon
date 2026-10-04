"""NEW AP21 exclusive deterministic streamed artifact storage."""
from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def json_exclusive(path: Path, value: dict) -> None:
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, ensure_ascii=False, sort_keys=True, indent=2)
        handle.write("\n")


class Stream:
    def __init__(self, path: Path):
        self.path = path
        self.raw = path.open("xb")
        self.writer = gzip.GzipFile(fileobj=self.raw, mode="wb", mtime=0)
        self.digest = hashlib.sha256()
        self.count = 0

    def emit(self, value: dict) -> None:
        data = (json.dumps(value, ensure_ascii=False, sort_keys=True,
                           separators=(",", ":")) + "\n").encode("utf-8")
        self.writer.write(data)
        self.digest.update(data)
        self.count += 1

    def close(self) -> dict:
        self.writer.close()
        self.raw.close()
        return {"path": str(self.path), "sha256": sha256(self.path),
                "uncompressed_sha256": self.digest.hexdigest(),
                "records": self.count, "bytes": self.path.stat().st_size}
