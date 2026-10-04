"""NEW composite20 durable complete catalogs; no implicit mathematical execution."""
from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path


def file_info(path: Path) -> dict:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": digest.hexdigest()}


def binary_catalog(path: Path, payload: bytes | bytearray, semantics: dict) -> dict:
    raw_hash = hashlib.sha256(payload).hexdigest()
    with path.open("xb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as writer:
            writer.write(payload)
    return {**file_info(path), "uncompressed_sha256": raw_hash,
            "uncompressed_bytes": len(payload), "semantics": semantics}


class JsonCatalog:
    def __init__(self, path: Path):
        self.path = path
        self.raw = path.open("xb")
        self.writer = gzip.GzipFile(fileobj=self.raw, mode="wb", mtime=0)
        self.digest = hashlib.sha256()
        self.count = 0

    def put(self, record: dict | list) -> int:
        position = self.count
        encoded = (json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n").encode("utf8")
        self.writer.write(encoded)
        self.digest.update(encoded)
        self.count += 1
        return position

    def close(self) -> dict:
        self.writer.close()
        self.raw.close()
        return {**file_info(self.path), "records": self.count,
                "uncompressed_sha256": self.digest.hexdigest(), "index_base": 0,
                "format": "gzip UTF8 JSON Lines, all positions retained"}
