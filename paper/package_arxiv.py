"""Package portable publication sources; no mathematical work is executed."""
from pathlib import Path
import gzip
import hashlib
import io
import json
import re
import tarfile

PAPER = Path(__file__).resolve().parent
members = {"main.tex", "main.bbl", "references.bib"}
pending = ["main.tex"]
while pending:
    name = pending.pop()
    source = (PAPER / name).read_text(encoding="utf8")
    for stem in re.findall(r"\\bibliographystyle\{([^{}]+)\}", source):
        style = stem + ".bst"
        if (PAPER / style).is_file():
            members.add(style)
    for stem in re.findall(r"\\input\{([^{}]+)\}", source):
        child = stem if stem.endswith(".tex") else stem + ".tex"
        assert not Path(child).is_absolute() and ".." not in Path(child).parts
        if child not in members:
            members.add(child)
            pending.append(child)
    for child in re.findall(r"\\includegraphics(?:\[[^]]*\])?\{([^{}]+)\}", source):
        if not Path(child).suffix:
            candidates = [child + ext for ext in (".pdf", ".png") if (PAPER / (child + ext)).is_file()]
            assert len(candidates) == 1
            child = candidates[0]
        assert not Path(child).is_absolute() and ".." not in Path(child).parts
        members.add(child)

buffer = io.BytesIO()
bindings = []
with tarfile.open(fileobj=buffer, mode="w", format=tarfile.PAX_FORMAT) as tar:
    for name in sorted(members):
        raw = (PAPER / name).read_bytes()
        info = tarfile.TarInfo(name)
        info.size = len(raw)
        info.mtime = 0
        info.mode = 0o644
        info.uid = info.gid = 0
        info.uname = info.gname = ""
        tar.addfile(info, io.BytesIO(raw))
        bindings.append({"path": name, "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)})
archive = PAPER / "arxiv_submission.tar.gz"
with archive.open("wb") as output:
    with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=0) as compressed:
        compressed.write(buffer.getvalue())
raw = archive.read_bytes()
result = {"schema": "portable-arxiv-source-bundle-v1", "author": "Durand Serge",
          "archive": "paper/arxiv_submission.tar.gz", "sha256": hashlib.sha256(raw).hexdigest(),
          "bytes": len(raw), "members": bindings,
          "scope": "Actual manuscript sources, compiled bibliography and figures; no caches or build intermediates"}
(PAPER / "arxiv_bundle_manifest.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf8", newline="\n")
print("Portable arXiv bundle:", len(members), "members;", len(raw), "bytes")
