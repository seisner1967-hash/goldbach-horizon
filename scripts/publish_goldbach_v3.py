"""Preserve every research file, packing oversized payloads for GitHub.

This is an archival operation, not a mathematical or numerical validation.
"""
import argparse
import gzip
import hashlib
import json
import os
import shutil
from datetime import datetime, timezone
from pathlib import Path

LIMIT = 100 * 1024 * 1024
PART = 48 * 1024 * 1024


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


parser = argparse.ArgumentParser()
parser.add_argument('--source', type=Path, required=True)
parser.add_argument('--publication', type=Path, required=True)
parser.add_argument('--stage-only', action='store_true')
parser.add_argument('--companion', type=Path, action='append', default=[])
args = parser.parse_args()
source = args.source.resolve(strict=True)
publication = args.publication.resolve()
assert source.is_dir() and not publication.is_relative_to(source)
source_display = str(source)
if os.name == 'nt':
    source = Path('\\\\?\\' + str(source))
    publication = Path('\\\\?\\' + str(publication))
workspace = publication / 'workspace' / source.name
payloads = publication / 'payloads'
temporary = publication / '.publication-tmp'
for folder in (workspace, payloads, temporary):
    folder.mkdir(parents=True, exist_ok=True)
(publication / '.gitattributes').write_bytes(b'* -text\n')
(publication / '.gitignore').write_bytes(b'.publication-tmp/\n')
rows = []
packed = {}
total = 0
for src in sorted(source.rglob('*')):
    if not src.is_file():
        continue
    if src.is_symlink():
        raise RuntimeError(f'Research symlink requires explicit archival handling: {src}')
    relative = src.relative_to(source)
    size = src.stat().st_size
    sha = digest(src)
    total += size
    row = {'path': relative.as_posix(), 'bytes': size, 'sha256': sha}
    if size < LIMIT:
        dst = workspace / relative
        dst.parent.mkdir(parents=True, exist_ok=True)
        if not dst.exists() or dst.stat().st_size != size or digest(dst) != sha:
            shutil.copyfile(src, dst)
        assert dst.stat().st_size == size and digest(dst) == sha
        row.update(storage='direct', published_path=dst.relative_to(publication).as_posix())
    else:
        if sha not in packed:
            metadata_path = payloads / (sha + '.json')
            if metadata_path.exists():
                record = json.loads(metadata_path.read_text(encoding='utf-8'))
                assert record['original_bytes'] == size and record['original_sha256'] == sha
                assert all(digest(publication / part['path']) == part['sha256']
                           for part in record['parts'])
            else:
                # Already-compressed files are split directly; others get reproducible gzip.
                encoding = 'identity' if src.suffix.lower() in {'.gz', '.zip', '.xz', '.zst', '.7z'} else 'gzip'
                intermediate = temporary / (sha + '.gz')
                if encoding == 'gzip':
                    with src.open('rb') as inp, intermediate.open('wb') as raw:
                        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0, compresslevel=6) as out:
                            shutil.copyfileobj(inp, out, 4 * 1024 * 1024)
                    packed_source = intermediate
                else:
                    packed_source = src
                parts = []
                with packed_source.open('rb') as inp:
                    number = 0
                    while True:
                        block = inp.read(PART)
                        if not block:
                            break
                        number += 1
                        dst = payloads / (sha + f'.{encoding}.part{number:03d}')
                        dst.write_bytes(block)
                        parts.append({'path': dst.relative_to(publication).as_posix(),
                                      'bytes': len(block), 'sha256': hashlib.sha256(block).hexdigest()})
                record = {'encoding': encoding, 'original_bytes': size,
                          'original_sha256': sha, 'parts': parts}
                metadata_path.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
                if encoding == 'gzip':
                    assert intermediate.resolve().parent == temporary.resolve()
                    intermediate.unlink()
            packed[sha] = record
            print(json.dumps({'packed_original_bytes': size, 'original_sha256': sha,
                              'part_count': len(record['parts'])}), flush=True)
        row.update(storage='packed', payload=packed[sha])
    rows.append(row)
companions = []
for src in args.companion:
    src = src.resolve(strict=True)
    assert src.is_file() and src.stat().st_size < LIMIT
    dst = publication / 'workspace' / src.parent.name / src.name
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    sha = digest(src)
    assert digest(dst) == sha
    companions.append({'root_name': src.parent.name, 'path': src.name,
                       'bytes': src.stat().st_size, 'sha256': sha,
                       'storage': 'direct', 'published_path': dst.relative_to(publication).as_posix()})
manifest = {'schema': 'GOLDBACH_V3_BYTE_EXACT_RESEARCH_ARCHIVE',
            'created_at_utc': datetime.now(timezone.utc).isoformat(),
            'source_root_name': source.name, 'historical_source_root': source_display,
            'file_count': len(rows), 'original_bytes': total,
            'omitted_files': [], 'normalization': 'none; publication .gitattributes uses -text',
            'scope': 'All files recursively under the engineering research workspace, including failed attempts and receipts.',
            'scientific_validation': 'None performed by this archival script.',
            'files': rows, 'companion_files': companions}
name = 'ARCHIVE_STAGE_MANIFEST.json' if args.stage_only else 'ARCHIVE_MANIFEST.json'
(publication / name).write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
if not args.stage_only:
    stage = publication / 'ARCHIVE_STAGE_MANIFEST.json'
    assert stage.parent == publication
    stage.unlink(missing_ok=True)
print(json.dumps({'manifest': name, 'files': len(rows), 'original_bytes': total,
                  'oversized_original_files': sum(x['storage'] == 'packed' for x in rows),
    'unique_packed_payloads': len(packed), 'omitted_files': 0}), flush=True)
