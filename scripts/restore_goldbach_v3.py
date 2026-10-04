"""Restore a byte-exact research snapshot from the V3 publication manifest."""
import argparse
import gzip
import hashlib
import io
import json
import os
import shutil
from pathlib import Path


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


class PartsReader(io.RawIOBase):
    def __init__(self, paths):
        self.paths = iter(paths)
        self.current = None

    def readable(self):
        return True

    def readinto(self, buffer):
        while True:
            if self.current is None:
                try:
                    self.current = next(self.paths).open('rb')
                except StopIteration:
                    return 0
            count = self.current.readinto(buffer)
            if count:
                return count
            self.current.close()
            self.current = None

    def close(self):
        if self.current is not None:
            self.current.close()
        super().close()


parser = argparse.ArgumentParser()
parser.add_argument('publication', type=Path)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
publication = args.publication.resolve(strict=True)
output = args.output.resolve() if args.output else None
if os.name == 'nt':
    publication = Path('\\\\?\\' + str(publication))
    if output:
        output = Path('\\\\?\\' + str(output))
manifest = json.loads((publication / 'ARCHIVE_MANIFEST.json').read_text(encoding='utf-8'))
verified_parts = set()
restored = 0
for row in manifest['files'] + manifest.get('companion_files', []):
    if row['storage'] == 'direct':
        src = (publication / row['published_path']).resolve(strict=True)
        assert src.is_relative_to(publication)
        assert src.stat().st_size == row['bytes'] and digest(src) == row['sha256']
        reader = src.open('rb')
    else:
        payload = row['payload']
        paths = []
        for part in payload['parts']:
            path = (publication / part['path']).resolve(strict=True)
            assert path.is_relative_to(publication)
            if path not in verified_parts:
                assert path.stat().st_size == part['bytes'] and digest(path) == part['sha256']
                verified_parts.add(path)
            paths.append(path)
        raw = io.BufferedReader(PartsReader(paths))
        reader = gzip.GzipFile(fileobj=raw, mode='rb') if payload['encoding'] == 'gzip' else raw
    dst = None
    if output:
        dst = (output / row.get('root_name', manifest['source_root_name']) / row['path']).resolve()
        assert dst.is_relative_to(output)
        dst.parent.mkdir(parents=True, exist_ok=True)
        if dst.exists():
            assert dst.stat().st_size == row['bytes'] and digest(dst) == row['sha256'], 'Refusing to replace a different existing file'
            reader.close()
            restored += 1
            continue
        out = dst.open('xb')
    else:
        out = None
    h = hashlib.sha256()
    count = 0
    try:
        with reader:
            for block in iter(lambda: reader.read(4 * 1024 * 1024), b''):
                h.update(block)
                count += len(block)
                if out:
                    out.write(block)
    finally:
        if out:
            out.close()
    assert count == row['bytes'] and h.hexdigest() == row['sha256'], row['path']
    restored += 1
assert not manifest['omitted_files']
print(json.dumps({'schema': 'GOLDBACH_V3_ARCHIVE_RECONSTRUCTION_CHECK',
                  'files_checked_or_restored': restored,
                  'expected_file_count': manifest['file_count'] + len(manifest.get('companion_files', [])),
                  'original_bytes': manifest['original_bytes'], 'all_original_SHA256_match': True,
                  'output': str(output) if output else None,
                  'scientific_validation': 'No mathematical claim; archival byte verification only.'}, indent=2))
