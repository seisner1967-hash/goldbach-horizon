"""Verify Git indexed blobs are the exact publication bytes, without filters."""
import json
import subprocess
from pathlib import Path

repo = Path(__file__).resolve().parent.parent
scopes = ['publications/2026-10-goldbach-synthesis-v3',
          'research/goldbach-synthesis-v3-20261004',
          'scripts/publish_goldbach_v3.py', 'scripts/restore_goldbach_v3.py',
          'scripts/verify_goldbach_v3_index.py']
result = subprocess.run(['git', '-c', 'core.excludesFile=', 'ls-files', '--stage', '-z', '--', *scopes],
                        cwd=repo, check=True, capture_output=True)
entries = []
for record in result.stdout.split(b'\0'):
    if not record:
        continue
    header, path = record.split(b'\t', 1)
    mode, oid, stage = header.decode('ascii').split()
    assert mode in {'100644', '100755'} and stage == '0'
    entries.append((path.decode('utf-8'), oid))
assert entries
paths = ''.join(path + '\n' for path, _ in entries).encode('utf-8')
hashes = subprocess.run(['git', 'hash-object', '--no-filters', '--stdin-paths'], cwd=repo,
                        input=paths, capture_output=True, check=True).stdout.decode('ascii').splitlines()
assert len(hashes) == len(entries)
assert all(expected == actual for (_, expected), actual in zip(entries, hashes)), 'Indexed bytes differ from working publication bytes'
tracked = {path for path, _ in entries}
pub = repo / 'research/goldbach-synthesis-v3-20261004'
manifest = json.loads((pub / 'ARCHIVE_MANIFEST.json').read_text(encoding='utf-8'))
for row in manifest['files'] + manifest.get('companion_files', []):
    paths = [row['published_path']] if row['storage'] == 'direct' else [p['path'] for p in row['payload']['parts']]
    assert all('research/goldbach-synthesis-v3-20261004/' + p in tracked for p in paths), row['path']
assert not manifest['omitted_files']
report = {'schema': 'GOLDBACH_V3_GIT_INDEX_BYTE_CHECK',
          'indexed_files_checked': len(entries), 'all_indexed_bytes_match_without_filters': True,
          'original_research_files_covered': manifest['file_count'],
          'companion_files_covered': len(manifest.get('companion_files', [])),
          'all_manifest_payload_paths_indexed': True, 'scientific_validation': 'None; Git and archival byte checks only.'}
print(json.dumps(report, indent=2))
