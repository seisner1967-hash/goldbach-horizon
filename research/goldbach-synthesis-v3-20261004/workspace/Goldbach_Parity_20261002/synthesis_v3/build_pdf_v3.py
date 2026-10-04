"""Export the standalone V3 manuscript using the already installed TeX engine."""
import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path(__file__).resolve().parent
source = root / 'goldbach_synthesis_v3.tex'
out = root / 'output/pdf'
out.mkdir(parents=True, exist_ok=True)
engine = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Research_20260930\tools\tectonic.exe')
env = dict(os.environ)
env['TECTONIC_CACHE_DIR'] = r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Final_20261001\tex_cache'
env['FONTCONFIG_FILE'] = str(root / 'fontconfig.xml')
command = [str(engine), '--only-cached', '--untrusted', '--keep-logs',
           '--keep-intermediates', '--outdir', str(out), str(source)]
started = datetime.now(timezone.utc).isoformat()
result = subprocess.run(command, env=env, capture_output=True, timeout=120)
finished = datetime.now(timezone.utc).isoformat()
(out / 'tectonic_stdout.log').write_bytes(result.stdout)
(out / 'tectonic_stderr.log').write_bytes(result.stderr)
pdf = out / 'goldbach_synthesis_v3.pdf'
receipt = {
    'schema': 'GOLDBACH_V3_DOCUMENT_BUILD', 'started_at_utc': started,
    'finished_at_utc': finished, 'command': command, 'exit_code': result.returncode,
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'engine_sha256': hashlib.sha256(engine.read_bytes()).hexdigest(),
    'PDF_bytes': pdf.stat().st_size if pdf.exists() else None,
    'PDF_sha256': hashlib.sha256(pdf.read_bytes()).hexdigest() if pdf.exists() else None,
    'PDF_valid_for_this_source_build': result.returncode == 0 and pdf.exists(),
    'stdout_sha256': hashlib.sha256(result.stdout).hexdigest(),
    'stderr_sha256': hashlib.sha256(result.stderr).hexdigest(),
    'scientific_executions': 0,
    'scope': 'Document compilation only; no Lean, native coefficient checker or mathematical experiment.',
}
(out / 'build_receipt_v3.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print(json.dumps(receipt, indent=2))
if result.returncode:
    print(result.stderr.decode('utf-8', errors='replace')[-2000:])
raise SystemExit(result.returncode)
