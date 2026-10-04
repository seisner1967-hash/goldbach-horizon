"""Render and inspect manuscript structure; no scientific calculation."""
import hashlib
import json
import math
import subprocess
from pathlib import Path

import pdfplumber
from PIL import Image, ImageDraw
from pypdf import PdfReader

root = Path(__file__).resolve().parent
pdf = root / 'output/pdf/goldbach_synthesis_v3.pdf'
qa = root / 'tmp/pdf_qa'
qa.mkdir(parents=True, exist_ok=True)
assert qa.resolve().is_relative_to(root.resolve())
for pattern in ['page-*.png', 'contact_*.png']:
    for previous_render in qa.glob(pattern):
        assert previous_render.is_file()
        previous_render.unlink()
poppler = Path(r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\poppler\Library\bin')
command = [str(poppler / 'pdftoppm.exe'), '-r', '100', '-png', str(pdf), str(qa / 'page')]
result = subprocess.run(command, capture_output=True, timeout=120)
assert result.returncode == 0, result.stderr.decode(errors='replace')
reader = PdfReader(pdf)
text = '\n\n'.join(page.extract_text() or '' for page in reader.pages)
(qa / 'extracted_text.txt').write_text(text, encoding='utf-8')
bad = []
with pdfplumber.open(pdf) as doc:
    for i, page in enumerate(doc.pages, 1):
        for char in page.chars:
            if char['x0'] < -0.5 or char['x1'] > page.width + 0.5 or char['top'] < -0.5 or char['bottom'] > page.height + 0.5:
                bad.append({'page': i, 'text': char['text'], 'box': [char['x0'], char['top'], char['x1'], char['bottom']]})
images = sorted(qa.glob('page-*.png'))
assert len(images) == len(reader.pages)
width, height = 315, 470
for start in range(0, len(images), 8):
    subset = images[start:start+8]
    canvas = Image.new('RGB', (4*width, 2*height), 'white')
    draw = ImageDraw.Draw(canvas)
    for i, path in enumerate(subset):
        with Image.open(path) as pic:
            pic.thumbnail((width-12, height-28))
            x = (i % 4)*width + (width-pic.width)//2
            y = (i // 4)*height + 23
            canvas.paste(pic.convert('RGB'), (x, y))
        draw.text(((i % 4)*width+12, (i // 4)*height+5), f'Page {start+i+1}', fill='black')
    canvas.save(qa / f'contact_{start+1:02d}.png')
log = (root / 'output/pdf/goldbach_synthesis_v3.log').read_text(encoding='utf-8', errors='replace')
report = {'schema': 'GOLDBACH_V3_PDF_DOCUMENT_QA', 'PDF_sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
          'page_count': len(reader.pages), 'A4': all(abs(float(p.mediabox.width)-595.28)<1 and abs(float(p.mediabox.height)-841.89)<1 for p in reader.pages),
          'encrypted': reader.is_encrypted, 'all_pages_have_text': all(bool(p.extract_text()) for p in reader.pages),
          'chars_outside_page': bad, 'missing_character_log': 'Missing character:' in log,
          'overfull_boxes_log': 'Overfull' in log, 'unresolved_references_log': 'undefined' in log.lower(),
          'render_exit_code': result.returncode, 'contact_sheets': [p.name for p in sorted(qa.glob('contact_*.png'))],
          'scope': 'PDF structure and rendered layout only; not mathematical verification.'}
(root / 'output/pdf/pdf_qa_v3.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps(report, ensure_ascii=False, indent=2))
