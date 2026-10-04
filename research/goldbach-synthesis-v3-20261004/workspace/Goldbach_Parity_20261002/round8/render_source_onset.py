from pathlib import Path
import hashlib
import json
import pypdfium2 as pdfium
from pypdf import PdfReader

source = Path(r'D:\Users\Utilisateur\Downloads\goldbach_synthesis.pdf')
output = Path(__file__).resolve().parent
reader = PdfReader(source)
selected = [31, 32, 35]
pdf = pdfium.PdfDocument(str(source))
receipt = {'source': str(source), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'page_count': len(reader.pages), 'pages': []}
for index in selected:
    png = output / f'source_onset_page{index+1}.png'
    txt = output / f'source_onset_page{index+1}.txt'
    page = pdf[index]
    bitmap = page.render(scale=1.7)
    bitmap.to_pil().save(png)
    txt.write_text(reader.pages[index].extract_text() or '', encoding='utf-8')
    receipt['pages'].append({'physical_page': index+1, 'png': png.name, 'png_sha256': hashlib.sha256(png.read_bytes()).hexdigest(), 'text': txt.name, 'text_sha256': hashlib.sha256(txt.read_bytes()).hexdigest()})
    print(f'Rendered physical page {index+1}')
    bitmap.close()
    page.close()
pdf.close()
(output / 'source_onset_render_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
