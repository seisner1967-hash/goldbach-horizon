from pathlib import Path
import re, sys, json
sys.dont_write_bytecode = True
p = Path(__file__).resolve().parent / 'SelbergFourForms.lean'
text = p.read_text(encoding='utf-8')
text = re.sub(r'^#print axioms .*\n', '', text, flags=re.M)
names = re.findall(r'^(?:lemma|theorem|def)\s+(\w+)', text, flags=re.M)
marker = 'end\nend GoldbachRound17.Selberg'
assert text.count(marker) == 1
text = text.replace(marker, '\n'.join('#print axioms ' + n for n in names) + '\n\n' + marker)
p.write_text(text, encoding='utf-8')
print(json.dumps({'axiom_prints': len(names)}))
