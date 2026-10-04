"""Freeze role3 outputs by reading existing attempts; never execute a proof again."""
import sys, hashlib, json, re, subprocess
from pathlib import Path
from datetime import datetime, timezone
sys.dont_write_bytecode=True
W=Path(__file__).resolve().parent; R=W.parents[1]
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
P=W/'final_receipt.json'; assert not P.exists(),'Final receipt already exists; no repeat'
src=W/'EulerAnchor.lean'; expected='88bbbb4d8e49cf2906ec3ae06ec7a9f4bcaf6e08ee811733f090fb084fce0285'; assert sha(src)==expected
s=src.read_text(encoding='utf-8-sig')
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s)
lemmas=re.findall(r'^(?:lemma|theorem)\s+(\w+)',s,re.M)
defs=re.findall(r'^noncomputable def\s+(\w+)',s,re.M)
assert len(lemmas)==27 and len(defs)==8
b=json.loads((W/'build_receipt.json').read_text(encoding='utf-8'))
assert len(b['attempts'])==13
for a in b['attempts']:
 for key in ['snapshot','log']:
  p=Path(a[key]);assert sha(p)==a[key+'_sha256']
 assert sha(Path(a['snapshot']))==a['source_sha256']
a=b['attempts'][-1];assert a['attempt']==13 and a['exit_code']==0 and a['source_sha256']==expected
assert Path(a['snapshot']).read_bytes()==src.read_bytes()
out=Path(a['log']).read_text(encoding='utf-8')
assert 'error:' not in out and 'warning:' not in out and 'sorryAx' not in out
ax=re.findall(r"'GoldbachRound16\.Anchor\.(\w+)' depends on axioms: \[([^]]+)\]",out)
assert set(n for n,_ in ax)==set(lemmas) and len(ax)==27
assert all(set(x.strip() for x in v.split(','))<= {'propext','Classical.choice','Quot.sound'} for _,v in ax)
LEAN=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
v=subprocess.run([str(LEAN),'--version'],capture_output=True,text=True,encoding='utf-8',errors='replace')
assert v.returncode==0 and '4.15.0' in v.stdout
inputs=[R/'round11'/'lean'/'ThreeAdicPrimePairing.lean',R/'round10'/'lean'/'ShortDivisorComplement.lean',R/'round13'/'role3'/'dependencies'/'ThreeAdicPrimePairing.lean',R/'round13'/'role3'/'dependencies'/'ThreeAdicPrimePairing.olean',R/'round13'/'role3'/'dependencies'/'ShortDivisorComplement.lean',R/'round13'/'role3'/'dependencies'/'ShortDivisorComplement.olean',R/'round16'/'role4'/'LeastMissingPrimeMargin.lean',R/'round16'/'role4'/'LeastMissingPrimeMargin.olean',R/'round16'/'role4'/'final_receipt.json',R/'round16'/'agent2_or_incidence.md']
assert inputs[0].read_bytes()==inputs[2].read_bytes() and inputs[1].read_bytes()==inputs[4].read_bytes()
assert sha(inputs[0])=='b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48'
assert sha(inputs[1])=='25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447'
assert sha(inputs[6])=='e1dbd4f8a68b433c4641c90d6eb12366e7084b0d8b7b7b045b8b11ebd41e6b4a'
assert sha(inputs[-1])=='f6f12c39afc445ce82482850c34482fa2450b9df1df7dbeef2089574b308128b'
report=R/'round16'/'agent3_formalisation.md'
files=sorted([p for p in W.iterdir() if p.is_file() and p!=P],key=lambda p:p.name)+[report]
bind=lambda p:{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
d={'status':'FINAL_ROLE3_CANONICAL_REAL_SINGULAR_SERIES_MARGIN_PARTIAL','frozen_utc':datetime.now(timezone.utc).isoformat(),'source':str(src),'source_sha256':expected,'olean':str(W/'EulerAnchor.olean'),'olean_sha256':sha(W/'EulerAnchor.olean'),'report_path':str(report),'report_sha256':sha(report),'compiler_version':v.stdout.strip(),'compiler_sha256':sha(LEAN),'mathlib_root':str(Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\mathlib')),'mathlib_commit':'9837ca9d65d9de6fad1ef4381750ca688774e608','theorem_count':27,'definition_count':8,'theorems':lemmas,'definitions':defs,'compilatory_invocations':13,'API_probe_invocations':1,'candidate_compilations':12,'actual_exit1_count':9,'actual_candidate_exit1_count':8,'PASS_attempts':[x['attempt'] for x in b['attempts'] if x['exit_code']==0],'last_attempt':13,'last_exit_code':0,'last_error_count':0,'last_warning_count':0,'banned_token_count':0,'axioms':['propext','Classical.choice','Quot.sound'],'old_rebuilds':0,'old_tests_replayed':False,'numeric_banks_replayed':False,'finalizer_proof_reexecuted':False,'version_read_calls_in_finalizer':1,'score':0,'victory':False,'source_enclosure_hypothesis':'2541/4096 <= GoldbachRound11.twinConstant','global_D_N_estimated':False,'prime_incidence_estimated':False,'semantics':'Canonical p0 via Nat.find among actual missing odd primes. True singularSeries and real tprod convergence, prefix cancellation, harmonic finite Euler lower bound, tail lower bound, then source-enclosure small cases; no availability or density assumed.','input_bindings':[bind(p) for p in inputs],'files':[bind(p) for p in files]}
P.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':d['status'],'source_sha256':expected,'report_sha256':sha(report),'receipt_sha256':sha(P),'bound_outputs':len(files),'input_bindings':len(inputs),'theorems':len(lemmas),'definitions':len(defs),'last_exit_code':0,'victory':False},ensure_ascii=False))
