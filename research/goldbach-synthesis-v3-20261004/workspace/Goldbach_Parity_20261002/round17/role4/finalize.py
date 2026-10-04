import sys, json, hashlib, re
from pathlib import Path
from datetime import datetime, timezone
sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
BASE = W.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
build = json.loads((W/'build_receipt.json').read_text(encoding='utf-8'))
targets = {'FourFormRoots':8, 'PowersetMoment':11, 'FourFormTruncation':13, 'FourFormCollisionLoss':16}
modules = []
allowed = {'propext','Classical.choice','Quot.sound'}
for stem, number in targets.items():
    src = W/(stem+'.lean')
    txt = src.read_text(encoding='utf-8')
    decls = re.findall(r'^(def|theorem|lemma|instance)\s+(\w+)',txt,re.M)
    printed = re.findall(r'^#print axioms (\w+)',txt,re.M)
    assert {n for _,n in decls} == set(printed) and len(decls)==len(printed)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',txt)
    attempt = next(a for a in build['attempts'] if a['attempt']==number)
    assert attempt['exit_code']==0
    assert src.read_bytes()==Path(attempt['snapshot']).read_bytes()
    assert sha(src)==attempt['source_sha256']
    assert sha(W/(stem+'.olean'))==attempt['olean_sha256']
    log = Path(attempt['log']).read_text(encoding='utf-8')
    assert 'error:' not in log and 'warning:' not in log
    ax = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log,re.S)
    ax += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(ax)==len(decls)
    for name,values in ax:
        used = {v.strip() for v in values.split(',') if v.strip()}
        assert used<=allowed, (name,used)
    modules.append({'source':str(src),'source_sha256':sha(src),'olean':str(W/(stem+'.olean')),
      'olean_sha256':sha(W/(stem+'.olean')),'success_attempt':number,'declarations':[{'kind':k,'name':n} for k,n in decls],
      'theorems':sum(k in {'theorem','lemma'} for k,n in decls),'defs':sum(k=='def' for k,n in decls),
      'instances':sum(k=='instance' for k,n in decls),'axioms_printed':len(ax)})
for attempt in build['attempts']:
    assert sha(Path(attempt['snapshot']))==attempt['snapshot_sha256']==attempt['source_sha256']
    assert sha(Path(attempt['log']))==attempt['log_sha256']
    if attempt['olean']:
        assert sha(Path(attempt['olean']))==attempt['olean_sha256']
dep_source = BASE/'round17'/'role3'/'SelbergFourForms.lean'
dep_olean = dep_source.with_suffix('.olean')
assert sha(dep_source)=='b1b658aa92f8e02cef29667e9e60b763ca3ef57bb25dcbc8aa9c50ba33591ce1'
assert sha(dep_olean)=='9639c1f7ae9eb03d07c1de2fd79cdea4dd503d29716e5de3adb4085de21fc46c'
report = BASE/'round17'/'agent4_formalisation.md'
assert report.exists()
files = sorted(p for p in W.iterdir() if p.is_file() and p.name!='final_receipt.json')
receipt = {'status':'FINAL_PASS_PARTIAL','timestamp_utc':datetime.now(timezone.utc).isoformat(),
  'score':0,'victory':False,'source_onset':'log N >= 10^24, not instantiated by finite tests',
  'runtime':'Lean 4.15.0','ownership':['round17/role4/**','round17/agent4_formalisation.md'],
  'old_Lean_rebuilds':0,'old_numeric_bank_reruns':0,'protected_archive_claim':'799 protected by root preflight; no old path written by role4',
  'modules':modules,'totals':{'modules':len(modules),'theorems':sum(m['theorems'] for m in modules),
    'defs':sum(m['defs'] for m in modules),'instances':sum(m['instances'] for m in modules),
    'axioms_printed':sum(m['axioms_printed'] for m in modules)},
  'attempts':len(build['attempts']),'exit_zero':sum(a['exit_code']==0 for a in build['attempts']),
  'exit_nonzero':sum(a['exit_code']!=0 for a in build['attempts']),
  'allowed_axioms':sorted(allowed),'build_receipt_sha256':sha(W/'build_receipt.json'),
  'fresh_dependency':{'source':str(dep_source),'source_sha256':sha(dep_source),'olean':str(dep_olean),
    'olean_sha256':sha(dep_olean),'rebuilt_by_role4':False,'dependency_declarations_recounted':False},
  'report':str(report),'report_sha256':sha(report),
  'bindings':[{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size} for p in files],
  'not_proved_in_Lean':['analytic prime log sum input','Mertens lower bound log y',
    'totient price for collision loss','CRT +1 bound','C6 total source weighted sum and onset',
    'T_S and T_A payments','prime availability','single-consumption global capacity','Goldbach target']}
(W/'final_receipt.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'report_sha256':sha(report),'receipt_sha256':sha(W/'final_receipt.json'),
  'totals':receipt['totals'],'attempts':receipt['attempts'],'exit_zero':receipt['exit_zero'],
  'exit_nonzero':receipt['exit_nonzero']},ensure_ascii=False))
