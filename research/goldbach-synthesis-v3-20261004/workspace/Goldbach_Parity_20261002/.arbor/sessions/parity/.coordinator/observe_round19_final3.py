"""Root observes frozen author bytes/logs only; no compiler or arithmetic."""
import json, hashlib, re
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round19'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
final=read(R/'role3/final_receipt.json'); manifest=read(R/'role3/manifest.json')
assert sha(R/'role3/final_receipt.json')=='2b592e3dba7c2a84d7665b98be29d6233fc332f0f9164cad0e5c9e2018f2567e'
assert sha(R/'role3/manifest.json')==final['manifest_sha256']=='5628f07bb3edfcaa851b1e9e8b436fe09644ef66c0e5fbce69e67411c5b145b7'
assert sha(R/'agent3_formalisation.md')==final['report_sha256']=='4755d2b0a787b0df71071dd1d1bc126b9901b8be059ca833fd1d6f45a7dfadc2'
assert sha(R/'role3/build_receipt.json')==final['build_receipt_sha256']=='a9b9aab4de064d805184ea11242a3ba427dc5cce6b7a1142321ad53288e960b5'
for field in ('bindings','readonly_dependency_bindings','numeric_gate_bindings'):
    for rel,digest in manifest[field].items(): assert sha(B/rel)==digest,(field,rel)
attempts=read(R/'role3/build_receipt.json')['attempts']; assert len(attempts)==17
rows=[]; allowed={'propext','Classical.choice','Quot.sound'}; prints=0
for i,row in enumerate(attempts,1):
    assert row['attempt']==i and row['state']=='FINISHED'
    for key in ('source_capture','launcher_capture','authorization_capture','log'):
        assert sha(Path(row[key]))==row[key+'_sha256'],(i,key)
    assert sha(Path(row['authorization_path']))==row['authorization_sha256']
    assert row['source_capture_sha256']==row['source_sha256']
    assert row['lean_exe_sha256']=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
    for field in ('checked_numeric_inputs_sha256','readonly_imports_sha256'):
        for rel,digest in row[field].items(): assert sha(B/rel)==digest,(i,field,rel)
    txt=Path(row['log']).read_text(encoding='utf-8')
    code=Path(row['source_capture']).read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|trustMe)\b',code)
    errors=re.findall(r'^.*?:\d+:\d+: error:.*$',txt,re.M)
    warnings=re.findall(r'^.*?:\d+:\d+: warning:.*$',txt,re.M)
    parsed=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",txt,re.S)
    if row['exit_code']==0:
        assert not errors and 'sorryAx' not in txt
        assert not warnings or (i==11 and len(warnings)==3)
        for key in ('olean','preserved_olean'): assert sha(Path(row[key]))==row[key+'_sha256']
        for name,axs in parsed: assert set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',axs))<=allowed,(i,name,axs)
        prints+=len(parsed)
    else: assert row['exit_code']==1 and errors
    rows.append({'attempt':i,'module':row['module'],'exit_code':row['exit_code'],
      'started_utc':row['started_at_utc'],'finished_utc':row['finished_at_utc'],
      'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],
      'error_headers':errors,'warning_headers':warnings,
      'internal_sorryAx_in_FAILED_log':'sorryAx' in txt,'axiom_print_entries':len(parsed)})
assert sum(x['exit_code']==0 for x in rows)==6 and prints==108
modules=[]
for m in manifest['modules']:
    p=R/'role3'/m['module']; assert sha(p)==m['source_sha256']
    assert sha(p.with_suffix('.olean'))==m['olean_sha256']
    txt=p.read_text(encoding='utf-8')
    counts={k:len(re.findall(pattern,txt,re.M)) for k,pattern in {
      'theorems':r'^theorem\s+','definitions':r'^def\s+',
      'structures':r'^(?:@\[ext\]\s+)?structure\s+','prints':r'^#print axioms '}.items()}
    assert counts['theorems']==m['theorems_explicit'] and counts['definitions']==m['definitions']
    assert counts['structures']==m['structures'] and counts['prints']==len(m['axiom_prints'])
    for x in m['axiom_prints']: assert set(x['axioms'])<=allowed
    modules.append({'module':m['module'],'source_sha256':m['source_sha256'],'olean_sha256':m['olean_sha256'],**counts})
assert [sum(m[k] for m in modules) for k in ('theorems','definitions','structures','prints')]==[85,23,0,108]
obs={'status':'ROOT_VERIFIED_FROZEN_FINAL3_AUTHOR_PASS_ONLY_INDEPENDENT_JUDGE_PENDING',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'round':19,'node':'13.11',
 'checked_author_bindings':len(manifest['bindings']),
 'checked_readonly_dependencies':len(manifest['readonly_dependency_bindings']),
 'checked_numeric_gate_bindings':len(manifest['numeric_gate_bindings']),
 'modules_FULL_root_read':modules,'actual_author_attempts':rows,
 'author_PASS':6,'author_FAIL_technical':11,'author_standard_axiom_prints':108,
 'full_current_final_source_and_report_reads':['e31218','a338d6','c17bc8','6a0991','f3906b','ed6a50','d266ed'],
 'root_compiler_or_mathematical_producer_invocations':0,
 'official_Judge_counts_modified':False,'victory':False,'unpaid':manifest['unpaid']}
with (C/'messages/round19_final3_root_observation.json').open('x',encoding='utf-8') as f:
    f.write(json.dumps(obs,ensure_ascii=False,indent=2)+'\n')
with (C/'messages/round19_failure_feedback_in_progress.md').open('a',encoding='utf-8') as f:
    f.write('\n\n## FINAL3 : onze échecs techniques effectivement conservés\n\n')
    for row in rows:
        if row['exit_code']:
            f.write(f"Tentative {row['attempt']:02d} {row['module']} exit1, log SHA {row['log_sha256']}. ")
            f.write(' ; '.join(x.split('error:',1)[1].strip() for x in row['error_headers'])+'\n\n')
    f.write('Aucun de ces FAIL techniques ne prouve un obstacle arithmétique. Les six PASS sont auxiliaires ; K14/source AP/K18/Γ_rank/capacité/ledger entier restent ouverts.\n')
cp=read(C/'checkpoint.json')
cp['phase']='ROUND19_ALL_FINAL_AUTHOR_RESULTS_ROOT_VERIFIED_INDEPENDENT_JUDGE_FREEZE_PENDING'
for row in cp['in_flight_executors']:
    if row['role']==3: row.update(agent=None,status='FINAL6authorPASS_all17attempts_root_verified_Judge_pending')
cp['last_progress']+=' FrozenFINAL3 fullsources/report/actualFAILlogs read; all131bindings/4readonlydeps/30numericbindings verified,6authorPASS85thm23defs108prints/11technicalFAIL,3benignwarnings. All11author modules now frozen, independentJudge pending; official30/507 unchanged, noWin.'
cp['previous_goal_turn_evidence'].append((C/'messages/round19_final3_root_observation.json').relative_to(B).as_posix())
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:obs[k] for k in ('status','checked_author_bindings','modules_FULL_root_read','author_PASS','author_FAIL_technical','author_standard_axiom_prints')},indent=2))
