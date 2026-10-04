"""Root verification of frozen author4 bytes/logs only, no Lean or arithmetic."""
import json,hashlib,re
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round19'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def save(p,d):
    with p.open('x',encoding='utf-8') as f: f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
manifest=read(R/'role4/manifest.json'); final=read(R/'role4/final_receipt.json')
assert sha(R/'role4/manifest.json')==final['manifest_sha256']=='62ae333e6376e4eceedd1fd61f85204f0844567f1cf1f8afcc0e0710d0a73996'
assert sha(R/'role4/final_receipt.json')=='502243fc6fd5954e1255bd0c70354f0511a618323fe71e68370179d546ec8ecb'
assert sha(R/'agent4_formalisation.md')==final['report_sha256']=='442a58cdec079b611a1be704f77dc729343e4a4a24cc526f601a280a7a5c068b'
for field in ['bindings','readonly_dependency_bindings','numeric_gate_bindings']:
    for rel,digest in manifest[field].items(): assert sha(B/rel)==digest,(field,rel)
attempts=read(R/'role4/build_receipt.json')['attempts']; assert len(attempts)==12
rows=[]; allowed={'propext','Classical.choice','Quot.sound'}; passprints=0
for i,row in enumerate(attempts,1):
    assert row['attempt']==i and row['phase']=='FINISHED'
    assert sha(Path(row['snapshot']))==row['snapshot_sha256']==row['source_sha256']
    assert sha(Path(row['builder_snapshot']))==row['builder_snapshot_sha256']
    assert sha(Path(row['started_receipt']))==row['started_receipt_sha256']
    assert sha(Path(row['log']))==row['log_sha256']
    assert sha(Path(row['compile_gate']))==row['compile_gate_sha256']
    assert row['compiler_sha256']=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
    for fld in ['dependency_bindings','numeric_bindings','new_import_bindings']:
        for rel,digest in row[fld].items(): assert sha(B/rel)==digest,(fld,rel)
    txt=Path(row['log']).read_text(encoding='utf-8')
    code=Path(row['snapshot']).read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|trustMe)\b',code)
    errors=re.findall(r'^.*?:\d+:\d+: error:.*$',txt,re.M)
    warnings=re.findall(r'^.*?:\d+:\d+: warning:.*$',txt,re.M)
    parsed=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",txt,re.S)
    if row['exit_code']==0:
        assert not errors and not warnings and 'sorryAx' not in txt
        assert sha(Path(row['olean']))==row['olean_sha256']
        for name,axs in parsed: assert set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',axs))<=allowed,(i,name,axs)
        passprints+=len(parsed)
    else: assert row['exit_code']==1 and errors
    rows.append({'attempt':i,'module':Path(row['source']).stem,'exit_code':row['exit_code'],
     'started_utc':row['started_utc'],'finished_utc':row['finished_utc'],
     'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],
     'error_headers':errors,'warning_headers':warnings,'internal_sorryAx_in_FAILED_log':'sorryAx' in txt,
     'axiom_print_entries':len(parsed)})
assert sum(x['exit_code']==0 for x in rows)==5 and sum(x['exit_code']==1 for x in rows)==7
assert passprints==160
modules=[]
for m in manifest['modules']:
    p=R/'role4'/m['module']; assert sha(p)==m['source_sha256']
    assert sha(p.with_suffix('.olean'))==m['olean_sha256']
    txt=p.read_text(encoding='utf-8')
    counts={k:len(re.findall(pat,txt,re.M)) for k,pat in {
     'theorems':r'^theorem\s+','definitions':r'^def\s+',
     'structures':r'^(?:@\[ext\]\s+)?structure\s+','prints':r'^#print axioms '}.items()}
    assert counts['theorems']==m['theorems_explicit'] and counts['definitions']==m['definitions']
    assert counts['structures']==m['structures'] and counts['prints']==len(m['axiom_prints'])
    for x in m['axiom_prints']: assert set(x['axioms'])<=allowed
    modules.append({'module':m['module'],'source_sha256':m['source_sha256'],'olean_sha256':m['olean_sha256'],**counts})
assert [sum(m[k] for m in modules) for k in ['theorems','definitions','structures','prints']]==[100,55,3,160]
obs={'status':'ROOT_VERIFIED_FROZEN_FINAL4_AUTHOR_PASS_ONLY_INDEPENDENT_JUDGE_PENDING',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'round':19,'node':'14.4',
 'checked_author_bindings':len(manifest['bindings']),'checked_readonly_dependencies':10,'checked_numeric_gate_bindings':26,
 'modules_FULL_root_read':modules,'actual_author_attempts':rows,'author_PASS':5,'author_FAIL_technical':7,
 'separate_preLean_launcher_parse_FAIL':1,'author_standard_axiom_prints':160,
 'manifest_display_truncation_resolved_by_compact_machine_read':True,
 'root_compiler_or_mathematical_producer_invocations':0,'official_Judge_counts_modified':False,'victory':False,
 'unpaid':manifest['unpaid']}
save(C/'messages/round19_final4_root_observation.json',obs)
feedback=C/'messages/round19_failure_feedback_in_progress.md'
with feedback.open('a',encoding='utf-8') as f:
    f.write('\n\n## FINAL4 : tous les échecs réels conservés\n\n')
    for row in rows:
        if row['exit_code']:
            f.write(f"Tentative {row['attempt']:02d} {row['module']} exit1, log SHA {row['log_sha256']}. ")
            f.write(' ; '.join(x.split('error:',1)[1].strip() for x in row['error_headers'])+'\n\n')
    f.write('Ces sept FAIL sont des erreurs de formalisation réparées, pas une preuve de petit résidu. Les cinq PASS prouvent seulement la reindexation/support et H8 exact. H7/H9, onset source, medium/long, Gamma, capacité et ledger entier restent impayés.\n')
cp=read(C/'checkpoint.json')
for row in cp['in_flight_executors']:
    if row['role']==3: row.update(agent='/root/round19_formal3_compile',status='actual_fresh_continuation_dispatched_under_concrete_rank_PASS_gate')
    if row['role']==4: row.update(agent=None,status='FINAL5authorPASS_all12actualattempts_root_verified_independent_Judge_pending')
cp['last_progress']+=' FrozenFINAL4 fullysource/log reviewed and all manifestbindings/deps/numeric bindings verified,5PASS100thm55defs3str160standardprints,7realtechnicalFAIL and1preLeanparseFAIL retained. Freshformal3continuation actuallyspawned, no oldrebuild/PASSreplay. Official30/507 remainunchanged,noWin.'
cp['previous_goal_turn_evidence'].append((C/'messages/round19_final4_root_observation.json').relative_to(B).as_posix())
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:obs[k] for k in ['status','checked_author_bindings','modules_FULL_root_read','author_PASS','author_FAIL_technical','author_standard_axiom_prints']},ensure_ascii=False,indent=2))
