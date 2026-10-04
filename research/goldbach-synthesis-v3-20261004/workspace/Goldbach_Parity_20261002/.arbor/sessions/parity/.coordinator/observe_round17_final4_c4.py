"""Root binding/schema observation only; no mathematics producer or compiler."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from collections import Counter
import json, re
B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B/'.arbor/sessions/parity/.coordinator'
R = B/'round17'
def digest(p):
    with p.open('rb') as f:
        h = sha256()
        for block in iter(lambda:f.read(1024*1024), b''): h.update(block)
    return h.hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def save(p,j): p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
p = R/'role4/final_receipt.json'; r = read(p)
assert digest(p) == 'd26e732ec7a4f746689f8ebd43be53118a85f18c689b328e76ea8167846a74ec'
assert digest(Path(r['report'])) == r['report_sha256'] == '59a035188ecab816f3aaf70be0ce4efe4f2d0c4ed5779d9aba597ea429d3fa1c'
for f in r['bindings']:
    q = Path(f['path']); assert digest(q)==f['sha256'] and q.stat().st_size==f['bytes']
assert r['totals']==dict(modules=4,theorems=51,defs=17,instances=1,axioms_printed=69)
assert r['attempts']==16 and r['exit_zero']==5 and r['exit_nonzero']==11
allowed={'propext','Classical.choice','Quot.sound'}
for m in r['modules']:
    assert digest(Path(m['source']))==m['source_sha256'] and digest(Path(m['olean']))==m['olean_sha256']
    txt=Path(m['source']).read_text(encoding='utf-8')
    decls=re.findall(r'^(def|theorem|lemma|instance)\s+(\w+)',txt,re.M)
    assert decls==[(x['kind'],x['name']) for x in m['declarations']]
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',txt)
    log=(R/'role4'/f"attempt{m['success_attempt']:02d}.log").read_text(encoding='utf-8')
    assert not re.search(r'error:|warning:|sorryAx',log)
    ax=re.findall(r'depends on axioms: \[([^]]*)\]',log,re.S)
    ax+=['']*len(re.findall(r'does not depend on any axioms',log))
    assert len(ax)==m['axioms_printed']
    for a in ax: assert {x.strip() for x in a.split(',') if x.strip()}<=allowed
dep=r['fresh_dependency']
assert digest(Path(dep['source']))==dep['source_sha256'] and digest(Path(dep['olean']))==dep['olean_sha256']
assert not r['victory'] and r['score']==0
obs4=dict(status='ROOT_FROZEN_FINAL4_BINDINGS_VERIFIED',totals=r['totals'],bindings=len(r['bindings']),
          attempts=16,technical_exit1=11,exit0=5,report_sha256=r['report_sha256'],receipt_sha256=digest(p),
          new_Lean_compiled_by_root=False,root_observer_prior_exit1='axiom-print reader omitted declarations using no axioms; read-only parser repaired',analytic_prime_log_sum_input_remains=True,full_source_C4=False,victory=False)
save(C/'messages/round17_root_final4_observation.json',obs4)
A=R/'role6_c4'; p=A/'manifest.json'; manifest=read(p)
assert digest(p)=='9671e8f8c3ffb32101544103cf57056f6c643aed92d2e86ef4dfadc05b8d6198'
assert manifest['files']==len(manifest['sha256_relative_role6_c4'])==15
for rel,h in manifest['sha256_relative_role6_c4'].items(): assert digest(A/rel)==h
assert digest(R/manifest['report_relative_round17'])==manifest['report_sha256']=='e92c7d210b11743e0079166c29d47195e2ab7a4b36bf110ab0528b991e192bb0'
receipt=read(A/'final_receipt.json')
assert digest(A/'final_receipt.json')==manifest['receipt_sha256']=='e6b3d9f8d1d3dc3374b6be67368cd831f43e941f0dd354f3e365635eb8355e91'
for rel,h in receipt['own_assets_sha256'].items(): assert digest(A/rel)==h
assert receipt['canonical_attempts']==receipt['isolated_replays']==1 and receipt['real_failed_attempts']==receipt['post_replay_runs']==0
original=A/'moment.json'; copied=A/'isolated/moment.json'
assert original.read_bytes()==copied.read_bytes()
j=read(original); assert j==read(copied)
assert j['core_count']==len(j['rows'])==16
assert j['true_condition_cores']==[7,21,31,43,57,73]
assert j['false_condition_cores']==[13,19,33,37,39,51,61,67,69,79]
signs=Counter()
def certificates(x):
    if isinstance(x,dict):
        if {'sign','lower','upper'}<=x.keys():
            lo,hi=Fraction(x['lower']),Fraction(x['upper']); assert lo<=hi
            assert (lo>0 if x['sign']=='POSITIVE' else hi<0 if x['sign']=='NEGATIVE' else lo==hi==0 if x['sign']=='ZERO' else False)
            signs[x['sign']]+=1
        else:
            for v in x.values(): certificates(v)
    elif isinstance(x,list):
        for v in x: certificates(v)
certificates(j)
assert sum(signs.values())==j['new_interval_certificate_positions']==64
assert signs==Counter(POSITIVE=54,NEGATIVE=10)
for row in j['rows']:
    assert len(row['all16_subsets'])==16
    assert [s['natural_product'] for s in row['all16_subsets'] if s['cell'].startswith('TAIL')]==[105,210]
    assert len(row['head_products_support_inclusion'])==14
    assert row['markov_no_division_certificate']['sign']=='POSITIVE'
    assert row['observed_G_P_ge_half_Z'] and row['half_G_not_inferred_from_false_condition']
    assert row['source_C4_C6_U4_BV_not_applied']
initial=read(R/'numeric_manifest.json')
assert digest(R/'numeric_manifest.json')==j['initial_numeric_manifest_sha256']=='c6e1efe0ef1e4c2448bb9d53eb6df1635b29eb9a077723620ce62d4f45a6b1e4'
assert len(initial['sha256'])==33
for rel,h in initial['sha256'].items(): assert digest(R/rel)==h
obs6=dict(status='ROOT_FROZEN_C4_ANNEX_BINDINGS_AND_STORED_CERTIFICATES_VERIFIED',
          bindings=15,report_separate=True,cores=16,new_positions=64,signs=dict(signs),
          condition_true=j['true_condition_cores'],condition_false=j['false_condition_cores'],
          all_tails_retained=[105,210],unique_canonical_and_replay_exit0=True,copies_bytes_and_fields_identical=True,
          initial33_unchanged=True,initial390_not_recounted=True,numeric_or_sign_producer_reran_by_root=False,
          source_C4_C6_not_applied=True,report_sha256=manifest['report_sha256'],manifest_sha256=digest(p),
          receipt_sha256=manifest['receipt_sha256'],victory=False)
save(C/'messages/round17_root_final6_c4_observation.json',obs6)
p=C/'checkpoint.json'; cp=read(p)
cp['phase']='ROUND17_ALL_PRODUCER_FINALS_FROZEN_INDEPENDENT_JUDGE_ACTIVE'
cp['in_flight_executors']=['round17_judge: all FINALs received, independent freeze/audit and fresh five-module compilation active']
cp['next_focus']='Read the actual independent Judge17 final, close nodes13.9/14.2 with actual evidence, then fresh constraints/IDEATE18; A/S and global D_N remain unestimated.'
cp['last_progress']+=f" Root fully reads FINAL4 report, final collision module, build/finalizer and real failures9/10/12/14 plus final logs11/13/16; verifies all{obs4['bindings']} role4 bindings,51theorems17defs1instance69standardaxiomprints/16attempts11exit1/5exit0. Root fully reads new C4 numeric source/shared/run/replay/finalizer/report; verifies15 bindings plus report, one canonical and one unique existing copy identical,64 stored strict signs54POS10NEG separate390,6TRUE10FALSE conditions and retained105/210 tail. Initial33 remain fixed. Five new modules await independent Judge17 actual verdict; no root numerical, sign or compiler rerun. FullsourceC4/analytic prime-log input/Mertens/totient/CRT+1/C6/T_A/T_S/global remain open, no victory."
for rel in ['round17/agent4_formalisation.md','round17/role4/final_receipt.json','round17/agent6_c4.md','round17/role6_c4/manifest.json','round17/role6_c4/final_receipt.json','.arbor/sessions/parity/.coordinator/messages/round17_root_final4_observation.json','.arbor/sessions/parity/.coordinator/messages/round17_root_final6_c4_observation.json']:
    if rel not in cp['previous_goal_turn_evidence']:cp['previous_goal_turn_evidence'].append(rel)
save(p,cp)
report=B/'REPORT.md'
with report.open('a',encoding='utf-8') as f:
    f.write('\n### Gel des nouveaux modules17 et annexe de moment\n\nLes deux formaliseurs livrent cinq nouveaux modules : Selberg42 théorèmes/23 defs, racines et raccords quantitatifs51 théorèmes/17 defs/1 instance. Les producteurs ont conservé23 vrais exit1 techniques (12+11), sans les interpréter comme une déduction analytique impossible. Les journaux finaux ne contiennent que les axiomes standards et aucun sorry. Root a lu les sources finales, les corrections et journaux, puis vérifié les bindings sans compiler. Le minorant du vrai G garde l\'input analytique indépendant de somme logarithmique première et la perte de collisions explicite ; C4 source complet/C6/T_A/T_S/global restent ouverts. Le Juge indépendant reçoit tous les FINAL et prépare son audit unique et cinq compilations fraîches. Aucun cumul acquis nouveau avant son verdict.\n\nL\'annexe numérique nouvelle, distincte des33 bindings FINAL6 inchangés, vérifie le moment exact et garde toute la queue105/210 des16 sous-ensembles sur chacun des16 cœurs. Un canonique et un seul rejeu isolé exit0 donnent une copie identique. Ses64 certificats stricts (54POS,10NEG) sont séparés des390 premiers. Six conditions demi-moment sont vraies, dix fausses ; les16 marges de Markov restent positives. Le minorant fini G_P≥Z/2 est observé pour tous16, y compris les dix où sa condition suffisante échoue. Aucune borne source n\'est appliquée à N=10^8. Root vérifie les pièces et bornes stockées sans relancer les producteurs ou les signes. La victoire reste fausse.\n')
print(json.dumps(dict(final4=obs4,c4_annex=obs6),ensure_ascii=False))
