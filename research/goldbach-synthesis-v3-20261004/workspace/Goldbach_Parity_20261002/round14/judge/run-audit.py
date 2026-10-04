"""Final round14 read-only audit. No producer, historical bank or Lean execution."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import ast, importlib.util, json
from datetime import datetime, timezone
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
spec = importlib.util.spec_from_file_location('round14_judge_frozen', HERE / 'verify-frozen.py')
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)
digest = verify.digest
manifest = HERE / 'input_sha256.json'
inputs = json.loads(manifest.read_bytes())
verify.verify_inputs(inputs)
before = verify.preservation(inputs)
def load(n): return json.loads((ROUND / n).read_bytes())
numeric = load('numeric_manifest.json')
assert digest(ROUND / 'numeric_manifest.json') == inputs['numeric_manifest_sha256']
assert numeric['status'] == 'FROZEN_NUMERICAL_INPUTS_TERMINATED'
assert numeric['file_count'] == len(numeric['sha256']) == 32
for name, expected in numeric['sha256'].items(): assert digest(ROUND / name) == expected, name
scripts = ('conservation.py', 'shared.py', 'coverage_checks.py', 'complement_checks.py',
    'prepare_candidates.py', 'coverage_pair_supplement.py', 'replay_checks.py', 'run_new.py',
    'role6/read_only_audit.py', 'role6/finalize.py')
for name in scripts: ast.parse((ROUND / name).read_text(encoding='utf-8'), filename=name)
replay = load('numerical_replay.json')
assert replay['status'] == 'PASS_NEW_ROUND14_TWO_SEPARATE_ISOLATED_BYTES_AND_FIELDS_REPLAY'
assert len(replay['runs']) == 2 and {r['bank'] for r in replay['runs']} == {'coverage', 'complement'}
statuses = {'coverage': 'PASS_NEW_SHORT_SHIFT_AND_COMPLETE_FIBRE_IDENTITIES_ONLY',
    'complement': 'PASS_NEW_COMPLETE_CRT_CUTS_AND_ACTUAL_NEIGHBOR_CAPACITIES_ONLY'}
gates, bank_audits = {}, {}
registry = load('previous_artifacts_sha256.json')['sha256']
for row in replay['runs']:
    name = row['bank']; source = ROUND / (name + '_checks.py'); canonical = ROUND / (name + '.json')
    isolated = ROUND / ('isolated_' + name) / (name + '.json')
    assert Path(row['canonical']) == canonical and Path(row['isolated']) == isolated
    assert row['exit_code'] == 0 and row['bytes_identical'] is True and row['all_fields_identical'] is True
    assert canonical.read_bytes() == isolated.read_bytes()
    assert json.loads(canonical.read_bytes()) == json.loads(isolated.read_bytes())
    assert digest(source) == row['source_sha256']
    assert digest(canonical) == digest(isolated) == row['output_sha256']
    assert digest(Path(row['log'])) == row['log_sha256']
    marker = load('role6/' + name + '_canonical_success.json')
    assert marker['exit_code'] == 0 and marker['producer_sha256'] == digest(source)
    assert marker['output_sha256'] == digest(canonical)
    assert digest(Path(marker['source_snapshot'])) == marker['producer_sha256']
    assert digest(Path(marker['log'])) == marker['log_sha256']
    gate = json.loads(canonical.read_bytes())
    assert gate['status'] == statuses[name]
    assert (gate['N'], gate['alpha'], gate['a'], gate['Q'], gate['M'], gate['H']) == (100000000,100,3163,999999,1000000,2)
    for old, expected in gate['imports_sha256'].items():
        assert registry[old] == expected and digest(BASE / old) == expected
    gates[name] = gate
    bank_audits[name] = dict(status=gate['status'], source_sha256=digest(source), receipt_sha256=digest(canonical),
        isolated_receipt_sha256=digest(isolated), bytes=len(canonical.read_bytes()), all_fields_equal=True,
        all_bytes_equal=True, canonical_marker_sha256=digest(ROUND / ('role6/' + name + '_canonical_success.json')),
        producer_invoked_by_judge=False)
supp = load('coverage_pair_supplement.json')
assert supp['status'] == 'PASS_NEW_STORED_ACTUAL_PAIR_AND_SYMBOLIC_PRINCIPAL_SUPPLEMENT_ONLY'
assert supp['frozen_coverage_sha256'] == digest(ROUND / 'coverage.json')
assert supp['stored_vectors_only_no_kernel_recalculation'] is True and supp['canonical_or_old_bank_rerun'] is False
bank_audits['supplement'] = dict(status=supp['status'], source_sha256=digest(ROUND / 'coverage_pair_supplement.py'),
    receipt_sha256=digest(ROUND / 'coverage_pair_supplement.json'), mode='STORED_FROZEN_VECTORS_ONLY',
    producer_invoked_by_judge=False, supplement_repeated_by_judge=False)
stored_audit = load('role6/read_only_audit.json')
assert stored_audit['status'] == 'PASS_NEW_STORED_VECTOR_CONSISTENCY_ONLY'
for name, expected in stored_audit['input_sha256'].items(): assert digest(ROUND / name) == expected
assert stored_audit['vertices_checked'] == stored_audit['distinct_actual_vertices'] == 78
assert stored_audit['complement_all_descent_X5_edges_checked'] == 44
assert stored_audit['kernels_recalculated'] is False and stored_audit['bank_reexecuted'] is False
bank_audits['stored_vector_audit'] = dict(status=stored_audit['status'],
    source_sha256=digest(ROUND / 'role6/read_only_audit.py'),receipt_sha256=digest(ROUND / 'role6/read_only_audit.json'),
    mode='STORED_FROZEN_VECTORS_ONLY',producer_invoked_by_judge=False,supplement_repeated_by_judge=False)
falsifiers, signs = {}, {}
def walk(node, path):
    assert not isinstance(node, float), ('Floating value in exact gate', path)
    if isinstance(node, dict):
        if 'sign' in node and 'lower' in node and 'upper' in node:
            lo, hi, sign = Fraction(node['lower']), Fraction(node['upper']), node['sign']
            assert lo <= hi and sign in ('POSITIVE', 'NEGATIVE', 'ZERO'), path
            assert (lo > 0 if sign == 'POSITIVE' else hi < 0 if sign == 'NEGATIVE' else lo == hi == 0), path
            signs[path] = sign
        assert node.get('global_no_go', False) is False
        for k,v in node.items(): walk(v, path + '.' + str(k))
    elif isinstance(node, list):
        for i,v in enumerate(node): walk(v, path + '.' + str(i))
for name, gate in [('coverage', gates['coverage']), ('complement', gates['complement']), ('supplement', supp)]:
    for k in ('global_D_N', 'asymptotic', 'payments', 'Lean_called', 'victory'): assert gate[k] is False
    assert gate['strict_rational_only'] is True and gate['finite_N_outside_source'] is True
    assert gate['source_u_minimum'] == '10^24'
    for k in ('conservation_before', 'conservation_after'):
        assert gate[k]['status'] == 'PRESERVED' and gate[k]['files'] == 603
    walk(gate, name)
    for i, item in enumerate(gate.get('ERROR_FALSIFIER', [])):
        assert item['status'].startswith('REFUTED_NEW_')
        falsifiers[name + '.ERROR_FALSIFIER.' + str(i)] = dict(claim=item['claim'], status=item['status'])
assert len(falsifiers) == 4
walk(stored_audit, 'stored_vector_audit')
assert numeric['strict_rational_sign_certificates'] == len(signs)
for k in ('global_D_N', 'asymptotic', 'payments', 'Lean_called', 'victory', 'old_PASS_replayed', 'old_Lean_recompiled'):
    assert replay[k] is False
assert replay['separate_isolated_directories'] is True and replay['only_new_round14_producers_executed'] is True
for k in ('conservation_before', 'conservation_after'):
    assert replay[k]['status'] == 'PRESERVED' and replay[k]['files'] == 603

# All following checks use stored exact vectors and integer supports only.
def vec(v): return {tuple(map(int,k.split(','))): Fraction(x) for k,x in v.items() if Fraction(x)}
def add(*items):
    out = {}
    for item in items:
        for k,v in item.items(): out[k] = out.get(k, Fraction(0)) + v
    return {k:v for k,v in out.items() if v}
def scale(item, x): return {k:v*x for k,v in item.items() if v*x}
def mul(left, right):
    out = {}
    for k,v in left.items():
        for l,w in right.items():
            kl = tuple(sorted(k+l)); out[kl] = out.get(kl, Fraction(0)) + v*w
    return {k:v for k,v in out.items() if v}
def log(n): return {(n,): Fraction(1)}
def profile(p, side, c):
    assert p['unit'] and p['bulk'] and p['n_prime']
    assert p['m'] + p['n'] == 100000000 and p['n'] > 999999
    assert p['R'] == min(999999, (p['m']-1)//3163) and p['original_cap_Q'] == 999999
    assert p['front_strict'] and p['k1_joint_D_minus_W'] == {} and p['k1_D'] == p['k1_W']
    assert p['mu_m'] == (-1 if side == 'P' else 1) and p['Lambda_m'] == {}
    assert vec(p['short_prefix']) == scale(log(c), -1 if side == 'P' else 1)
    assert vec(p['short_prefix']) == add(vec(p['low_prefix']), vec(p['annulus']))
    expected = add(log(c), scale(vec(p['W']), -1)) if side == 'P' else add(vec(p['W']), scale(log(c),-1))
    assert vec(p['C']) == expected
    assert vec(p['C']) == scale(add(vec(p['D']),scale(vec(p['W']),-1)), -p['mu_m'])
    assert vec(p['theta_n']) == vec(p['raw_Lambda_N_n']) == log(p['n'])
    assert vec(p['B_prime_source']) == vec(p['B_raw_source']) == mul(log(p['n']), expected)

coverage, complement = gates['coverage'], gates['complement']
fibre = coverage['complete_fibre_window']; profiles = fibre['all_vertices_profiles']
assert fibre['L'] == 3580 and fibre['integer_candidates_examined'] == list(range(3164,3581))
assert fibre['candidate_count'] == 417 and fibre['front_parents'] == [3167]
assert fibre['P_int'] == [p for p in fibre['P_all'] if p != 3167]
for key, p in profiles.items(): profile(p, key.split(':')[0], 3)
assert (coverage['parent_zero_H']['m'], coverage['parent_zero_H']['n']) == (35698989,64301011)
assert coverage['H_window']['degrees_parent']['3323'] == 0
assert coverage['new_front_parent_zero_all']['parent']['m'] == 34023081
assert coverage['new_front_parent_zero_all']['parent']['n'] == 65976919
assert [x['t'] for x in coverage['new_front_parent_zero_all']['all_possible_t_before_p']] == [3164,3165,3166]
assert all(x['gcd_with_N'] > 1 for x in coverage['new_front_parent_zero_all']['all_possible_t_before_p'])
graph_summary = {}
for label in ('graph_all', 'graph_interior'):
    g = coverage[label]; P,T = g['parents'],g['images']; used = set(); D = 0
    assert g['edges'] == [[p,t] for p in P for t in T if t<p]
    matched = []; unmatched = []
    for j, (p,row) in enumerate(zip(P,g['prefix_steps_complete']),1):
        neighbors = [t for t in T if t<p]; nextD = max(D,j-len(neighbors),0)
        assert row['j'] == j and row['p'] == p and row['neighbors'] == neighbors and row['T_j'] == len(neighbors)
        assert row['D_previous'] == D and row['D_j'] == nextD and row['unmatched_indicator'] == nextD-D
        avail = [t for t in neighbors if t not in used]
        if avail: used.add(avail[0]); matched.append([p,avail[0]])
        else: unmatched.append(p)
        D = nextD
    assert matched == g['matching'] and unmatched == g['unmatched_parents']
    assert [t for t in T if t not in used] == g['unmatched_images'] and D == g['prefix_deficit']
    assert len(matched) == g['maximum_matching_size'] and len(g['prefix_steps_complete']) == len(P)
    whole = add(*[vec(profiles['P:'+str(p)]['B_prime_source']) for p in P],
        *[vec(profiles['T:'+str(t)]['B_prime_source']) for t in T])
    assert whole == vec(g['whole_actual_B']) == add(vec(g['matched_actual_B']),
        vec(g['unmatched_parent_actual_B']),vec(g['unmatched_image_actual_B']))
    assert g['unpaid_complement_retained'] and g['entire_partition_identity_exact']
    graph_summary[label] = dict(parents=len(P),images=len(T),edges=len(g['edges']),matching=len(matched),
        prefix_deficit=D,unmatched_parents=unmatched,unmatched_images=g['unmatched_images'])
assert graph_summary['graph_all']['prefix_deficit'] == 5 and graph_summary['graph_interior']['prefix_deficit'] == 4
H = coverage['H_window']; assert H['edges'] == [[p,t] for p in fibre['P_all'] for t in fibre['T'] if p-t in (2,4)]
for side, key in (('parent','P_all'),('image','T')):
    index = 0 if side=='parent' else 1
    for x in fibre[key]:
        d = sum(edge[index]==x for edge in H['edges'])
        assert H['degrees_'+side][str(x)] == d <= 2
        assert Fraction(H['normalized_'+side+'_load'][str(x)]) == Fraction(d,2)
assert vec(H['whole_actual_B']) == add(vec(H['joint_edge_charge']),vec(H['parent_deficit_actual']),vec(H['image_deficit_actual']))

pair_memberships = {}
for label, rows in [('E_H',H['edges']),('G_all',coverage['graph_all']['matching']),('G_int',coverage['graph_interior']['matching'])]:
    for p,t in rows: pair_memberships.setdefault((p,t),[]).append(label)
assert supp['checked_unique_pairs'] == len(pair_memberships) == len(supp['checks'])
for row in supp['checks']:
    p,t = row['p'],row['t']; P,T = profiles['P:'+str(p)],profiles['T:'+str(t)]
    assert row['memberships'] == pair_memberships[p,t]
    assert row['h'] == (p-t)//2 and p>t and (p-t)%2==0
    assert row['n_image']-row['n_parent'] == row['exact_displacement'] == 2*row['h']*3*3581
    actual = add(vec(P['B_prime_source']),vec(T['B_prime_source']))
    assert actual == vec(row['literal_actual_pair_B']) == add(vec(row['X5_retained_entropy']),vec(row['X5_retained_commutator']))
    assert row['C3_C4_X5_exact'] and row['principal_sign_not_promoted_to_actual_sign']
    assert row['principal_S_symbolic']['constant_sign_certificate']['sign'] == 'NEGATIVE'
    assert row['principal_S_symbolic']['S_coefficient_sign_certificate']['sign'] == 'NEGATIVE'

cuts = {}; all_actual_m = [p['m'] for p in profiles.values()]; cross_edges = 0
for label in ('C1','C2'):
    g = complement[label]; parentprofiles = g['all_actual_parent_profiles']; imageprofiles = g['all_descent_image_profiles']
    assert g['parent_count'] == len(g['parents']) == len(parentprofiles)
    assert not g['finite_family_neighbor_union'] and all(v==0 for v in g['finite_family_degrees'].values())
    for p in parentprofiles.values(): profile(p,'P',7)
    for p in imageprofiles.values(): profile(p,'T',7)
    all_actual_m.extend(p['m'] for p in parentprofiles.values())
    all_actual_m.extend(p['m'] for p in imageprofiles.values())
    debt = add(*[vec(p['B_prime_source']) for p in parentprofiles.values()])
    cap = scale(add(*[vec(p['B_prime_source']) for p in imageprofiles.values()]),-1)
    assert debt == vec(g['actual_unmatched_finite_family_debt']) and cap == vec(g['actual_distinct_image_capacity'])
    assert add(debt,scale(cap,-1)) == vec(g['actual_cut_minus_all_neighbor_capacity'])
    assert g['strict_positive_debt_certificate']['sign'] == g['capacity_sign_certificate']['sign'] == 'POSITIVE'
    assert g['defect_sign_certificate']['sign'] == 'NEGATIVE'
    assert len(g['Gamma_all']) == len({v['key'] for v in g['Gamma_all']}) == len(imageprofiles) == g['Gamma_all_distinct_count']
    assert g['all_union_counted_once_per_y_t'] and g['outside_cut_complement_retained']
    assert g['Hall_or_capacity_lower_bound_assumed'] is False and g['zero_finite_degree_not_promoted_to_all_orphan']
    for edge in g['all_descent_edges']:
        assert edge['x']-edge['t'] == 2*edge['h'] > 0
        P,T = parentprofiles[edge['parent']],imageprofiles[edge['image']]
        assert P['m']-T['m'] == T['n']-P['n'] == 2*edge['h']*7*edge['y']
        ratio = add(log(T['n']),scale(log(P['n']),-1))
        actual = add(vec(P['B_prime_source']),vec(T['B_prime_source']))
        assert actual == add(scale(mul(vec(P['C']),ratio),-1),
            mul(log(T['n']),add(vec(T['W']),scale(vec(P['W']),-1))))
        cross_edges += 1
    for row in g['all_shift_candidates_complete']: assert row['small_factor_divides'] and not row['neighbors'] and row['ell']<=7
    cuts[label] = dict(parents=g['parent_count'],images=g['Gamma_all_distinct_count'],edges=len(g['all_descent_edges']),
        both_axes=g['both_large_axes_tested'],finite_degrees_zero=True,debt='POSITIVE',capacity='POSITIVE',expanded_defect='NEGATIVE')
assert len(all_actual_m) == len(set(all_actual_m)) == 78 and cross_edges == 44
assert not complement['double_CRT105_both_axes_empty']['parents']
assert complement['proposed_C2_witness_rejected']['n_prime'] is False
assert complement['proposed_C2_witness_rejected']['n'] == 11793077
assert complement['proposed_C2_witness_rejected']['n_factorization'] == [[73,2],[2213,1]]
assert complement['proposed_C2_witness_rejected']['raw_Lambda_N_n'] == {}
assert complement['new_parent_C2']['n'] == 2335097
failure = load('role6/complement_attempt01_failure.json')
assert failure['exit_code'] == 1 and failure['attempt'] == 1
assert digest(Path(failure['source_snapshot'])) == failure['producer_sha256']
assert digest(Path(failure['log'])) == failure['log_sha256']
failurelog = Path(failure['log']).read_text(encoding='utf-8')
assert 'AssertionError' in failurelog and "v['q']==3917" in failurelog
assert failure['producer_sha256'] != digest(ROUND / 'complement_checks.py')
verify.verify_inputs(inputs)
after = verify.preservation(inputs)
assert before == after
receipt = dict(round=14,status='PARTIAL_EXACT_CAPACITY_DEFECT_WITH_UNESTIMATED_INTERIOR',
    recorded_at_utc=datetime.now(timezone.utc).isoformat(),input_manifest=str(manifest),input_manifest_sha256=digest(manifest),
    input_sha256=inputs['sha256'],external_sha256=inputs['external_sha256'],final_role_signals=inputs['final_role_signals'],
    numeric_manifest_sha256=digest(ROUND / 'numeric_manifest.json'),numeric_bindings=len(numeric['sha256']),
    numerical_audit_mode='READ_ONLY_ALL_FIELDS_AND_BYTES_OF_TWO_EXISTING_ISOLATED_REPLAYS_AND_STORED_SUPPLEMENT',
    bank_audits=bank_audits,distinct_contract_statuses={n:v['status'] for n,v in bank_audits.items()},
    falsifiers=falsifiers,falsifier_count=len(falsifiers),rational_signs=signs,rational_sign_count=len(signs),
    strict_signs=True,unresolved_signs=0,floating_values=0,graphs=graph_summary,cuts=cuts,
    supplemental_unique_pairs=len(supp['checks']),supplemental_actual_sign_counts={v:sum(r['actual_pair_sign_certificate']['sign']==v for r in supp['checks']) for v in ('POSITIVE','NEGATIVE','ZERO')},
    distinct_actual_vertices_checked=78,complement_all_descent_C4_edges_checked=44,
    real_failed_numerical_selection=dict(exit_code=1,attempt=1,source_sha256=failure['producer_sha256'],
        log_sha256=failure['log_sha256'],classification='Composite proposed complement, not failed arithmetic identity and not Lean'),
    preservation_before=before,preservation_after=after,lean_invoked=False,compiler_failure_fabricated=False,
    new_lean_modules=0,new_lean_conclusions=0,cumulative_auxiliary_modules=15,cumulative_auxiliary_conclusions=208,
    old_banks_rerun=False,new_producers_repeated_by_judge=False,supplement_repeated_by_judge=False,
    old_lean_rerun=False,old_pdf_rerendered=False,finite_N=100000000,source_adaptive_u_min='10^24',
    finite_witness_is_source_onset_test=False,global_no_go=False,victory=False,score=0,
    written_partial_costs={'window_variation':'42*N^(63/64)*u^2','whole_front':'28*N^(37/64)*u^3*(1+u)',
        'written_not_Lean_certified':True,'interior_capacity_not_paid':True,'alternative_U4_not_double_counted':True},
    semantic_open_obligations=['C17 actual coupled prime-incidence prefix defect or matching-independent C16 weighted comparison',
        'Remaining J0/J1/J2, c=1, -S(N)N, long cofactors and matching S(cN)',
        'Full K2/P5, singletons/faces and rough credit retained before exact withdrawals',
        'Physical-band additional effective BV onset and 2 max(e,0)'],
    judge_scripts_sha256={n:digest(HERE/n) for n in ('audit-judge.ps1','verify-frozen.ps1','freeze-inputs.py','verify-frozen.py','run-audit.py')})
(HERE/'judge_receipt.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=receipt['status'],protected_files=603,numeric_bindings=receipt['numeric_bindings'],
    bank_copies_audited=2,supplemental_pairs=len(supp['checks']),falsifiers=len(falsifiers),rational_sign_positions=len(signs),
    lean_invoked=False,new_conclusions=0,cumulative_conclusions=208,victory=False,score=0),indent=2))
