"""Final readonly round15 Judge: exact frozen replay receipts and stored arithmetic."""
import sys
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
import ast,importlib.util,json
from datetime import datetime,timezone
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
HERE=Path(__file__).resolve().parent; ROUND=HERE.parent; BASE=ROUND.parent
spec=importlib.util.spec_from_file_location('round15_judge_verify',HERE/'verify-frozen.py')
verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify);digest=verify.digest
manifest=HERE/'input_sha256.json';inputs=json.loads(manifest.read_bytes());verify.verify_inputs(inputs)
before=verify.preservation(inputs)
def load(n):return json.loads((ROUND/n).read_bytes())
numeric=load('numeric_manifest.json')
assert digest(ROUND/'numeric_manifest.json')==inputs['numeric_manifest_sha256']
assert numeric['status']=='FINAL_FROZEN_NEW_ROUND15_NUMERIC_PARTIAL'
assert numeric['files']==len(numeric['sha256'])
for n,h in numeric['sha256'].items():assert digest(ROUND/n)==h,n
final6=load('role6_final_receipt.json');closure=load('role6/closure_receipt.json')
assert numeric['receipt_sha256']==digest(ROUND/'role6_final_receipt.json')
assert numeric['reports_FINAL_sha256']==final6['reports_FINAL_sha256']==closure['reports_FINAL_sha256']=={
    v['report']:v['report_sha256'] for k,v in inputs['final_role_signals'].items() if k in ('role1','role2')}
assert numeric['new_bank_bindings']==final6['bindings']==closure['bindings']
assert final6['status']=='FINAL_NEW_ROUND15_NUMERICAL_ONLY_PARTIAL'
assert closure['status']=='READ_ONLY_FINAL_GATE_BINDINGS_AND_SCOPE_VERIFIED'
assert final6['own_asset_count_before_receipt']==len(final6['own_assets_sha256'])
for n,h in final6['own_assets_sha256'].items():assert digest(ROUND/n)==h,n
assert final6['isolated_replays_total']==3 and final6['new_canonical_attempts']==3
assert final6['new_canonical_candidate_banks']==2 and final6['necessary_read_only_supplements']==1
assert final6['real_failed_attempts']==0 and final6['post_replay_reruns']==0 and final6['old_PASS_replays']==0
for entry in (numeric,final6,closure):
    assert entry['score']==0 and entry['victory'] is False and entry['noLean'] and entry['noGlobal']
for k in ('new_Lean_modules','new_Lean_theorems','new_Lean_definitions'):assert final6[k]==0
assert closure['all_existing_gates_and_replay_copies_read_only'] and closure['source_or_gate_mutated'] is False
assert closure['producer_or_kernel_called_during_closure'] is False
for n in inputs['sha256']:
    if n.endswith('.py'):ast.parse((ROUND/n).read_text(encoding='utf-8'),filename=n)
statuses={'incidence':'PASS_NEW_COMPLETE_141_MASK_PROJECTION_AND_COVARIANCE_ONLY',
    'fusion':'PASS_NEW_COMPLETE_SMALL_CORE_FUSION_UNION_AND_PRINCIPAL_MAJORANT_ONLY'}
gates={};bank_audits={};registry=load('previous_artifacts_sha256.json')['sha256']
for name,status in statuses.items():
    canonical=ROUND/(name+'.json');isolated=ROUND/('isolated_'+name)/(name+'.json');src=ROUND/(name+'_checks.py')
    row=load('role6/'+name+'_replay_receipt.json');marker=load('role6/'+name+'_canonical_success.json')
    assert row['status']=='PASS_NEW_ROUND15_SEPARATE_ISOLATED_BYTES_AND_FIELDS_REPLAY'
    assert row['bank']==name and row['exit_code']==0 and row['all_fields_identical'] and row['bytes_identical']
    assert Path(row['canonical'])==canonical and Path(row['isolated'])==isolated
    assert canonical.read_bytes()==isolated.read_bytes() and json.loads(canonical.read_bytes())==json.loads(isolated.read_bytes())
    assert digest(canonical)==digest(isolated)==row['output_sha256']==marker['output_sha256']
    assert digest(src)==row['source_sha256']==marker['producer_sha256']
    assert marker['exit_code']==0 and digest(Path(marker['source_snapshot']))==marker['producer_sha256']
    for entry in (row,marker):assert digest(Path(entry['log']))==entry['log_sha256']
    gate=json.loads(canonical.read_bytes());assert gate['status']==status
    assert (gate['N'],gate['alpha'],gate['a'],gate['Q'],gate['M'])==(100000000,100,3163,999999,1000000)
    for n,h in gate['imports_sha256'].items():assert registry[n]==h and digest(BASE/n)==h,n
    for entry in (row,gate):
        for k in ('global_D_N','asymptotic','payments','Lean_called','victory'):assert entry[k] is False
        for k in ('conservation_before','conservation_after'):assert entry[k]['status']=='PRESERVED' and entry[k]['files']==651
    assert row['old_PASS_replayed'] is False and row['old_Lean_recompiled'] is False
    assert gate['finite_N_outside_source'] and gate['source_u_minimum']=='10^24' and gate['strict_rational_only']
    gates[name]=gate
    bank_audits[name]=dict(status=status,source_sha256=digest(src),receipt_sha256=digest(canonical),
        isolated_receipt_sha256=digest(isolated),all_fields_equal=True,all_bytes_equal=True,bytes=len(canonical.read_bytes()),
        replay_receipt_sha256=digest(ROUND/('role6/'+name+'_replay_receipt.json')),producer_invoked_by_judge=False)
moment=load('incidence_moment.json');mrow=load('role6/incidence_moment_replay_receipt.json')
mmarker=load('role6/incidence_moment_canonical_success.json')
assert moment['status']=='PASS_NEW_READ_ONLY_INCIDENCE_L4_AND_EXACT_AP_FRONT_SUPPLEMENT'
assert mrow['status']=='PASS_NEW_ROUND15_SEPARATE_ISOLATED_BYTES_AND_FIELDS_REPLAY' and mrow['bank']=='incidence_moment'
assert mrow['exit_code']==mmarker['exit_code']==0 and mrow['all_fields_identical'] and mrow['bytes_identical']
mc=ROUND/'incidence_moment.json';mi=ROUND/'isolated_incidence_moment/incidence_moment.json'
assert mc.read_bytes()==mi.read_bytes() and json.loads(mc.read_bytes())==json.loads(mi.read_bytes())
assert digest(mc)==digest(mi)==mrow['output_sha256']==mmarker['output_sha256']
assert digest(ROUND/'incidence_moment_checks.py')==mrow['source_sha256']==mmarker['producer_sha256']
assert digest(Path(mmarker['source_snapshot']))==mmarker['producer_sha256']
for entry in (mrow,mmarker):assert digest(Path(entry['log']))==entry['log_sha256']
assert moment['input_gate_sha256']==digest(ROUND/'incidence.json') and moment['input_producer_sha256']==digest(ROUND/'incidence_checks.py')
assert moment['producer_incidence_not_executed'] and moment['D_W_kernels_not_recomputed'] and moment['old_PASS_not_executed']
for k in ('global_D_N','asymptotic','payments','Lean_called','victory'):assert moment[k] is False and mrow[k] is False
for k in ('conservation_before','conservation_after'):assert moment[k]['status']=='PRESERVED' and moment[k]['files']==651
for n,h in moment['imports_sha256'].items():assert registry[n]==h and digest(BASE/n)==h,n
bank_audits['incidence_moment']=dict(status=moment['status'],source_sha256=mrow['source_sha256'],receipt_sha256=digest(mc),
    isolated_receipt_sha256=digest(mi),all_fields_equal=True,all_bytes_equal=True,bytes=len(mc.read_bytes()),
    replay_receipt_sha256=digest(ROUND/'role6/incidence_moment_replay_receipt.json'),producer_invoked_by_judge=False,
    stored_frozen_vectors_only=True)
signs={};falsifiers={};unrefuted_promotions={}
def walk(node,path):
    assert not isinstance(node,float),('Floating value in exact gate',path)
    if isinstance(node,dict):
        if all(k in node for k in ('sign','lower','upper')):
            sign=node['sign'];lo,hi=Fraction(node['lower']),Fraction(node['upper'])
            assert lo<=hi and sign in ('POSITIVE','NEGATIVE','ZERO'),path
            assert (lo>0 if sign=='POSITIVE' else hi<0 if sign=='NEGATIVE' else lo==hi==0),path
            signs[path]=sign
        assert node.get('global_no_go',False) is False
        for k,v in node.items():walk(v,path+'.'+str(k))
    elif isinstance(node,list):
        for i,v in enumerate(node):walk(v,path+'.'+str(i))
for name,gate in gates.items():
    walk(gate,name)
    for i,item in enumerate(gate['ERROR_FALSIFIER']):
        key=name+'.ERROR_FALSIFIER.'+str(i)
        if item['status'].startswith('REFUTED_NEW_'):falsifiers[key]=dict(claim=item['claim'],status=item['status'])
        else:
            assert item['status']=='NO_COUNTEREXAMPLE_IN_WINDOW'
            unrefuted_promotions[key]=dict(claim=item['claim'],status=item['status'])
walk(moment,'incidence_moment')

# Pure checks of stored integer supports and exact logarithmic coefficients.
def vec(v):return {tuple(map(int,k.split(','))):Fraction(c) for k,c in v.items() if Fraction(c)}
def add(*items):
    out={}
    for item in items:
        for k,v in item.items():out[k]=out.get(k,Fraction(0))+v
    return {k:v for k,v in out.items() if v}
def scale(item,x):return {k:v*x for k,v in item.items() if v*x}
def mul(left,right):
    out={}
    for k,v in left.items():
        for j,w in right.items():
            key=tuple(sorted(k+j));out[key]=out.get(key,Fraction(0))+v*w
    return {k:v for k,v in out.items() if v}
def log(n):return {(n,):Fraction(1)}
def profile(p,U_a,expected_mu):
    assert p['unit'] and p['bulk'] and p['m']+p['n']==100000000 and p['n']>999999
    assert p['R']==min(999999,(p['m']-1)//3163) and p['original_cap_Q']==999999 and p['front_strict']
    assert p['k1_joint_D_minus_W']=={} and p['k1_D']==p['k1_W'] and p['mu_m']==expected_mu
    assert p['Lambda_m']=={} and vec(p['short_prefix'])==U_a
    assert vec(p['short_prefix'])==add(vec(p['low_prefix']),vec(p['annulus']))
    C=add(scale(U_a,-1),scale(vec(p['W']),expected_mu))
    assert C==vec(p['C'])==scale(add(vec(p['D']),scale(vec(p['W']),-1)),-expected_mu)
    assert vec(p['B_prime_source'])==mul(vec(p['theta_n']),C)
    assert vec(p['B_raw_source'])==mul(vec(p['raw_Lambda_N_n']),C)

inc=gates['incidence'];interval=inc['interval_complete']
assert (inc['c'],inc['r'],inc['d'])==(3,47,141)
assert (interval['low'],interval['high'],interval['integer_count'],interval['unit_count_J'])==(7093,702127,695035,278014)
assert interval['all_integer_b_examined'] and interval['unit_gcd_b_N_equals_unit_gcd_n_N']
beta=inc['structural_beta_without_n_prime_filter'];M=len(beta);J=interval['unit_count_J'];rho=Fraction(inc['rho_unit'])
assert M==inc['M_beta'] and rho==Fraction(M,J) and Fraction(inc['rho_integer_interval'])==Fraction(M,interval['integer_count'])
assert Fraction(inc['rho_unit_bias'])==rho-Fraction(inc['rho_integer_interval'])>0
assert len({v['b'] for v in beta})==M
assert inc['exact_prime_sieve']['primes_through_isqrt_N']==1229
assert inc['exact_prime_sieve']['largest_sieving_prime']==9973
assert interval['min_n']>10000 and interval['high']//71==9889<10000
for v in beta:
    assert v['b']==v['s']*v['q'] and v['m']==141*v['b'] and v['n']==100000000-v['m']
    assert 47<v['s'] and 3*v['s']<=3163<47*v['s']<v['q'] and v['q']>3163
    assert 71<=v['s']<=1054 and v['q']<=9889
    assert v['structural_without_first_prime_filter']
thetaU,thetaB,Gamma=vec(inc['theta_unit_sum']),vec(inc['theta_beta_sum']),vec(inc['Gamma_centered'])
assert Gamma==add(thetaB,scale(thetaU,-rho)) and thetaB==add(scale(thetaU,rho),Gamma)
assert len(thetaU)==inc['exact_prime_sieve']['unit_prime_first_axes']
assert len(thetaB)==sum(v['theta_prime'] for v in beta)
assert Fraction(inc['centered_beta_sum'])==0
norm=Fraction(M)*(1-rho)
assert Fraction(inc['centered_beta_norm_sq_direct'])==Fraction(inc['centered_beta_norm_sq_M_one_minus_rho'])==norm
assert inc['Gamma_sign_certificate']['sign'] in ('POSITIVE','NEGATIVE')
assert inc['projection_identity_exact'] and inc['centered_theta_covariance_equals_Gamma']
raw=inc['raw_Lambda_N'];assert raw['mu_n_sq_filter_used'] is False and raw['proper_powers_retained_separately']
raw_extra=vec(raw['proper_powers_extra_beta'])
assert add(vec(raw['raw_beta']),scale(thetaB,-1))==raw_extra==vec(raw['raw_minus_theta_beta_exact'])
records=raw['proper_power_records_complete'];assert len({v['n'] for v in records})==len(records)
assert add(*[log(v['base_prime']) for v in records])==vec(raw['proper_powers_extra_unit'])
assert add(*[log(v['base_prime']) for v in records if v['beta']])==raw_extra
for v in records:
    assert v['n']==v['base_prime']**v['exponent'] and v['exponent']>=2 and v['n']==100000000-141*v['b']
sample=inc['physical_raccord_sample'];assert sample['sample_count']==len(sample['vertices'])==5
sample_ms=[]
for row in sample['vertices']:
    p=row['profile'];profile(p,log(3),1);assert p['n_prime'] and p['short_prefix']=={'3':'1'}
    assert row['sample_only_no_extrapolation'] and row['structure']['q']>=4001
    assert vec(row['actual_capacity'])==scale(vec(p['B_prime_source']),-1);sample_ms.append(p['m'])
assert sample['historical_values_removed_only_from_sample_not_from_complete_beta_or_Gamma']
assert sample['unsampled_W_errors_literal_uncomputed_and_unpaid']
historical_values=set()
def values(node):
    if isinstance(node,dict):
        for v in node.values():values(v)
    elif isinstance(node,list):
        for v in node:values(v)
    elif isinstance(node,int) and not isinstance(node,bool) and node>=1000000:historical_values.add(node)
    elif isinstance(node,str) and node.isdigit() and int(node)>=1000000:historical_values.add(int(node))
for name in registry:
    if name.endswith('.json'):values(json.loads((BASE/name).read_bytes()))
assert not set(sample_ms)&historical_values
incidence_summary=dict(interval=interval,structural_mask=M,unit_density=str(rho),centered_norm_sq=str(norm),
    first_prime_axes=len(thetaU),first_prime_images=len(thetaB),covariance_sign=inc['Gamma_sign_certificate']['sign'],
    raw_unit_properpowers=len(records),raw_masked_properpowers=sum(v['beta'] for v in records),physical_kernel_sample=sample_ms,
    all_kernels_exhaustively_evaluated=False,covariance_analytic_bound_obtained=False)

# Strict enclosing moment intervals, still factorized; no quadratic-size expansion.
assert moment['J']==J and moment['M_beta']==M and Fraction(moment['rho'])==rho
assert Fraction(moment['centered_beta_norm_sq'])==norm
assert vec(moment['theta_second_moment_exact_vector'])=={(k[0],k[0]):v for k,v in thetaU.items()}
bounds={n:tuple(Fraction(v) for v in endpoints) for n,endpoints in moment['strict_rational_intervals'].items()}
for n,(lo,hi) in bounds.items():
    assert lo<=hi
    sign='NEGATIVE' if n=='Gamma' else 'POSITIVE'
    assert hi<0 if sign=='NEGATIVE' else lo>0
    signs['incidence_moment.strict_rational_intervals.'+n]=sign
Tlo,Thi=bounds['T'];Glo,Ghi=bounds['Gamma'];sqlo,sqhi=bounds['theta_second_moment']
assert bounds['theta_variance']==(sqlo-Thi*Thi/J,sqhi-Tlo*Tlo/J)
assert bounds['Gamma_squared']==(Ghi*Ghi,Glo*Glo)
vlo,vhi=bounds['theta_variance'];glo,ghi=bounds['Gamma_squared']
assert bounds['norm_squared_times_variance_minus_Gamma_squared']==(norm*vlo-ghi,norm*vhi-glo)
assert moment['Cauchy_L4']['strict_positive_gap_certified'] and moment['Cauchy_L4']['no_payment_for_Gamma']
ap=moment['AP_front'];X=interval['max_n']-interval['min_n']+1
assert (ap['d'],ap['phi_d'],ap['X_exact'])==(141,92,X) and X==97999795
assert X==141*(interval['integer_count']-1)+1
assert Fraction(ap['principal_X_over_phi_d'])==Fraction(X,92)
assert Fraction(ap['incorrect_d_times_I_over_phi_d'])==Fraction(141*interval['integer_count'],92)
assert Fraction(ap['front_difference_exact'])==Fraction(1-141,92)==Fraction(-35,23)
assert not ap['E_divN_exceptional_prime_list'] and ap['BV_not_certified_at_this_bank'] and ap['BV_onset_and_K_N_remain_unpaid']
APlo,APhi=map(Fraction,ap['literal_interval_AP_error_bounds'])
assert (APlo,APhi)==(Tlo-Fraction(X,92),Thi-Fraction(X,92)) and APlo<=APhi<0
assert ap['literal_interval_AP_error_sign']=='NEGATIVE';signs['incidence_moment.AP_front.literal_interval_AP_error_bounds']='NEGATIVE'
incidence_summary['L4_positive_gap_enclosure']=True
incidence_summary['AP_width']=X;incidence_summary['AP_front_correction']='-35/23';incidence_summary['AP_finite_error_sign']='NEGATIVE'

fusion=gates['fusion'];qs=fusion['q_window_complete']['q_primes_unit'];union=fusion['structural_parent_core_union']
labels=fusion['structural_cofactor_labels_before_incidence'];corelabels=fusion['structural_core_to_labels']
assert fusion['E']==3003 and fusion['q_window_complete']['low']==8000 and fusion['q_window_complete']['high']==8200
assert fusion['q_window_complete']['all_q_integers_tested'] and qs==sorted(set(qs))
assert all(8000<=q<=8200 and q>3163 for q in qs)
assert union==sorted(set(v['e'] for v in labels)) and len(labels)==sum(len(v) for v in corelabels.values())
for row in labels:
    assert row['c'] in (21,33,39,77,91,143) and row['c']*row['removed_semiprime_t']==3003
    assert row['e']==row['c']*row['p']<3003 and row['p']<row['removed_semiprime_t'] and row['mu_c']==1
    assert row in corelabels[str(row['e'])]
assert {(v['c'],v['p']) for v in corelabels['231']}=={(21,11),(33,7),(77,3)}
vertices=fusion['physical_vertices_all_candidates'];lookup={(v['q'],v['e']):v for v in vertices}
assert len(vertices)==len(lookup)==fusion['candidate_vertex_count'] and len({v['m'] for v in vertices})==len(vertices)
profiles=0;nonzero=0;core_set=set(union)|{3003,131,2751}
assert set(lookup)=={(q,e) for q in qs for e in core_set}
for row in vertices:
    e,q=row['e'],row['q'];assert row['m']==e*q and row['n']==100000000-e*q
    assert row['bulk'] and row['unit'] and row['n_above_original_Q'] and row['canonical_large_prime_q']==q
    assert row['canonical_core_e']==e and row['mu_m']==-row['mu_e'] and row['Lambda_m']=={}
    assert vec(row['U_a'])==scale(vec(row['Lambda_e']),-1)
    assert row['parent_labels_before_first_incidence']==corelabels.get(str(e),[])
    theta,raw=vec(row['theta_N_n']),vec(row['raw_Lambda_N_n'])
    if row['kernel_computed']:
        p=row['physical_profile'];profile(p,scale(vec(row['Lambda_e']),-1),row['mu_m']);profiles+=1
        assert p['short_prefix']==row['U_a'] and theta==vec(p['theta_n']) and raw==vec(p['raw_Lambda_N_n'])
    else:
        assert not theta and not raw and row['actual_B_prime_exact_zero'] and row['actual_B_raw_exact_zero']
        assert row['uncomputed_W_not_free_not_estimated']
    nonzero+=bool(theta or raw)
    for idx in row['bilateral_deleted_prime_indices']:
        assert idx['cofactor_b']*idx['deleted_prime']==row['m'] and idx['model_index_bN']==idx['cofactor_b']*100000000
        assert idx['symbol_preserved_not_substituted_by_S_N']
assert profiles==fusion['computed_D_W_profiles'] and len(vertices)-profiles==fusion['actual_zero_vertices_with_literal_W']
assert fusion['sample_used_for_nonzero_terms'] is False
def B(row,raw=False):
    if not row['kernel_computed']:return {}
    return vec(row['physical_profile']['B_raw_source' if raw else 'B_prime_source'])
principal={};actual={};actualraw={};orphans={};parents=targets=0;edges=0
for row in fusion['per_q']:
    q=row['q'];target=lookup[q,3003];IE=bool(target['theta_N_n']);active=[e for e in union if lookup[q,e]['theta_N_n']]
    assert row['I_E']==int(IE) and row['D_distinct_parent_prime_vertices']==len(active) and row['active_parent_cores']==active
    assert row['active_label_count']==sum(len(corelabels[str(e)]) for e in active)
    delta=add(vec(target['theta_N_n']),scale(add(*[vec(lookup[q,e]['theta_N_n']) for e in active]),-1))
    orphan=vec(target['theta_N_n']) if IE and not active else {}
    real=add(B(target),*[B(lookup[q,e]) for e in union]);rawreal=add(B(target,True),*[B(lookup[q,e],True) for e in union])
    assert delta==vec(row['principal_Delta_q']) and orphan==vec(row['orphan_majorant_F4_q'])
    assert add(orphan,scale(delta,-1))==vec(row['F4_gap_orphan_minus_Delta'])
    assert row['F4_gap_sign_certificate']['sign'] in ('ZERO','POSITIVE') and row['target_orphan']==bool(orphan)
    assert real==vec(row['entire_actual_B_q']) and rawreal==vec(row['entire_actual_raw_B_q'])
    principal=add(principal,delta);actual=add(actual,real);actualraw=add(actualraw,rawreal);orphans=add(orphans,orphan)
    parents+=len(active);targets+=IE;edges+=len(active) if IE else 0
assert principal==vec(fusion['principal_entire_Delta']) and actual==vec(fusion['entire_actual_B_prime'])
assert orphans==vec(fusion['orphan_mass_F6']) and add(orphans,scale(principal,-1))==vec(fusion['F4_total_gap_orphan_minus_Delta'])
assert parents==fusion['parent_prime_vertex_count'] and targets==fusion['target_prime_count'] and edges==len(fusion['active_physical_edges'])
for row in fusion['active_physical_edges']:
    q,e=row['q'],row['e'];P,T=lookup[q,e],lookup[q,3003]
    assert e<3003 and P['n']-T['n']==row['n_parent_minus_target']==(3003-e)*q
    pair=add(B(P),B(T));assert pair==vec(row['actual_pair'])
    thetaP,thetaT=vec(P['theta_N_n']),vec(T['theta_N_n']);delta=add(thetaT,scale(thetaP,-1))
    Wp,Wt=vec(P['physical_profile']['W']),vec(T['physical_profile']['W'])
    assert pair==add(scale(mul(Wt,delta),-1),mul(thetaP,add(Wp,scale(Wt,-1))))
    assert delta==vec(row['principal_coefficient']) and row['principal_sign_certificate']['sign']=='NEGATIVE'
    assert row['physical_edge_count']==1 and row['target_counted_once_in_entire_sum'] and row['U4_error_unpaid']
rawfusion=fusion['raw_Lambda_N'];assert actualraw==vec(rawfusion['entire_actual_B_raw'])
assert add(actualraw,scale(actual,-1))==vec(rawfusion['raw_minus_prime_exact']) and rawfusion['no_mu_n_squared_filter']
assert rawfusion['proper_power_count']==len(rawfusion['proper_power_vertices'])
assert fusion['rank_cut_finite']['minimum_six_factor_product']==161525364>100000000
assert fusion['J2_composite_cofactor_empty_finite']['c_max']==9 and fusion['J2_composite_cofactor_empty_finite']['squarefree_unit_c']==[1,3,7]
assert fusion['controls']['F1_domain_e_at_least_2']
fusion_summary=dict(q_window=[8000,8200],q_primes=len(qs),structural_labels=len(labels),distinct_parent_cores=len(union),
    candidate_vertices=len(vertices),computed_D_W_profiles=profiles,exact_zero_uncomputed_vertices=len(vertices)-profiles,
    first_prime_parents=parents,first_prime_targets=targets,physical_edges=edges,orphan_targets=fusion['orphan_target_q'],
    principal_sign=fusion['principal_entire_sign_certificate']['sign'],actual_sign=fusion['entire_actual_sign_certificate']['sign'],
    raw_properpowers=rawfusion['proper_power_count'],global_union_over_other_E_estimated=False)

# Preserve actual failures as recorded; do not turn missing estimates into compiler errors.
failures=[]
for p in sorted((ROUND/'role6').glob('*_failure.json')):
    entry=json.loads(p.read_bytes());assert entry['exit_code']!=0
    assert digest(Path(entry['source_snapshot']))==entry['producer_sha256']
    assert digest(Path(entry['log']))==entry['log_sha256']
    failures.append(dict(receipt=p.relative_to(ROUND).as_posix(),exit_code=entry['exit_code'],
        source_sha256=entry['producer_sha256'],log_sha256=entry['log_sha256'],classification='ACTUAL_NUMERICAL_ATTEMPT_ONLY_NOT_LEAN'))
verify.verify_inputs(inputs);after=verify.preservation(inputs);assert before==after
receipt=dict(round=15,status='PARTIAL_SHORT_CONDUCTOR_COVARIANCE_AND_UNESTIMATED_ORPHAN_INCIDENCE',
    recorded_at_utc=datetime.now(timezone.utc).isoformat(),input_manifest_sha256=digest(manifest),input_sha256=inputs['sha256'],
    external_sha256=inputs['external_sha256'],final_role_signals=inputs['final_role_signals'],numeric_manifest_sha256=digest(ROUND/'numeric_manifest.json'),
    numeric_bindings=len(numeric['sha256']),numerical_audit_mode='READ_ONLY_EXISTING_THREE_ISOLATED_REPLAY_FIELDS_BYTES_AND_STORED_VECTORS',
    bank_audits=bank_audits,distinct_contract_statuses={n:v['status'] for n,v in bank_audits.items()},falsifiers=falsifiers,falsifier_count=len(falsifiers),
    promotions_without_counterexample=unrefuted_promotions,rational_signs=signs,rational_sign_count=len(signs),
    strict_signs=True,unresolved_signs=0,floating_values=0,incidence=incidence_summary,fusion=fusion_summary,
    actual_numerical_failures=failures,preservation_before=before,preservation_after=after,lean_invoked=False,
    compiler_failure_fabricated=False,new_lean_modules=0,new_lean_conclusions=0,cumulative_auxiliary_modules=15,cumulative_auxiliary_conclusions=208,
    old_banks_rerun=False,new_producers_repeated_by_judge=False,old_lean_rerun=False,old_pdf_rerendered=False,
    finite_N=100000000,source_adaptive_u_min='10^24',finite_witness_is_source_onset_test=False,global_no_go=False,victory=False,score=0,
    corrected_pre_freeze_domain=dict(F2_F5_E_rank_even_min=4,parent_core_composite_odd_rank_min=3,physical_core_e1_separate=True,
        common_bulk_unit_Q_guards_on_all_selected_vertices=True,correction_not_Lean_failure=True),
    semantic_open_obligations=['Weighted Gamma_d covariance and comparison to true parent incidences',
        'F6 coupled target-first-prime with no parent-first-prime, plus union capacities over all E',
        'c=1, -S(N)N, matching S(bN), long cofactors and remaining signed J0/J1/J2',
        'Full P5, singletons/faces/nonbulk, extra effective physical-band BV onset and 2 max(e,0)'],
    judge_scripts_sha256={n:digest(HERE/n) for n in ('audit-judge.ps1','verify-frozen.ps1','freeze-inputs.py','verify-frozen.py','run-audit.py')})
(HERE/'judge_receipt.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=receipt['status'],protected_files=651,numeric_bindings=receipt['numeric_bindings'],
    bank_copies_audited=3,falsifiers=len(falsifiers),promotions_without_counterexample=len(unrefuted_promotions),
    rational_sign_positions=len(signs),lean_invoked=False,new_conclusions=0,cumulative_conclusions=208,victory=False,score=0),indent=2))
