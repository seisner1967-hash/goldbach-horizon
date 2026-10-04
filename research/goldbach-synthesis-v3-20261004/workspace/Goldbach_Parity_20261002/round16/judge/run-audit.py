"""Single round16 independent audit: frozen arithmetic plus two NEW Lean modules.
No numerical producer, historical test, historical Lean build or PDF render runs.
"""
import sys
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
import ast,importlib.util,json,os,re,subprocess
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from math import gcd,isqrt,prod
from collections import Counter
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent;ROUND=HERE.parent;BASE=ROUND.parent
spec=importlib.util.spec_from_file_location('judge16_verify',HERE/'verify-frozen.py')
verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify);digest=verify.digest
def load(n):return json.loads((ROUND/n).read_bytes())
inputs=json.loads((HERE/'input_sha256.json').read_bytes())
verify.verify_inputs(inputs);before=verify.preservation(inputs)
numeric=load('numeric_manifest.json');final6=load('role6_final_receipt.json');closure=load('role6/closure_receipt.json')
assert numeric['files']==len(numeric['sha256'])==30
assert numeric['status']=='FINAL_FROZEN_NEW_ROUND16_NUMERIC_PARTIAL'
assert numeric['receipt_sha256']==digest(ROUND/'role6_final_receipt.json')
for n,h in numeric['sha256'].items():assert digest(ROUND/n)==h,n
assert numeric['reports_FINAL_sha256']==final6['reports_FINAL_sha256']==closure['reports_FINAL_sha256']=={
    v['report']:v['report_sha256'] for k,v in inputs['final_role_signals'].items() if k in ('role1','role2')}
assert numeric['new_bank_bindings']==final6['bindings']==closure['bindings']
assert final6['status']=='FINAL_ROUND16_ROLE6_NUMERIC_PARTIAL'
assert final6['canonical_attempts']==final6['isolated_replays']==2 and final6['real_failed_numeric_attempts']==0
assert final6['post_replay_runs']==0 and final6['old_PASS_replays']==0 and final6['old_Lean_or_dependency_recompiles']==0
assert final6['numeric_noLean'] and final6['noGlobal'] and final6['score']==0 and final6['victory'] is False
assert final6['own_asset_count_before_receipt']==len(final6['own_assets_sha256'])==29
for n,h in final6['own_assets_sha256'].items():assert digest(ROUND/n)==h,n
for n in inputs['sha256']:
    if n.endswith('.py'):ast.parse((ROUND/n).read_text(encoding='utf-8'),filename=n)
registry=load('previous_artifacts_sha256.json')['sha256']
gates={};bank_audits={}
statuses={'typei':'PASS_NEW_FULL_D77_TYPEI3_DRIFT_AND_LOCAL_CORRECTION_ONLY',
    'capacity':'PASS_NEW_COMPLETE_CAP98_PHYSICAL_ONCE_CAPACITY_AND_DEMAND_ONLY'}
for name,status in statuses.items():
    canonical=ROUND/(name+'.json');isolated=ROUND/('isolated_'+name)/(name+'.json')
    row=load('role6/'+name+'_replay_receipt.json');marker=load('role6/'+name+'_canonical_success.json')
    assert row['status']=='PASS_NEW_ROUND16_SEPARATE_ISOLATED_BYTES_AND_FIELDS_REPLAY'
    assert row['bank']==name and row['exit_code']==marker['exit_code']==0
    assert row['all_fields_identical'] and row['bytes_identical']
    assert Path(row['canonical'])==canonical and Path(row['isolated'])==isolated
    assert canonical.read_bytes()==isolated.read_bytes()
    gate=json.loads(canonical.read_bytes());assert gate==json.loads(isolated.read_bytes())
    assert digest(canonical)==digest(isolated)==row['output_sha256']==marker['output_sha256']
    assert digest(ROUND/(name+'_checks.py'))==row['source_sha256']==marker['producer_sha256']
    assert digest(Path(marker['source_snapshot']))==marker['producer_sha256']
    for entry in (row,marker):assert digest(Path(entry['log']))==entry['log_sha256']
    assert gate['status']==status
    assert (gate['N'],gate['alpha'],gate['a'],gate['Q'],gate['M'])==(100000000,100,3163,999999,1000000)
    for n,h in gate['imports_sha256'].items():assert registry[n]==h and digest(BASE/n)==h,n
    for entry in (row,gate):
        for k in ('global_D_N','asymptotic','payments','Lean_called','victory'):assert entry[k] is False
        for k in ('conservation_before','conservation_after'):assert entry[k]['status']=='PRESERVED' and entry[k]['files']==701
    assert gate['strict_rational_only'] and gate['finite_N_outside_source'] and gate['source_u_minimum']=='10^24'
    gates[name]=gate
    bank_audits[name]=dict(status=status,gate_sha256=digest(canonical),producer_sha256=row['source_sha256'],
        bytes=len(canonical.read_bytes()),all_bytes_identical=True,all_fields_identical=True,
        existing_isolated_replay_verified=True,producer_executed_by_judge=False)
signs={};falsifiers={};promotions={}
def walk(node,path):
    assert not isinstance(node,float),('Unexpected floating value',path)
    if isinstance(node,dict):
        if all(k in node for k in ('sign','lower','upper')):
            lo,hi=Fraction(node['lower']),Fraction(node['upper']);sign=node['sign']
            assert lo<=hi and sign in ('POSITIVE','NEGATIVE','ZERO'),path
            assert (lo>0 if sign=='POSITIVE' else hi<0 if sign=='NEGATIVE' else lo==hi==0),path
            signs[path]=sign
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
            promotions[key]=dict(claim=item['claim'],status=item['status'])
assert len(signs)==final6['rational_certificate_positions']==closure['certificates_positions_verified']==1879
assert len(falsifiers)==4 and len(promotions)==1

def vec(v):return {tuple(map(int,k.split(','))) if k else ():Fraction(c) for k,c in v.items() if Fraction(c)}
def add(*items):
    out={}
    for item in items:
        for k,v in item.items():out[k]=out.get(k,Fraction(0))+v
    return {k:v for k,v in out.items() if v}
def scale(item,c):return {k:v*c for k,v in item.items() if v*c}
def mul(left,right):
    out={}
    for k,v in left.items():
        for j,w in right.items():
            key=tuple(sorted(k+j));out[key]=out.get(key,Fraction(0))+v*w
    return {k:v for k,v in out.items() if v}
def log(n):return {(n,):Fraction(1)}
@lru_cache(None)
def prime(n):
    if n<2:return False
    if n%2==0:return n==2
    return all(n%d for d in range(3,isqrt(n)+1,2))
def factor_check(n,fs):
    assert prod(p**e for p,e in fs)==n
    assert [p for p,e in fs]==sorted(set(p for p,e in fs))
    assert all(e>=1 and prime(p) for p,e in fs)
def factor_vec(fs):return {(p,):Fraction(e) for p,e in fs}

# Pure validation of stored coefficient decompositions, without sieve/kernels.
t=gates['typei'];window=t['complete_candidate_window'];units=t['unit_counts']
assert (window['b_low'],window['b_high'],window['integer_count'])==(1038962,1168831,129870)
assert (window['n_lo'],window['n_hi'],window['X_exact'])==(10000013,19999926,9999914)
assert window['X_exact']==77*(window['integer_count']-1)+1
assert window['X_minus_d_times_integer_count']==-76 and window['all_integer_b_examined']
assert units['J']==51948 and units['J_classes_mod3']==[17316]*3 and units['J_star']==34632
beta=t['structural_beta'];A=len(beta);rho=Fraction(t['rho']);rhostar=Fraction(t['rho_star'])
assert A==t['A_beta']==216 and rho==Fraction(A,51948)==Fraction(2,481) and rhostar==Fraction(3,481)
assert len({v['b'] for v in beta})==A
for v in beta:
    assert prime(v['s']) and prime(v['q']) and v['b']==v['s']*v['q'] and v['m']==77*v['b']
    assert v['j']==100000000-v['m'] and 1038962<=v['b']<=1168831
    assert 11<v['s'] and 7*v['s']<=3163<11*v['s']<v['q'] and v['q']>3163
    assert gcd(v['m'],100000000)==1 and v['class_b_mod3']==v['b']%3!=0
    assert v['structural_without_candidate_prime_filter']
At=[sum(v['class_b_mod3']==i for v in beta) for i in range(3)]
assert At==t['A_classes_mod3']==[0,106,110]
f=t['f_candidate_divisible3'];g=t['g_other_nonzero_class'];assert (f,g)==(2,1)
drift=t['TypeI3_exact'];assert Fraction(drift['uniform_drift_Af_minus_rho_Jf'])==At[f]-rho*17316==38
assert Fraction(drift['corrected_drift_Af_minus_rho_star_Jf'])==At[f]-rhostar*17316==2
assert Fraction(drift['difference_exact'])==(rhostar-rho)*17316==36
T=[vec(t['theta_sums_classes'][str(i)]) for i in range(3)];thetaB=vec(t['theta_beta'])
assert [len(v) for v in T]==t['theta_prime_counts_classes']==[5067,5079,0]
assert len(thetaB)==sum(v['theta_prime'] for v in beta)==28 and not T[f]
assert thetaB=={(v['j'],):Fraction(1) for v in beta if v['theta_prime']}
for i,V in enumerate(T):
    for key,c in V.items():
        assert len(key)==1 and c==1 and (100000000-key[0])%77==0
        b=(100000000-key[0])//77
        assert b%3==i and 1038962<=b<=1168831 and gcd(b,100000000)==1
Gamma=add(thetaB,scale(add(*T),-rho));Gstar=add(thetaB,scale(add(T[1],T[2]),-rhostar))
L3=add(scale(T[g],rhostar),scale(add(T[0],T[g]),-rho))
assert Gamma==vec(t['Gamma_uniform'])==add(Gstar,L3)
assert Gstar==vec(t['Gamma_corrected_star']) and L3==vec(t['L3_reference_difference'])
assert Fraction(t['centered_norms_exact']['uniform_A_one_minus_rho'])==A*(1-rho)
assert Fraction(t['centered_norms_exact']['corrected_A_one_minus_rho_star'])==A*(1-rhostar)
raw=t['raw_Lambda_N'];pp=raw['proper_power_records_complete'];assert len(pp)==9
extras=[{} for _ in range(3)];extraB={}
for row in pp:
    assert prime(row['base_prime']) and row['exponent']>=2 and row['j']==row['base_prime']**row['exponent']
    assert row['j']==100000000-77*row['b'] and row['class_b_mod3']==row['b']%3
    extras[row['class_b_mod3']]=add(extras[row['class_b_mod3']],log(row['base_prime']))
    if row['beta']:extraB=add(extraB,log(row['base_prime']))
assert [sum(v['class_b_mod3']==i for v in pp) for i in range(3)]==raw['proper_power_count_classes']==[9,0,0]
rawT=[add(T[i],extras[i]) for i in range(3)];rawB=add(thetaB,extraB)
RG=add(rawB,scale(add(*rawT),-rho));RGS=add(rawB,scale(add(rawT[1],rawT[2]),-rhostar))
RL3=add(scale(add(rawT[1],rawT[2]),rhostar),scale(add(*rawT),-rho))
assert RG==vec(raw['raw_Gamma_uniform'])==add(RGS,RL3)
assert RGS==vec(raw['raw_Gamma_corrected_star']) and RL3==vec(raw['raw_reference_difference'])
ap=t['AP_front_and_principal'];X=window['X_exact']
assert Fraction(ap['X_over_phi231'])==Fraction(X,120)
assert Fraction(ap['uniform_rho_X_over_phi77'])==rho*Fraction(X,60)
assert Fraction(ap['L3_principal'])==(rhostar-2*rho)*Fraction(X,120)==-rho*Fraction(X,60)/4
assert t['D_W_kernels_recomputed'] is False and t['physical_brackets_not_tested_in_this_bank']
typei_summary=dict(complete_progression_integer_count=129870,units=51948,beta=216,
    beta_classes=At,uniform_drift='38',corrected_drift='2',theta_counts=[5067,5079,0],raw_properpowers=9,
    Gamma_sign=t['sign_certificates']['Gamma']['sign'],Gamma_star_sign=t['sign_certificates']['Gamma_star']['sign'],
    L3_sign=t['sign_certificates']['L3']['sign'],TypeII_estimated=False)

c=gates['capacity'];qs=c['q_window_complete']['q_primes_unit'];cores=c['core_window_complete']['squarefree_unit_cores']
tested=c['q_window_complete']['all_q_tested'];assert [v['q'] for v in tested]==list(range(1000100,1000301))
for row in tested:
    factor_check(row['q'],row['factorization']);assert row['prime']==prime(row['q'])
assert qs==[v['q'] for v in tested if v['prime'] and v['unit']] and len(qs)==18
assert len(cores)==34 and cores==sorted(set(cores)) and c['core_window_complete']['cap']==98
verts=c['physical_candidates'];lookup={(v['q'],v['e']):v for v in verts}
assert len(verts)==len(lookup)==c['candidate_vertices']==612
assert set(lookup)=={(q,e) for q in qs for e in cores} and len({v['m'] for v in verts})==612
SL,SU=Fraction(847,512),Fraction(11011,6144)
assert Fraction(c['S_N_source_enclosure_acquired']['lower'])==SL==Fraction(8,3)*Fraction(2541,4096)
assert Fraction(c['S_N_source_enclosure_acquired']['upper'])==SU==Fraction(8,3)*Fraction(11011,16384)
def affine(value):return (vec(value['A_constant_log_polynomial']),vec(value['B_S_N_coefficient']))
def affine_check(value):
    A0,B0=affine(value)
    for name,point in [('lower',SL),('upper',SU)]:
        endpoint=value['endpoints'][name]
        assert Fraction(endpoint['S_N_endpoint'])==point and vec(endpoint['polynomial'])==add(A0,scale(B0,point))
    return (A0,B0)
def affine_add(*items):return (add(*(v[0] for v in items)),add(*(v[1] for v in items)))
def affine_scale(item,z):return (scale(item[0],z),scale(item[1],z))
def physical_profile(p,row):
    assert p['m']==row['m'] and p['n']==row['n'] and p['bulk'] and p['unit']
    assert p['R']==min(999999,(p['m']-1)//3163) and p['original_cap_Q']==999999 and p['front_strict']
    assert p['k1_D']==p['k1_W'] and p['k1_joint_D_minus_W']=={}
    assert vec(p['short_prefix'])==vec(row['U_a'])==add(vec(p['low_prefix']),vec(p['annulus']))
    U,W=vec(p['short_prefix']),vec(p['W']);mu=row['mu_m'];Lm=vec(p['Lambda_m'])
    C=add(scale(add(Lm,U),-mu*mu),scale(W,mu))
    assert C==vec(p['C'])==scale(add(vec(p['D']),scale(W,-1)),-mu)
    assert vec(p['B_prime_source'])==mul(vec(p['theta_n']),C)
    assert vec(p['B_raw_source'])==mul(vec(p['raw_Lambda_N_n']),C)
def B(row,raw=False):
    return vec(row['physical_profile']['B_raw_source' if raw else 'B_prime_source']) if row['kernel_computed'] else {}
profiles=active=0
for row in verts:
    e,q=row['e'],row['q'];assert row['m']==e*q and row['n']==100000000-e*q
    for n,fs in [(e,row['e_factorization']),(q,row['q_factorization']),(row['m'],row['m_factorization']),(row['n'],row['n_factorization'])]:factor_check(n,fs)
    assert row['unit'] and row['bulk'] and row['n_above_original_Q'] and row['n']>999999
    assert row['mu_m']==-row['mu_e'] and gcd(row['m'],100000000)==1
    assert row['canonical_core_e']==e and row['unique_large_prime_q']==q and row['physical_vertex_count']==1
    assert vec(row['U_a'])==scale(vec(row['Lambda_e']),-1)
    theta,rawv=vec(row['theta_N_n']),vec(row['raw_Lambda_N_n'])
    assert bool(theta)==row['n_prime']==prime(row['n'])
    if row['kernel_computed']:
        physical_profile(row['physical_profile'],row);profiles+=1
        assert row['physical_profile']['theta_n']==row['theta_N_n'] and row['physical_profile']['raw_Lambda_N_n']==row['raw_Lambda_N_n']
    else:
        assert not theta and not rawv and row['B_actual_exact_zero'] and row['B_raw_actual_exact_zero']
        assert row['uncomputed_W_not_estimated']
    active+=bool(theta)
    expected=(scale(mul(theta,factor_vec(row['q_factorization'])),-1),theta) if e==1 else (mul(theta,vec(row['Lambda_e'])),scale(theta,row['mu_e']))
    assert affine_check(row['principal_affine'])==expected
    for idx in row['bilateral_actual_deleted_prime_indices']:
        assert idx['deleted_prime']*idx['cofactor_b']==row['m'] and idx['S_index_bN']==idx['cofactor_b']*100000000
        assert idx['index_is_actual_deleted_prime_cofactor'] and idx['S_bN_not_replaced_by_S_N']
assert profiles==c['computed_D_W_profiles']==128 and active==95
assert len(verts)-profiles==c['exact_zero_literal_W_vertices']==484 and c['sample_used_for_active_terms'] is False
totalB=totalRaw=Dplus=R13=Rother=orDemand=orResource={}
totalP=({},{});demandP=({},{});resourceP=({},{})
for row in c['per_q']:
    q=row['q'];local=[lookup[q,e] for e in cores]
    activecores=[v['e'] for v in local if v['n_prime']]
    assert row['active_first_prime_cores']==activecores and row['first_prime_count']==len(activecores)
    bp=add(*(B(v) for v in local));br=add(*(B(v,True) for v in local))
    dp=add(*(B(v) for v in local if v['kernel_computed'] and v['B_actual_sign_certificate']['sign']=='POSITIVE'))
    r13=scale(add(*(B(v) for v in local if v['e'] in (1,3) and v['kernel_computed'] and v['B_actual_sign_certificate']['sign']=='NEGATIVE')),-1)
    ro=scale(add(*(B(v) for v in local if v['e'] not in (1,3) and v['kernel_computed'] and v['B_actual_sign_certificate']['sign']=='NEGATIVE')),-1)
    od=add(*(B(v) for v in local if v['e'] not in (1,3)));ores=scale(add(*(B(v) for v in local if v['e'] in (1,3))),-1)
    assert bp==vec(row['actual_entire_B_prime'])==add(dp,scale(r13,-1),scale(ro,-1))==add(od,scale(ores,-1))
    assert br==vec(row['actual_entire_B_raw']) and add(dp,scale(r13,-1))==vec(row['actual_deficit_using_only_R13plus'])
    assert dp==vec(row['actual_positive_demand_Dplus']) and r13==vec(row['actual_designated_resources_R13plus'])
    assert ro==vec(row['actual_other_resources_Rotherplus'])
    pp=affine_add(*(affine(v['principal_affine']) for v in local))
    pd=affine_add(*(affine(v['principal_affine']) for v in local if v['e'] not in (1,3)))
    pr=affine_scale(affine_add(*(affine(v['principal_affine']) for v in local if v['e'] in (1,3))),-1)
    assert pp==affine_check(row['principal_deficit_after_once_spending'])==affine_add(pd,affine_scale(pr,-1))
    assert pd==affine_check(row['principal_demand']) and pr==affine_check(row['principal_resources13_once'])
    totalB=add(totalB,bp);totalRaw=add(totalRaw,br);Dplus=add(Dplus,dp);R13=add(R13,r13);Rother=add(Rother,ro)
    orDemand=add(orDemand,od);orResource=add(orResource,ores)
    totalP=affine_add(totalP,pp);demandP=affine_add(demandP,pd);resourceP=affine_add(resourceP,pr)
assert totalB==vec(c['whole_actual_entire_B_prime'])==add(Dplus,scale(R13,-1),scale(Rother,-1))
assert totalB==add(orDemand,scale(orResource,-1)) and totalRaw==vec(c['raw_Lambda_N']['whole_actual_B_raw'])
assert add(totalRaw,scale(totalB,-1))==vec(c['raw_Lambda_N']['whole_raw_minus_prime'])=={}
assert totalP==affine_check(c['whole_principal_deficit'])==affine_add(demandP,affine_scale(resourceP,-1))
assert R13==vec(c['whole_actual_R13_resources_once']) and not Rother and c['raw_Lambda_N']['proper_power_count']==0
assert c['raw_Lambda_N']['no_mu_n_squared_filter'] and c['all_physical_resources_counted_once']
assert len(c['finite_A9_comparisons_prime_e3'])==3
capacity_summary=dict(q_primes=18,cores=34,candidate_vertices=612,computed_profiles=128,
    exact_zero_literal_W=484,prime_incidences=95,prime_e1_incidence=0,prime_e3_incidence=3,raw_properpowers=0,
    principal_deficit_endpoint_signs={k:v['sign_certificate']['sign'] for k,v in c['whole_principal_deficit']['endpoints'].items()},
    entire_actual_sign=c['whole_actual_entire_sign_certificate']['sign'],global_capacity_estimated=False)
print(json.dumps(dict(stage='stored_numeric_audit_complete',certificate_positions=len(signs),falsifiers=4,
    promotions_without_counterexample=1,new_producer_invocations=0)),flush=True)

# Actual historical attempts are hashes/logs only; failed snapshots are not proofs.
producer_attempts=load('role3/build_receipt.json')['attempts'];assert len(producer_attempts)==13
diagnoses={1:'API_NAMES_UNAVAILABLE',2:'BETA_REDUCTION_COERCIONS_COMMUTATION_INDUCTION_SYNTAX',
    3:'DENOMINATOR_NORMALIZATION',5:'FINITE_SUP_LAMBDA_FOCUS_CAST_SUBTRACTION',6:'REAL_NUMERAL_NORMALIZATION',
    7:'CONDITIONAL_LOCAL_FACTOR_SIMPLIFICATION_AND_API',8:'INDEX_DOMAIN_INFERENCE',
    10:'SMALL_PRIME_FINSET_EVALUATION',12:'DEPENDENT_CONDITIONAL_REDUCTION'}
failures=[];passes=[]
for row in producer_attempts:
    assert digest(row['snapshot'])==row['snapshot_sha256']==row['source_sha256']
    assert digest(row['log'])==row['log_sha256']
    output=Path(row['log']).read_text(encoding='utf-8-sig')
    if row['exit_code']:
        assert 'error:' in output and row['attempt'] in diagnoses
        failures.append(dict(attempt=row['attempt'],exit_code=row['exit_code'],source_sha256=row['source_sha256'],
            log_sha256=row['log_sha256'],diagnosis=diagnoses[row['attempt']],parity_diagnostic=False))
    else:passes.append(row['attempt'])
assert len(failures)==9 and passes==[4,9,11,13]
assert producer_attempts[-1]['source_sha256']==digest(ROUND/'role3/EulerAnchor.lean')
for role in (3,4):
    receipt=load(f'role{role}/final_receipt.json')
    assert receipt['victory'] is False and receipt['report_sha256']==inputs['final_role_signals'][f'role{role}']['report_sha256']
    for row in receipt['files']:assert digest(row['path'])==row['sha256'] and Path(row['path']).stat().st_size==row['bytes']
    if role==3:
        for row in receipt['input_bindings']:assert digest(row['path'])==row['sha256']
LEAN=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
assert digest(LEAN)=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
CACHE=Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
commit=subprocess.run(['git','rev-parse','HEAD'],cwd=CACHE/'mathlib',capture_output=True,text=True,check=True).stdout.strip()
assert commit=='9837ca9d65d9de6fad1ef4381750ca688774e608'
BUILD=HERE/'build';assert not BUILD.exists(),'Fresh compile folder already exists';BUILD.mkdir()
DEPS=BASE/'round13/role3/dependencies'
packages=['aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq']
env=dict(os.environ);env['LEAN_PATH']=';'.join(map(str,[BUILD,DEPS,*[CACHE/p/'.lake/build/lib' for p in packages]]))
compiled=[];allowed={'propext','Classical.choice','Quot.sound'}
for role,name,theorems,defs in [(4,'LeastMissingPrimeMargin',9,0),(3,'EulerAnchor',27,8)]:
    source=ROUND/f'role{role}'/(name+'.lean');snapshot=BUILD/(name+'.lean');snapshot.write_bytes(source.read_bytes())
    text=snapshot.read_text(encoding='utf-8');assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
    decls=re.findall(r'^(?:lemma|theorem)\s+(\w+)',text,re.M)
    definitions=re.findall(r'^(?:noncomputable\s+)?def\s+(\w+)',text,re.M)
    assert len(decls)==theorems and len(definitions)==defs
    cmd=[str(LEAN),'-o',name+'.olean',name+'.lean'];start=datetime.now(timezone.utc).isoformat()
    result=subprocess.run(cmd,cwd=BUILD,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
    logpath=HERE/(name+'_fresh.log');logpath.write_text(result.stdout+result.stderr,encoding='utf-8')
    assert digest(source)==digest(snapshot)==inputs['sha256'][f'role{role}/{name}.lean']
    output=result.stdout+result.stderr
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S)
    record=dict(role=role,module=name,command=cmd,started_utc=start,completed_utc=datetime.now(timezone.utc).isoformat(),
        exit_code=result.returncode,source_sha256=digest(snapshot),log_sha256=digest(logpath),
        theorem_count=theorems,definition_count=defs,printed_axiom_positions=len(rows),
        warnings=output.count('warning:'),errors=output.count('error:'),fresh_source_copy=True,old_dependencies_rebuilt=False)
    (HERE/(name+'_fresh_receipt.json')).write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    assert result.returncode==0 and record['warnings']==record['errors']==0,(name,record)
    assert len(rows)==theorems
    for decl,axioms in rows:assert set(v.strip() for v in axioms.split(',') if v.strip())<=allowed,(decl,axioms)
    assert {decl.rsplit('.',1)[-1] for decl,axioms in rows}==set(decls)
    record['olean_sha256']=digest(BUILD/(name+'.olean'));record['axioms_standard_only']=True
    compiled.append(record)
    print(json.dumps(dict(stage='independent_new_Lean_compile',module=name,exit_code=0,theorems=theorems,definitions=defs,warnings=0)),flush=True)
verify.verify_inputs(inputs);after=verify.preservation(inputs);assert before==after
receipt=dict(round=16,status='PARTIAL_CANONICAL_REAL_SINGULAR_MARGIN_COMPILED_GLOBAL_INCIDENCE_OPEN',
    recorded_at_utc=datetime.now(timezone.utc).isoformat(),input_manifest_sha256=digest(HERE/'input_sha256.json'),
    input_sha256=inputs['sha256'],external_sha256=inputs['external_sha256'],final_role_signals=inputs['final_role_signals'],
    numeric_manifest_sha256=digest(ROUND/'numeric_manifest.json'),numeric_bindings=30,
    numerical_audit_mode='READ_ONLY_EXISTING_TWO_ISOLATED_COPIES_AND_STORED_EXACT_COEFFICIENTS',bank_audits=bank_audits,
    rational_signs=signs,rational_sign_count=len(signs),rational_sign_distribution=dict(Counter(signs.values())),
    unresolved_signs=0,floating_values=0,strict_rational_interval_signs=True,
    falsifiers=falsifiers,falsifier_count=4,promotions_without_counterexample=promotions,
    typei=typei_summary,capacity=capacity_summary,producer_Lean_failures=failures,
    producer_role3_compilations=13,producer_role3_API_probes=1,producer_role3_candidate_compilations=12,
    producer_role3_PASS_attempts=passes,producer_role4_compilations=1,actual_numeric_failures=0,
    independent_new_compiles=compiled,independent_compile_invocations=2,independent_compile_failures=0,
    new_lean_modules=2,new_lean_conclusions=36,new_lean_definitions=8,
    cumulative_auxiliary_modules=17,cumulative_auxiliary_conclusions=244,
    preservation_before=before,preservation_after=after,lean_invoked=True,
    Lean_compiler_sha256=digest(LEAN),mathlib_commit=commit,
    source_A7_certified=True,A7_input='2541/4096 <= actual GoldbachRound11.twinConstant',
    canonical_p0_certified=True,real_tprod_convergence_and_tail_proved=True,source_A9_Lean_certified=False,
    numerical_producers_invoked_by_judge=False,old_banks_replayed=False,old_Lean_or_dependency_rebuilt=False,old_PDF_rerendered=False,
    finite_N=100000000,source_u_minimum='10^24',finite_test_is_source_onset_test=False,
    semantic_open_obligations=['Availability and weighted mass of q,N-p0q prime incidences',
        'Gamma_star/full TypeII and weighted comparison with actual parents',
        'F6 OR and global union capacity consumed physically once',
        'Whole ledger D_N including raw powers, W errors, long cofactors and source guards'],
    global_D_N_estimated=False,parity_bypass_certified=False,victory=False,score=0,
    judge_scripts_sha256={p.name:digest(p) for p in sorted(HERE.glob('*.py'))})
assert not (HERE/'judge_receipt.json').exists()
(HERE/'judge_receipt.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=receipt['status'],frozen_files=inputs['file_count'],protected_files=701,
    numeric_bindings=30,existing_copies=2,rational_certificate_positions=len(signs),new_modules=2,new_theorems=36,new_definitions=8,
    cumulative_modules=17,cumulative_theorems=244,actual_producer_Lean_failures=9,
    independent_compiles=2,independent_compile_failures=0,victory=False,score=0),indent=2),flush=True)
