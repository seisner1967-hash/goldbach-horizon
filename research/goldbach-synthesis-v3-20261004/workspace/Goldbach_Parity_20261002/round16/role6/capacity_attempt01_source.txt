"""NEW complete cap98 J1 window; least-prime capacity spent physically once."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from math import gcd
import argparse,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s
REPORT_SHA='f6f12c39afc445ce82482850c34482fa2450b9df1df7dbeef2089574b308128b'
SL,SU=Fraction(847,512),Fraction(11011,6144)

def affine_add(target,value,scale=1):
 s.add(target[0],value[0],scale);s.add(target[1],value[1],scale)

def affine_endpoints(value):
 out={}
 for name,point in [('lower',SL),('upper',SU)]:
  polynomial=dict(value[0]);s.add(polynomial,value[1],point)
  out[name]={'S_N_endpoint':str(point),'polynomial':s.serialize(polynomial),'sign_certificate':s.resolved(polynomial)}
 return out

def affine_serial(value):return {'A_constant_log_polynomial':s.serialize(value[0]),'B_S_N_coefficient':s.serialize(value[1]),'endpoints':affine_endpoints(value)}

def principal(theta,e,q):
 if e==1:return ({k:-v for k,v in s.multiply(theta,s.log_vector(q)).items()},dict(theta))
 return (s.multiply(theta,s.Lambda(e)),{k:s.mu(e)*v for k,v in theta.items()})

def bilateral(m):
 result=[]
 for p,exponent in s.factor(m):
  assert exponent==1;b=m//p;ratio=Fraction(1)
  for ell,_ in s.factor(b):
   if s.N%ell:ratio*=Fraction(ell-1,ell-2)
  result.append({'deleted_prime':p,'cofactor_b':b,'S_index_bN':b*s.N,'symbol':'S('+str(b*s.N)+')',
   'weight':'log('+str(p)+')/log('+str(m)+')','ratio_to_S_N':str(ratio),'cofactor_above_a':b>s.A,
   'index_is_actual_deleted_prime_cofactor':True,'S_bN_not_replaced_by_S_N':True})
 return result

def run():
 before=s.conservation.verify()
 assert s.sha256((s.ROOT/'agent2_or_incidence.md').read_bytes()).hexdigest()==REPORT_SHA
 qlow,qhigh=1000100,1000300;assert qhigh-qlow+1==201
 tested_q=[{'q':q,'factorization':s.factor(q),'prime':s.prime(q),'unit':gcd(q,s.N)==1} for q in range(qlow,qhigh+1)]
 qs=[v['q'] for v in tested_q if v['prime'] and v['unit']];assert all(q>s.A and q>s.M for q in qs)
 p0=next(p for p in s.historical.parity.PRIMES if p>2 and s.N%p);assert p0==3
 assert SL==Fraction(8,3)*Fraction(2541,4096) and SU==Fraction(8,3)*Fraction(11011,16384)
 cores=[e for e in range(1,99) if s.mu(e)!=0 and gcd(e,s.N)==1]
 assert all(len(s.factor(e))<=2 for e in cores) and min(e for e in cores if len(s.factor(e))==2)==21
 assert 3*7*11==231>98
 # Verify principal coefficient orientation, retaining every prime Lambda(e).
 coefficient_signs={}
 for e in cores:
  if e==1:continue
  coefficient=(s.Lambda(e),{():Fraction(s.mu(e))})
  ends=affine_endpoints(coefficient);wanted='NEGATIVE' if e==p0 else 'POSITIVE'
  assert all(v['sign_certificate']['sign']==wanted for v in ends.values())
  coefficient_signs[str(e)]={'formula':'Lambda(e)+mu(e)*S_N','endpoints':ends}
 local={};vec={};all_m=set();profile_count=0;pp=[]
 print(json.dumps({'stage':'complete_domain_fixed','q_count':len(qs),'core_count':len(cores),'candidate_vertices':len(qs)*len(cores)}),flush=True)
 for q in qs:
  cap=min(s.A,(s.N-s.Q-1)//q);assert cap==98
  c1_ends=affine_endpoints(({k:-v for k,v in s.log_vector(q).items()},{():Fraction(1)}))
  assert all(v['sign_certificate']['sign']=='NEGATIVE' for v in c1_ends.values())
  coefficient_signs['1,'+str(q)]={'formula':'S_N-log(q)','endpoints':c1_ends}
  for e in cores:
   m=e*q;n=s.N-m;assert m not in all_m;all_m.add(m)
   fs=s.factor(m);nf=s.factor(n);theta=s.theta(n);raw=s.Lambda(n) if n>1 and gcd(n,s.N)==1 else {}
   assert gcd(m,s.N)==gcd(n,s.N)==1 and s.M<=m<=s.N-s.Q-1 and n>s.Q
   assert all(ex==1 for _,ex in fs) and s.mu(m)==-s.mu(e)
   assert [p for p,_ in fs if p>s.A]==[q]
   shorts=[v for v in s.divisors(m) if v<=s.A];assert shorts==list(s.divisors(e))
   U=s.prefix(m,s.A)
   assert U=={k:-v for k,v in s.Lambda(e).items()}
   assert s.Lambda(m)==(s.log_vector(q) if e==1 else {})
   record={'e':e,'q':q,'m':m,'n':n,'e_factorization':s.factor(e),'q_factorization':s.factor(q),'m_factorization':fs,'n_factorization':nf,
    'rank_e':len(s.factor(e)),'mu_e':s.mu(e),'mu_m':s.mu(m),'Lambda_e':s.serialize(s.Lambda(e)),'Lambda_m':s.serialize(s.Lambda(m)),
    'theta_N_n':s.serialize(theta),'raw_Lambda_N_n':s.serialize(raw),'n_prime':bool(theta),'n_proper_power':bool(raw) and not bool(theta),
    'unit':True,'bulk':True,'n_above_original_Q':True,'short_divisors_complete':shorts,
    'short_terms':[{'d':v,'mu':s.mu(v),'log_d':s.serialize(s.log_vector(v))} for v in shorts],
    'U_a':s.serialize(U),'unique_large_prime_q':q,'canonical_core_e':m//q,'physical_vertex_count':1,
    'bilateral_actual_deleted_prime_indices':bilateral(m),'theta_raw_not_filtered_by_bulk':True}
   P=principal(theta,e,q);B={};rawB={};C=None;W=None
   if theta or raw or e in (1,p0):
    profile,B,C,W=s.source_profile(m);profile_count+=1
    if e==1:
     expected={k:-v for k,v in s.log_vector(q).items()};s.add(expected,W,-1)
    else:
     expected=dict(s.Lambda(e));s.add(expected,W,-s.mu(e))
    assert C==expected and profile['short_prefix']==s.serialize(U)
    rawB=s.multiply(raw,C);assert profile['B_raw_source']==s.serialize(rawB)
    record['physical_profile']=profile;record['kernel_computed']=True
    record['C_actual_sign_certificate']=s.resolved(C);record['B_actual_sign_certificate']=s.resolved(B)
    record['B_raw_actual_sign_certificate']=s.resolved(rawB)
   else:
    assert not theta and not raw
    record['kernel_computed']=False;record['B_actual_exact_zero']=True;record['B_raw_actual_exact_zero']=True
    record['W_literal_uncomputed']='W_a(N-eq,eq), Q original, ak<eq and gcd(k,(N-eq)N)=1'
    record['uncomputed_W_not_estimated']=True
   record['principal_affine']=affine_serial(P)
   record['principal_designated_resource']=e in (1,p0)
   local[(q,e)]=record;vec[(q,e)]=(B,rawB,P,C,W)
   if record['n_proper_power']:pp.append({'q':q,'e':e,'n':n,'factorization':nf,'raw_Lambda_N_n':record['raw_Lambda_N_n'],'B_raw':s.serialize(rawB)})
  print(json.dumps({'stage':'q_complete','q':q,'profiled_so_far':profile_count}),flush=True)
 totalP=({},{});demandP=({},{});resourceP=({},{});actual={};raw_actual={}
 Dpositive={};R13positive={};Rotherpositive={};demand_oriented={};resource_oriented={}
 rows=[];reuse=[];finiteA9=[];Lambda_witness=None
 for q in qs:
  qp=({},{});dp=({},{});rp=({},{});Bq={};rawq={};Dq={};R13q={};Rotherq={};doq={};roq={}
  active_first=[]
  for e in cores:
   B,rawB,P,C,W=vec[(q,e)];record=local[(q,e)]
   affine_add(qp,P);s.add(Bq,B);s.add(rawq,rawB)
   if e in (1,p0):affine_add(rp,P,-1);s.add(roq,B,-1)
   else:affine_add(dp,P);s.add(doq,B)
   sign=s.resolved(B)['sign']
   if sign=='POSITIVE':s.add(Dq,B)
   elif sign=='NEGATIVE':s.add(R13q if e in (1,p0) else Rotherq,B,-1)
   if record['n_prime']:
    active_first.append(e)
    if e==p0:
     margin=dict(C);s.add(margin,{():Fraction(1,288)})
     finiteA9.append({'q':q,'e':e,'C_actual':s.serialize(C),'C_plus_1over288_sign_certificate':s.resolved(margin),
      'source_onset_not_applied_here':True})
    if e>1 and s.prime(e) and Lambda_witness is None:
     difference=s.multiply(s.theta(record['n']),s.Lambda(e))
     Lambda_witness={'q':q,'e':e,'m':record['m'],'n':record['n'],'actual_term_if_Lambda_erased_difference':s.serialize(difference),
      'difference_sign_certificate':s.resolved(difference),'Lambda_e_not_zero':True}
  principal_def=(dict(dp[0]),dict(dp[1]));affine_add(principal_def,rp,-1);assert principal_def==qp
  assert s.difference(doq,roq)==Bq
  def13=s.difference(Dq,R13q);full_actual=s.difference(def13,Rotherq);assert full_actual==Bq
  affine_add(totalP,qp);affine_add(demandP,dp);affine_add(resourceP,rp)
  s.add(actual,Bq);s.add(raw_actual,rawq);s.add(Dpositive,Dq);s.add(R13positive,R13q);s.add(Rotherpositive,Rotherq)
  s.add(demand_oriented,doq);s.add(resource_oriented,roq)
  B3=vec[(q,p0)][0];other_positive=[e for e in active_first if e not in (1,p0) and s.resolved(vec[(q,e)][0])['sign']=='POSITIVE']
  if B3 and s.resolved(B3)['sign']=='NEGATIVE' and len(other_positive)>=2:
   inflation={k:-(len(other_positive)-1)*v for k,v in B3.items()}
   reuse.append({'q':q,'e3_m':p0*q,'positive_other_core_count':len(other_positive),'other_positive_cores':other_positive,
    'physical_resource3_count':1,'false_reuse_count':len(other_positive),'capacity_inflation_if_reused':s.serialize(inflation),
    'capacity_inflation_sign_certificate':s.resolved(inflation)})
  rows.append({'q':q,'active_first_prime_cores':active_first,'first_prime_count':len(active_first),
   'principal_demand':affine_serial(dp),'principal_resources13_once':affine_serial(rp),'principal_deficit_after_once_spending':affine_serial(qp),
   'actual_positive_demand_Dplus':s.serialize(Dq),'actual_designated_resources_R13plus':s.serialize(R13q),'actual_other_resources_Rotherplus':s.serialize(Rotherq),
   'actual_deficit_using_only_R13plus':s.serialize(def13),'actual_deficit_R13_sign_certificate':s.resolved(def13),
   'actual_entire_B_prime':s.serialize(Bq),'actual_entire_sign_certificate':s.resolved(Bq),
   'actual_signed_source_oriented_demand':s.serialize(doq),'actual_signed_source_oriented_resource':s.serialize(roq),
   'signed_orientation_not_assumed_positive':True,'actual_entire_B_raw':s.serialize(rawq),
   'positive_part_ledger_exact':True,'principal_and_actual_separate':True})
 deficitP=(dict(demandP[0]),dict(demandP[1]));affine_add(deficitP,resourceP,-1);assert deficitP==totalP
 deficit13=s.difference(Dpositive,R13positive);assert s.difference(deficit13,Rotherpositive)==actual
 assert s.difference(demand_oriented,resource_oriented)==actual
 rawextra=s.difference(raw_actual,actual)
 Pend=affine_endpoints(totalP);fullprincipalpositive=all(v['sign_certificate']['sign']=='POSITIVE' for v in Pend.values())
 actual13cert=s.resolved(deficit13);actualcert=s.resolved(actual)
 A9bad=[v for v in finiteA9 if v['C_plus_1over288_sign_certificate']['sign']=='POSITIVE']
 falsifiers=[{'claim':'the observed least-prime capacity supplies enough once-only resources for the entire selected core family',
  'status':'REFUTED_NEW_FINITE_FULL_PRINCIPAL_DEFICIT' if fullprincipalpositive else 'NO_COUNTEREXAMPLE_IN_WINDOW',
  'principal_deficit_endpoints':Pend,'finite_principal_only_not_source_coverage':True},
  {'claim':'erase Lambda(e) on all prime cores in the selected bracket','status':'REFUTED_NEW_PRIME_CORE_LAMBDA_TERM' if Lambda_witness else 'NO_COUNTEREXAMPLE_IN_WINDOW','witness':Lambda_witness},
  {'claim':'reuse the same e3 physical capacity for each positive core','status':'REFUTED_NEW_RESOURCE_REUSE' if reuse else 'NO_COUNTEREXAMPLE_IN_WINDOW',
   'witnesses':reuse,'physical_count_per_vertex':1},
  {'claim':'extend source A9 C_e3<=-1/288 to every finite prime e3 vertex here',
   'status':'REFUTED_NEW_FINITE_C3_COUNTEREXAMPLE' if A9bad else 'NO_COUNTEREXAMPLE_IN_WINDOW',
   'counterexamples':A9bad,'source_bound_not_refuted':True}]
 return {'status':'PASS_NEW_COMPLETE_CAP98_PHYSICAL_ONCE_CAPACITY_AND_DEMAND_ONLY','contract_FINAL2_sha256':REPORT_SHA,
  'N':s.N,'alpha':s.ALPHA,'a':s.A,'Q':s.Q,'M':s.M,'p0_least_odd_prime_not_dividing_N':p0,
  'q_window_complete':{'low':qlow,'high':qhigh,'integer_count':201,'all_q_tested':tested_q,'q_primes_unit':qs,
   'q_enumeration_not_limited_to_prime_list_10000':True,'q_factor_and_n_factor_trial_prime_limit':10000},
  'core_window_complete':{'cap':98,'all_e_integers_examined':True,'squarefree_unit_cores':cores,
   'ranks_counts':{str(rank):sum(len(s.factor(e))==rank for e in cores) for rank in range(5)},
   'rank3_or_higher_empty_finite_minimum231':True,'e1_and_all_prime_cores_and_rank2_retained':True},
  'S_N_source_enclosure_acquired':{'lower':str(SL),'upper':str(SU),'C2_acquired_lower':'2541/4096','C2_acquired_upper':'11011/16384',
   'factor_N':s.factor(s.N),'derived_multiplier_8over3':True,'not_numeric_substitution_for_actual_W':True},
  'principal_coefficient_orientation_endpoints':coefficient_signs,'physical_candidates':[local[k] for k in sorted(local)],
  'candidate_vertices':len(local),'computed_D_W_profiles':profile_count,'exact_zero_literal_W_vertices':len(local)-profile_count,
  'physical_unique_m_count':len(all_m),'sample_used_for_active_terms':False,'per_q':rows,
  'whole_principal_demand':affine_serial(demandP),'whole_principal_resources13_once':affine_serial(resourceP),
  'whole_principal_deficit':affine_serial(totalP),'whole_actual_positive_demand':s.serialize(Dpositive),
  'whole_actual_R13_resources_once':s.serialize(R13positive),'whole_actual_Rother_resources_once':s.serialize(Rotherpositive),
  'whole_actual_deficit_using_R13_only':s.serialize(deficit13),'whole_actual_deficit_R13_sign_certificate':actual13cert,
  'whole_actual_entire_B_prime':s.serialize(actual),'whole_actual_entire_sign_certificate':actualcert,
  'whole_actual_signed_source_oriented_demand':s.serialize(demand_oriented),'whole_actual_signed_source_oriented_resources':s.serialize(resource_oriented),
  'positive_part_and_signed_ledgers_both_exact':True,'all_physical_resources_counted_once':True,
  'finite_A9_comparisons_prime_e3':finiteA9,'raw_Lambda_N':{'proper_power_vertices_complete':pp,'proper_power_count':len(pp),
   'whole_actual_B_raw':s.serialize(raw_actual),'whole_raw_sign_certificate':s.resolved(raw_actual),
   'whole_raw_minus_prime':s.serialize(rawextra),'raw_not_given_U4':True,'no_mu_n_squared_filter':True},
  'ERROR_FALSIFIER':falsifiers,'U4_errors_literal':'each active theta vertex retains theta(n)*mu(m)*delta_m, delta_m=W_m+S(N); e1 has -theta*delta_m',
  'S_bN_indices_and_weights_preserved':True,'unpaid':['availability of least-prime pairs','all source OR and global union capacities','remaining ledger terms and W errors'],
  'imports_sha256':s.IMPORTS,'conservation_before':before,'conservation_after':s.conservation.verify(),
  'strict_rational_only':True,'finite_N_outside_source':True,'source_u_minimum':'10^24','global_D_N':False,'asymptotic':False,
  'payments':False,'Lean_called':False,'victory':False}

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=s.ROOT)
 args=parser.parse_args();data=run();out=s.conservation.output_directory(args.output_dir)
 (out/'capacity.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'q_count':len(data['q_window_complete']['q_primes_unit']),
  'core_count':len(data['core_window_complete']['squarefree_unit_cores']),'candidate_vertices':data['candidate_vertices'],
  'computed_profiles':data['computed_D_W_profiles'],'principal_deficit_signs':{k:v['sign_certificate']['sign'] for k,v in data['whole_principal_deficit']['endpoints'].items()},
  'actual_deficit_R13_sign':data['whole_actual_deficit_R13_sign_certificate']['sign'],'actual_entire_sign':data['whole_actual_entire_sign_certificate']['sign'],
  'proper_powers':data['raw_Lambda_N']['proper_power_count'],'victory':False}),flush=True)
