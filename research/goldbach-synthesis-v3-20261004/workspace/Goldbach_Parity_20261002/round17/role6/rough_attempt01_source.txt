"""Selected NEW round17 four-form partition and exact finite Selberg square."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from math import gcd,lcm,prod
import argparse,json,re
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s
REPORT_SHA='2c3b2dfadb507925b0fdc92a69b5174353f8f93ba2fc188175dadf05b38ad8d7'
QL,QH,Z,CAP=1200100,1200300,100,82
SL,SU=Fraction(847,512),Fraction(11011,6144)

def affine_add(target,value,scale=1):s.add(target[0],value[0],scale);s.add(target[1],value[1],scale)
def affine_serial(value):
 endpoints={}
 for name,point in [('lower',SL),('upper',SU)]:
  vector=dict(value[0]);s.add(vector,value[1],point)
  endpoints[name]={'S_N':str(point),'sign_certificate':s.resolved(vector)}
 return {'constant_exact':s.serialize(value[0]),'S_N_coefficient_exact':s.serialize(value[1]),'endpoints':endpoints}
def principal(theta,e,q):
 if e==1:return ({key:-v for key,v in s.multiply(theta,s.log_vector(q)).items()},dict(theta))
 return (s.multiply(theta,s.Lambda(e)),{key:s.mu(e)*v for key,v in theta.items()})
def recipe(entries,vector):
 return {'exact_recipe':[{'m':m,'axis':axis,'scale':str(scale)} for m,axis,scale in entries],
  'evaluation':'sum scale*axis(n)*C_recipe(m); primitive W appears once in kernel_catalog',
  'sign_certificate':s.resolved(vector)}
def bilateral(m):
 rows=[]
 for p,power in s.factor(m):
  assert power==1;b=m//p;ratio=Fraction(1)
  for ell,_ in s.factor(b):
   if s.N%ell:ratio*=Fraction(ell-1,ell-2)
  rows.append({'deleted_prime':p,'b':b,'S_index_bN':b*s.N,'ratio_to_S_N':str(ratio),
   'weight':'log('+str(p)+')/log('+str(m)+')','cofactor_above_a':b>s.A,'S_bN_not_substituted':True})
 return rows
def old_vertex_scan():
 """Read frozen values only, deduplicating copies; never evaluate old kernels."""
 found=set();seen_hashes=set();inputs={}
 for relative,digest in sorted(s.PROTECTED.items()):
  if not relative.endswith('.json') or digest in seen_hashes:continue
  seen_hashes.add(digest);path=s.BASE/relative;assert s.sha256(path.read_bytes()).hexdigest()==digest
  data=json.loads(path.read_text(encoding='utf-8'));inputs[relative]=digest;stack=[data]
  while stack:
   item=stack.pop()
   if isinstance(item,dict):
    for key,value in item.items():
     if type(value) is int and (key in ('m','m0','m1') or key.endswith('_m')) and 0<value<s.N:found.add(value)
     if isinstance(value,(dict,list)):stack.append(value)
   elif isinstance(item,list):stack.extend(value for value in item if isinstance(value,(dict,list)))
 return found,inputs
def F(e,q):return q*(s.N-e*q)*(s.N-q)*(s.N-3*q)
def crt_roots(modulus,local_roots):
 residues=[0];previous=1
 for ell,_ in s.factor(modulus):
  inverse=pow(previous,-1,ell)
  residues=[a+previous*((b-a)*inverse%ell) for a in residues for b in local_roots[ell]]
  previous*=ell
 assert previous==modulus and len(residues)==len(set(residues))
 assert all(0<=a<modulus for a in residues)
 return sorted(residues)
def sieve(e,primes,domains):
 roots={ell:[x for x in range(ell) if F(e,x)%ell==0] for ell in primes}
 delta=s.N*e*3*(e-1)*(e-3)*2
 for ell,values in roots.items():
  assert 1<=len(values)<=min(4,ell)
  if delta%ell:assert len(values)==4
  assert not all((s.N-e*x)%ell==0 for x in range(ell))
  assert not all((s.N-3*x)%ell==0 for x in range(ell))
 saturation=[ell for ell,values in roots.items() if len(values)==ell]
 values=[F(e,q) for q in range(QL,QH+1)]
 rough=[all(value%ell for ell in primes) for value in values]
 local={'e':e,'Delta_e':delta,'rho_roots_all_primes_le100':{str(ell):{'rho':len(rs),'roots':rs} for ell,rs in roots.items()},
  'all_201_integer_q_examined':True,'rough_integer_q':[q for q,ok in zip(range(QL,QH+1),rough) if ok],
  'physical_R_prime_q':domains['R'],'physical_R_count':len(domains['R']),
  'physical_A_prime_q':domains['A'],'physical_S_prime_q':domains['S']}
 if saturation:
  assert not any(rough) and not domains['R']
  local.update({'status':'LOCAL_SATURATION_ROUGH_CELL_EMPTY','saturating_primes':saturation,'G_or_lambda_not_formed':True})
  return local
 support=[d for d in range(1,Z+1) if s.mu(d)!=0]
 h={d:prod((Fraction(len(roots[ell]),ell-len(roots[ell])) for ell,_ in s.factor(d)),start=Fraction(1)) for d in support}
 G=sum(h.values(),Fraction(0));assert G>0
 weights={}
 for d in support:
  gd=sum((h[r] for r in support if r<=Z//d and gcd(r,d)==1),Fraction(0))
  inverse=prod((Fraction(ell,ell-len(roots[ell])) for ell,_ in s.factor(d)),start=Fraction(1))
  weights[d]=s.mu(d)*inverse*gd/G
 assert weights[1]==1 and all(abs(value)<=1 for value in weights.values())
 signed_lcm={};absolute_lcm={}
 for d in support:
  for t in support:
   modulus=lcm(d,t);term=weights[d]*weights[t]
   signed_lcm[modulus]=signed_lcm.get(modulus,Fraction(0))+term
   absolute_lcm[modulus]=absolute_lcm.get(modulus,Fraction(0))+abs(term)
 gram=Fraction(0);signed_remainder=Fraction(0);absolute_error=Fraction(0);crt_bound=Fraction(0);table=[]
 for modulus in sorted(signed_lcm):
  residues=crt_roots(modulus,roots);rho=prod(len(roots[ell]) for ell,_ in s.factor(modulus))
  assert len(residues)==rho
  actual=sum(value%modulus==0 for value in values)
  crt_count=sum((QH-a)//modulus-(QL-1-a)//modulus for a in residues)
  assert actual==crt_count
  rem=Fraction(actual)-Fraction(201*rho,modulus);assert abs(rem)<=rho
  gram+=signed_lcm[modulus]*Fraction(rho,modulus)
  signed_remainder+=signed_lcm[modulus]*rem
  absolute_error+=absolute_lcm[modulus]*abs(rem);crt_bound+=absolute_lcm[modulus]*rho
  table.append({'lcm':modulus,'rho_product':rho,'integer_count_exact':actual,'remainder_exact':str(rem),
   'lambda_pair_sum':str(signed_lcm[modulus]),'absolute_lambda_pair_sum':str(absolute_lcm[modulus]),
   'CRT_roots_sha256':s.sha256(json.dumps(residues,separators=(',',':')).encode()).hexdigest()})
 assert gram==1/G
 diagonals={}
 for r in support:
  inner=sum((weights[d]*Fraction(prod(len(roots[ell]) for ell,_ in s.factor(d)),d) for d in support if d%r==0),Fraction(0))
  assert inner==s.mu(r)*h[r]/G;diagonals[str(r)]=str(inner)
 squares=[];square_sum=Fraction(0)
 for q,value,ok in zip(range(QL,QH+1),values,rough):
  inner=sum((weights[d] for d in support if value%d==0),Fraction(0));square=inner*inner
  assert Fraction(ok)<=square
  if ok:assert inner==1
  square_sum+=square;squares.append({'q':q,'rough_mask':int(ok),'divisor_lambda_sum':str(inner),'square':str(square)})
 main=Fraction(201)/G
 assert square_sum==main+signed_remainder and square_sum<=main+absolute_error<=main+crt_bound
 assert len(domains['R'])<=sum(rough)<=square_sum
 local.update({'status':'EXACT_FINITE_SELBerg_SQUARE_VERIFIED','G_exact':str(G),'support_squarefree_d_le100':support,
  'h_exact':{str(d):str(h[d]) for d in support},'lambda_exact':{str(d):str(weights[d]) for d in support},
  'lambda1_one_all_abs_le1':True,'mobius_diagonal_inner_sums':diagonals,'principal_quadratic_exact':str(gram),
  'principal_equals_1_over_G':True,'CRT_lcm_catalog':table,'CRT_root_recipe':'CRT of stored local root lists; no root multiplicity assumed',
  'integer_squares_201':squares,'square_sum_exact':str(square_sum),'main_201_over_G':str(main),
  'signed_CRT_remainder_exact':str(signed_remainder),'absolute_pairwise_remainder_error':str(absolute_error),
  'CRT_plus1_absolute_bound':str(crt_bound),'rough_upper_main_plus_abs_error':str(main+absolute_error),
  'rough_upper_main_plus_CRT_bound':str(main+crt_bound),'weak_upper_published_without_replacement':True})
 return local

def run():
 before=s.conservation.verify();assert s.sha256((s.ROOT/'agent2_capacity_incidence.md').read_bytes()).hexdigest()==REPORT_SHA
 assert QH-QL+1==201 and all(min(s.A,(s.N-s.Q-1)//q)==CAP for q in range(QL,QH+1))
 tested=[{'q':q,'factorization':s.factor(q),'prime':s.prime(q),'unit':gcd(q,s.N)==1} for q in range(QL,QH+1)]
 qs=[row['q'] for row in tested if row['prime'] and row['unit']]
 primes=[p for p in range(2,Z+1) if s.prime(p)]
 p0=next(p for p in range(3,100) if s.prime(p) and s.N%p);assert p0==3
 all_e=[{'e':e,'factorization':s.factor(e),'squarefree':s.mu(e)!=0,'unit':gcd(e,s.N)==1} for e in range(1,CAP+1)]
 cores=[row['e'] for row in all_e if row['squarefree'] and row['unit']]
 assert 1 in cores and 3 in cores and all(len(s.factor(e))<=2 for e in cores) and 3*7*11>CAP
 old_m,old_inputs=old_vertex_scan();all_m=set();candidates={};kernels={};vectors={};profiles=0;properpowers=[];qrows=[]
 partitions={e:{key:[] for key in ('A','R','S')} for e in cores if e>3}
 print(json.dumps({'stage':'domain_fixed','q_primes':len(qs),'cores':len(cores),'candidate_vertices':len(qs)*len(cores),'old_m_values_read_only':len(old_m)}),flush=True)
 for q in qs:
  n1,n3=s.N-q,s.N-3*q;inc1,inc3=bool(s.theta(n1)),bool(s.theta(n3))
  small1=[p for p,_ in s.factor(n1) if p<=Z];small3=[p for p,_ in s.factor(n3) if p<=Z]
  cell='A' if inc1 or inc3 else ('R' if not small1 and not small3 else 'S')
  witness=None
  if cell=='S':
   j=1 if small1 else 3;ell=min(small1 if small1 else small3)
   assert s.N%ell and j%ell and (s.N-j*q)%ell==0
   witness={'j':j,'ell_least_prime_factor':ell,'n_j':s.N-j*q,'n_j_factorization':s.factor(s.N-j*q),
    'priority_j1_if_small_factor_else_j3':True,'n1_rough_required_on_j3_face':not small1 if j==3 else None}
  qrows.append({'q':q,'cell_for_active_demands':cell,'n1':n1,'n3':n3,'n1_factorization':s.factor(n1),'n3_factorization':s.factor(n3),
   'I1':inc1,'I3':inc3,'n1_small_prime_factors':small1,'n3_small_prime_factors':small3,'small_factor_witness':witness,
   'resource_m_ids':[q,3*q],'resource_physical_count_each':1})
  for e in cores:
   m=e*q;n=s.N-m;assert m not in all_m;all_m.add(m)
   assert gcd(m,s.N)==gcd(n,s.N)==1 and s.M<=m<=s.N-s.Q-1 and n>s.Q
   fs=s.factor(m);nf=s.factor(n);theta=s.theta(n);raw=s.Lambda(n)
   assert all(power==1 for _,power in fs) and s.mu(m)==-s.mu(e) and [p for p,_ in fs if p>s.A]==[q]
   shorts=[d for d in s.divisors(m) if d<=s.A];assert shorts==list(s.divisors(e))
   U=s.prefix(m,s.A);assert U=={key:-v for key,v in s.Lambda(e).items()}
   assert s.Lambda(m)==(s.log_vector(q) if e==1 else {})
   if e>3 and theta:partitions[e][cell].append(q)
   excluded=False
   if witness and e%witness['ell_least_prime_factor']==witness['j']%witness['ell_least_prime_factor']:
    assert not theta;excluded=True
    if raw:assert nf[0][0]==witness['ell_least_prime_factor'] and len(nf)==1
   row={'m':m,'q':q,'e':e,'n':n,'n_factorization':nf,'mu_m':s.mu(m),'theta_exact':s.serialize(theta),'raw_Lambda_N_exact':s.serialize(raw),
    'prime_axis_active':bool(theta),'proper_power_axis_active':bool(raw) and not bool(theta),'unit':True,'bulk':True,'n_above_original_Q':True,
    'short_divisors_complete':shorts,'U_a_exact':s.serialize(U),'Lambda_m_exact':s.serialize(s.Lambda(m)),
    'cell':cell if e>3 and theta else None,'small_factor_exclusion_verified':excluded,
    'physical_count':1,'unique_large_prime_q':q,'canonical_e':m//q,'bilateral_actual_deleted_prime_indices':bilateral(m)}
   B={};rawB={};C=None
   if theta or raw or e in (1,3):
    assert m not in old_m,('OLD_VERTEX_RECOMPUTATION_PROHIBITED',m)
    kernel,C,W=s.active_kernel(m);profiles+=1
    expected={key:-v for key,v in s.log_vector(q).items()} if e==1 else dict(s.Lambda(e))
    s.add(expected,W,-1 if e==1 else -s.mu(e));assert C==expected
    assert kernel['whole_U_a']==s.serialize(U)
    kernels[str(m)]=kernel;B=s.multiply(theta,C);rawB=s.multiply(raw,C)
    row.update({'kernel_ref':str(m),'C_recipe':{'constant_exact':s.serialize({key:-v for key,v in s.log_vector(q).items()} if e==1 else s.Lambda(e)),
     'W_scale':str(-1 if e==1 else -s.mu(e)),'W_ref':str(m)},
     'C_sign_certificate':s.resolved(C),'B_theta_sign_certificate':s.resolved(B),'B_raw_sign_certificate':s.resolved(rawB)})
   else:
    assert not theta and not raw
    row.update({'kernel_ref':None,'B_theta_exact_zero':True,'B_raw_exact_zero':True,
     'W_literal':'W_a(N-eq,eq); Q original, ak<eq, gcd(k,(N-eq)N)=1','W_not_estimated':True})
   candidates[str(m)]=row;vectors[m]=(B,rawB,principal(theta,e,q))
   if row['proper_power_axis_active']:properpowers.append({'m':m,'e':e,'q':q,'n':n,'factorization':nf,'raw_Lambda_N_exact':s.serialize(raw)})
  print(json.dumps({'stage':'q_kernels_complete','q':q,'profiles':profiles}),flush=True)
 print(json.dumps({'stage':'physical_catalog_complete','profiles':profiles,'properpowers':len(properpowers)}),flush=True)
 wholeP=({},{});demandP=({},{});resourceP=({},{});whole={};whole_raw={};T={key:{} for key in ('A','R','S')};Runique={}
 whole_entries=[];raw_entries=[];Tentries={key:[] for key in T};Rentries=[];perq=[]
 signed_parts={key:{} for key in T};signed_entries={key:[] for key in T};falsifier_absence=None
 for qrow in qrows:
  q=qrow['q'];qP=({},{});qT={key:{} for key in T};qTentries={key:[] for key in T};qR={};qRentries=[];qB={};qBentries=[]
  for e in cores:
   m=e*q;B,rawB,P=vectors[m];row=candidates[str(m)];affine_add(wholeP,P);affine_add(qP,P)
   s.add(whole,B);s.add(whole_raw,rawB);s.add(qB,B)
   if B:whole_entries.append((m,'theta',1));qBentries.append((m,'theta',1))
   if rawB:raw_entries.append((m,'raw',1))
   sign=row.get('B_theta_sign_certificate',{'sign':'ZERO'})['sign']
   if e in (1,3):
    affine_add(resourceP,P,-1)
    if sign=='NEGATIVE':
     s.add(Runique,B,-1);s.add(qR,B,-1);Rentries.append((m,'theta',-1));qRentries.append((m,'theta',-1))
   else:
    affine_add(demandP,P)
    if B:
     cell=qrow['cell_for_active_demands'];s.add(signed_parts[cell],B);signed_entries[cell].append((m,'theta',1))
     if sign=='POSITIVE':
      s.add(T[cell],B);s.add(qT[cell],B);Tentries[cell].append((m,'theta',1));qTentries[cell].append((m,'theta',1))
     if cell=='S' and falsifier_absence is None:
      falsifier_absence={'m':m,'q':q,'e':e,'n_e':row['n'],'n_e_factorization':row['n_factorization'],
       'I1':False,'I3':False,'small_factor_witness':qrow['small_factor_witness']}
  qpositive={};qpositive_entries=[]
  for cell in T:s.add(qpositive,qT[cell]);qpositive_entries+=qTentries[cell]
  qdef=s.difference(qpositive,qR)
  perq.append({'q':q,'cell':qrow['cell_for_active_demands'],
   'T_positive_parts':{cell:recipe(qTentries[cell],qT[cell]) for cell in T},'resources_once':recipe(qRentries,qR),
   'positive_demand_minus_unique_resources':recipe(qpositive_entries+[(m,axis,-scale) for m,axis,scale in qRentries],qdef),
   'entire_signed_theta_sum':recipe(qBentries,qB),'entire_principal_affine':affine_serial(qP)})
 totalT={};totalTentries=[]
 for cell in T:s.add(totalT,T[cell]);totalTentries+=Tentries[cell]
 deficit=s.difference(totalT,Runique);defentries=totalTentries+[(m,axis,-scale) for m,axis,scale in Rentries]
 principal_def=(dict(demandP[0]),dict(demandP[1]));affine_add(principal_def,resourceP,-1);assert principal_def==wholeP
 assert sum(len(partitions[e][cell]) for e in partitions for cell in T)==sum(bool(candidates[str(e*q)]['prime_axis_active']) for e in cores if e>3 for q in qs)
 sieve_rows=[]
 for e in cores:
  if e>3:
   sieve_rows.append(sieve(e,primes,partitions[e]));print(json.dumps({'stage':'sieve_core_complete','e':e,'status':sieve_rows[-1]['status']}),flush=True)
 collisions=[{'e':row['e'],'ell':int(ell),'rho':local['rho'],'roots':local['roots']} for row in sieve_rows for ell,local in row['rho_roots_all_primes_le100'].items() if local['rho']!=4]
 u_lower=s.difference(s.log_vector(s.N),{():Fraction(18)});ell_lower=s.difference(s.log_vector(18),{():Fraction(2)})
 assert s.resolved(u_lower)['sign']==s.resolved(ell_lower)['sign']=='POSITIVE'
 budget_upper=Fraction(s.N,8192*18*2);promotion_difference=s.difference(totalT,{():budget_upper});promotion_sign=s.resolved(promotion_difference)
 rawextra=s.difference(whole_raw,whole);rawextra_entries=[(m,'raw',1) for m,_,_ in raw_entries]+[(m,'theta',-1) for m,_,_ in whole_entries]
 core_catalog={str(e):{'factorization':s.factor(e),'mu_e':s.mu(e),'Lambda_e_exact':s.serialize(s.Lambda(e)),
  'rank':len(s.factor(e)),'divisors_complete':list(s.divisors(e)),
  'principal_coefficient_affine':affine_serial((s.Lambda(e),{():Fraction(s.mu(e))})) if e>1 else 'S_N-logq; see physical q vertex'} for e in cores}
 return {'status':'PASS_NEW_FOUR_FORM_ROUGH_PARTITION_AND_EXACT_FINITE_SELBerg_ONLY','contract_FINAL2_sha256':REPORT_SHA,
  'N':s.N,'alpha':s.ALPHA,'a':s.A,'Q':s.Q,'M':s.M,'z':Z,'p0_least_odd_prime_missing_N':3,
  'q_window_complete':{'low':QL,'high':QH,'integer_count':201,'all_q_tested':tested,'prime_unit_q':qs,
   'enumeration_not_limited_to_prime_base10000':True,'factor_trial_primes_complete_through10000':True},
  'core_window_complete':{'cap_all_201_q':CAP,'all_e_examined':all_e,'squarefree_unit_cores':cores,'core_catalog':core_catalog,
   'rank3_or_more_empty_finite_minunit231_gt82':True},
  'old_vertices_readonly_guard':{'frozen_JSON_sha256':old_inputs,'distinct_old_m_values':len(old_m),'new_computed_m_disjoint':True,'old_W_not_evaluated':True},
  'physical_candidates_catalog':candidates,'kernel_catalog':kernels,'candidate_count':len(candidates),'kernel_count':profiles,
  'literal_zero_axis_W_count':len(candidates)-profiles,'unique_physical_m_count':len(all_m),
  'source_enclosure_affine_only':{'S_N_lower':str(SL),'S_N_upper':str(SU),'actual_W_not_replaced':True},
  'q_resources_and_small_factor_cells':qrows,'partition_active_demands':{str(e):parts for e,parts in partitions.items()},'per_q':perq,
  'whole_positive_parts':{cell:recipe(Tentries[cell],T[cell]) for cell in T},
  'whole_signed_parts':{cell:recipe(signed_entries[cell],signed_parts[cell]) for cell in T},
  'whole_positive_demand':recipe(totalTentries,totalT),'whole_unique_resources13':recipe(Rentries,Runique),
  'whole_positive_demand_minus_resources':recipe(defentries,deficit),'whole_entire_signed_theta':recipe(whole_entries,whole),
  'whole_principal_demand':affine_serial(demandP),'whole_principal_resources_once':affine_serial(resourceP),'whole_principal_deficit':affine_serial(wholeP),
  'finite_selberg_by_core':sieve_rows,'all_local_primes_le100':primes,
  'raw_Lambda_N':{'proper_power_vertices':properpowers,'proper_power_count':len(properpowers),'whole_raw':recipe(raw_entries,whole_raw),
   'raw_minus_theta':recipe(rawextra_entries,rawextra),'no_mu_n_squared_filter':True,'no_U4_on_raw':True},
  'ERROR_FALSIFIER':[{'claim':'I1=I3=0 implies both resource complements are100-rough on an active demand',
   'status':'REFUTED_NEW_SMALL_FACTOR_ABSENCE_VERTEX' if falsifier_absence else 'NO_COUNTEREXAMPLE_IN_WINDOW','witness':falsifier_absence},
   {'claim':'all four-form local root counts equal4, ignoring collisions and saturation',
    'status':'REFUTED_NEW_EXACT_LOCAL_COLLISIONS' if collisions else 'NO_COUNTEREXAMPLE_IN_WINDOW','counterexamples':collisions},
   {'claim':'apply source C6 budget to the entire demand in this finite window, omitting S and A',
    'status':'REFUTED_NEW_FINITE_PROMOTION_ONLY' if promotion_sign['sign']=='POSITIVE' else 'NO_COUNTEREXAMPLE_IN_WINDOW',
    'rational_upper_for_N_over_8192_logN_loglogN':str(budget_upper),'logN_minus18':s.resolved(u_lower),'log18_minus2':s.resolved(ell_lower),
    'whole_positive_demand_minus_upper_certificate':promotion_sign,'source_C6_onset_and_R_claim_not_refuted':True}],
  'whole_U_a_original_Q_strict_front_k1_preserved':True,'S_bN_actual_indices_preserved':True,
  'unpaid':['source T_A and T_S','global incidence deficit','outside selected support','all remaining whole D_N ledger terms'],
  'no_source_C6_C7_U4_applied_to_finite_N':True,'source_u_minimum':'10^24','imports_sha256':s.IMPORTS,
  'conservation_before':before,'conservation_after':s.conservation.verify(),'strict_rational_only':True,
  'global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'victory':False}

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=s.ROOT);args=parser.parse_args()
 data=run();out=s.conservation.output_directory(args.output_dir)
 (out/'rough.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'q_primes':len(data['q_window_complete']['prime_unit_q']),
  'cores':len(data['core_window_complete']['squarefree_unit_cores']),'candidates':data['candidate_count'],'kernels':data['kernel_count'],
  'active_A_R_S_counts':{cell:sum(len(parts[cell]) for parts in data['partition_active_demands'].values()) for cell in ('A','R','S')},
  'positive_A_R_S_signs':{cell:value['sign_certificate']['sign'] for cell,value in data['whole_positive_parts'].items()},
  'unique_resource_sign':data['whole_unique_resources13']['sign_certificate']['sign'],
  'deficit_sign':data['whole_positive_demand_minus_resources']['sign_certificate']['sign'],
  'entire_signed_sign':data['whole_entire_signed_theta']['sign_certificate']['sign'],'properpowers':data['raw_Lambda_N']['proper_power_count'],
  'falsifier_statuses':[row['status'] for row in data['ERROR_FALSIFIER']],'victory':False}),flush=True)
