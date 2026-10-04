"""Selected NEW Type II character mode, physical caps and two unit conventions."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from math import gcd,prod,isqrt
import argparse,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s
REPORT_SHA='446c2d8fe21c86b05fbaf0e2864e7129da1b964287f31ff4287c0a19251103a9'
ADDENDUM_SHA='51735b4ecd379b8b58066d24b952ff779347af5ae8a32ecd4b4ac303b7636cac'
C,R,D,X,V,BLO,BHI=7,11,77,25000000,10,974026,1136363
HVALUES=(1,3,39);SCOPES=(0,77)
def ceildiv(a,b):return -(-a//b)
def chi(n):
 residue=n%13
 return 0 if residue==0 else (1 if residue in (1,3,4,9,10,12) else -1)
def factor_column(values):return ';'.join('*'.join(str(p)+'^'+str(exponent) for p,exponent in s.factor(value)) for value in values)
def bithex(values):
 output=bytearray((len(values)+7)//8)
 for i,value in enumerate(values):
  if value:output[i//8]|=1<<(i%8)
 return output.hex()
def scalar_certificate(value):
 return {'sign':'POSITIVE' if value>0 else ('NEGATIVE' if value<0 else 'ZERO'),'lower':str(value),'upper':str(value),'rational_exact':True}
def vector_copy(value):return dict(value)
def scaled(vector,scale):return {key:value*scale for key,value in vector.items() if value*scale}
def key(scope,h):return str(scope)+':'+str(h)
def theta_AP_model(scope,h):
 # The inert factor helper has domain n<=N. Factor the bounded components,
 # then form their squarefree union; never pass the larger product to it.
 components=((77 if scope else 1),h,s.N)
 modulus=prod(sorted({p for part in components for p,_ in s.factor(part)}));nmod=D*modulus
 admissible=[b for b in range(modulus) if gcd(b,(77 if scope else 1)*h*s.N)==1 and gcd(s.N-D*b,nmod)==1]
 coefficient=Fraction(len(admissible),s.phi(nmod))
 return {'b_class_modulus':modulus,'candidate_n_modulus':nmod,'admissible_b_residue_count':len(admissible),
  'candidate_totient':s.phi(nmod),'coefficient_exact':str(coefficient),'length_X_principal':str(coefficient*(s.N-D*BLO-(s.N-D*BHI)+1)),
  'admissible_residues_sha256':s.sha256(json.dumps(admissible,separators=(',',':')).encode()).hexdigest(),
  'residue_recipe':'gcd(b,scope*h*N)=1 and gcd(N-77b,77*rad(scope*h*N))=1',
  'finite_AP_reference_only_no_BV':True},coefficient

def run():
 before=s.conservation.verify()
 assert s.sha256((s.ROOT/'agent1_calibrated_typeii.md').read_bytes()).hexdigest()==REPORT_SHA
 assert s.sha256((s.ROOT/'role1'/'unit_mask_addendum.md').read_bytes()).hexdigest()==ADDENDUM_SHA
 assert gcd(s.N,3003)==1 and C*R==D and s.N//4==X and V**8>=s.N>(V-1)**8
 assert BLO==ceildiv(s.N-X,D) and BHI==ceildiv(s.N-X//2,D)-1
 size=BHI-BLO+1;nlo,nhi=s.N-D*BHI,s.N-D*BLO;length=nhi-nlo+1
 assert size==162338 and (nlo,nhi,length)==(12500049,24999998,12499950)
 assert length-D*size==-76 and (s.phi(77),s.phi(231),s.phi(3003))==(60,120,1440)
 own_primes=[p for p in range(2,5001) if s.prime(p)];assert isqrt(X)==5000 and own_primes[-1]<=5000
 ptested=[{'v':v,'factorization':s.factor(v),'prime':s.prime(v),'unit_3003N':gcd(v,3003*s.N)==1} for v in range(V+1,2*V+1)]
 P=[row['v'] for row in ptested if row['prime'] and row['unit_3003N']];assert P==[17,19]
 smin=next(p for p in own_primes if p>R and R*p>s.A);smax=s.A//C;qcap=BHI//smin
 assert (smin,smax,qcap)==(293,451,3878)
 svalues=[p for p in own_primes if p>R and C*p<=s.A<R*p]
 beta=bytearray(size);beta_vertices=[];fibres=[];Aall=0;AP_actual=Fraction(0);AP_reference=Fraction(0);AP_residual=Fraction(0)
 all_prime_beta_pairs=[];beta_m=set();chiN=chi(s.N);assert chiN==1
 hV=sum((Fraction(1,v-1) for v in P),Fraction(0));h0=sum((Fraction(1,v) for v in P),Fraction(0))
 assert 0<=hV-h0<=hV/V and hV-h0==sum((Fraction(1,v*(v-1)) for v in P),Fraction(0))
 for p in svalues:
  L=max(s.A,R*p,R,ceildiv(BLO,p)-1);H=BHI//p
  Lsource=ceildiv(3*s.N,4*D*p)-1;Hsource=ceildiv(7*s.N,8*D*p)-1
  qprime=[q for q in range(L+1,H+1) if s.prime(q)] if L<H else []
  C_all=len(qprime);Aall+=C_all
  unit_q=[q for q in qprime if gcd(C*R*p*q,s.N)==1];removed=[q for q in qprime if q not in unit_q]
  for q in unit_q:
   b=p*q;j=s.N-D*b;m=D*b;i=b-BLO
   assert BLO<=b<=BHI and not beta[i] and C*p<=s.A<R*p<q and q>s.A and p>R
   assert X//2<j<=X and j>s.Q and s.M<=m<=s.N-2 and gcd(m,s.N)==gcd(b,77*39*s.N)==1
   assert s.prime(p) and s.prime(q) and p!=q and m not in beta_m
   beta_m.add(m);beta[i]=1
   beta_vertices.append({'b':b,'s':p,'q':q,'m':m,'j':j,'factorization_b':s.factor(b),'canonical_once':True})
  for q in qprime:all_prime_beta_pairs.append((p,q))
  ap=[]
  for v in P:
   assert gcd(D*p*s.N,13*v)==1 and p!=13 and p>2*V
   a=s.N*pow(D*p,-1,v)%v;classrows=[];local_actual=0;local_residual=Fraction(0)
   characters=[chi(s.N-D*p*t) for t in range(1,13)];assert sum(characters)==-chiN
   for t in range(1,13):
    residue=a+v*((t-a)*pow(v,-1,13)%13);assert 0<=residue<13*v and gcd(residue,13*v)==1
    assert residue%v==a and residue%13==t
    count=sum(q%(13*v)==residue for q in qprime);weight=chi(s.N-D*p*t)
    ref=Fraction(C_all,12*(v-1));error=Fraction(count)-ref
    local_actual+=weight*count;local_residual+=weight*error
    classrows.append({'t_mod13':t,'q_residue_mod13v':residue,'count_prime_exact':count,'character_weight':weight,
     'C_s_all_over_phi13v':str(ref),'exact_count_residual':str(error)})
   reference=Fraction(-chiN*C_all,12*(v-1));assert Fraction(local_actual)==reference+local_residual
   direct=sum(chi(s.N-D*p*q) for q in qprime if (s.N-D*p*q)%v==0)
   assert local_actual==direct
   AP_actual+=local_actual;AP_reference+=reference;AP_residual+=local_residual
   ap.append({'v':v,'q_class_required_mod_v':a,'classes_unit_mod13':classrows,'B1_character_sum':sum(characters),
    'actual_AP_character_sum':local_actual,'principal_exact':str(reference),'signed_residual_exact':str(local_residual)})
  fibres.append({'s':p,'s_factorization':s.factor(p),'L_phys_strict':L,'H_phys_inclusive':H,'L_source_strict':Lsource,'H_source_inclusive':Hsource,
   'physical_caps_cut_source_interval':L!=Lsource or H!=Hsource,'q_primes_all':qprime,'q_unit_retained':unit_q,'q_nonunit_removed':removed,
   'C_s_all':C_all,'AP_by_v':ap})
 A=sum(beta);assert A==len(beta_vertices)==len(beta_m)
 masks={};Js={};densities={}
 for scope in SCOPES:
  for h in HVALUES:
   mask=bytearray(gcd(b,(77 if scope else 1)*h*s.N)==1 for b in range(BLO,BHI+1));k=key(scope,h)
   masks[k]=mask;Js[k]=sum(mask);assert Js[k]>0 and all(not beta[i] or mask[i] for i in range(size))
   densities[k]=Fraction(A,Js[k]) if A else Fraction(0)
 print(json.dumps({'stage':'complete_beta_masks','I_integers':size,'beta':A,'J':Js,'qcap_own':qcap,'v':P}),flush=True)
 ns=[s.N-D*b for b in range(BLO,BHI+1)]
 prime_mask=bytearray(size);rawpp=[];allpp=[];theta_beta={};theta_U={k:{} for k in masks}
 rawII_beta={};rawII_U={k:{} for k in masks};II_beta=0;II_U={k:0 for k in masks};multiplicities={0:0,1:0,2:0}
 candidate_prime_count=0;candidate_theta_count=0;raw_factor_classes={str(t):0 for t in range(13)}
 for i,j in enumerate(ns):
  b=BLO+i;nf=s.factor(j);isprime=nf==((j,1),);unit=gcd(j,s.N)==1
  if isprime:candidate_prime_count+=1
  theta=s.log_vector(j) if isprime and unit else {}
  if theta:prime_mask[i]=1;candidate_theta_count+=1
  raw=s.log_vector(nf[0][0]) if len(nf)==1 and unit else {}
  if len(nf)==1 and nf[0][1]>1:
   row={'b':b,'j':j,'factorization':nf,'unit_N':unit,'raw_Lambda_N_exact':s.serialize(raw)};allpp.append(row)
   if raw:rawpp.append(row);raw_factor_classes[str(b%13)]+=1
  vs=[v for v in P if j%v==0];multiplicities[len(vs)]+=1
  character=chi(j);eta=0
  for v in vs:
   w=j//v;assert j==v*w and X//2<j<=X and w>1
   assert abs(chi(v))<=1 and abs(chi(w))<=1 and chi(v)*chi(w)==character
   eta+=chi(v)*chi(w)
  assert eta==len(vs)*character
  if isprime:assert not vs and eta==0
  if beta[i]:
   s.add(theta_beta,theta);II_beta+=eta;s.add(rawII_beta,raw,eta)
  for k,mask in masks.items():
   if mask[i]:s.add(theta_U[k],theta);II_U[k]+=eta;s.add(rawII_U[k],raw,eta)
 products=[]
 for v in P:
  residue=s.N*pow(D,-1,v)%v;first=BLO+(residue-BLO)%v;last=BHI-(BHI-residue)%v
  count=0 if first>last else (last-first)//v+1
  assert count==sum(j%v==0 for j in ns)
  products.append({'v':v,'xi_chi13':chi(v),'b_residue_mod_v':residue,'b_first':first,'b_last':last,'b_step':v,'count':count,
   'w_at_first':(s.N-D*first)//v,'w_at_last':(s.N-D*last)//v,'w_step_when_b_increases':-D,
   'complete_pair_recipe':'b=first+t*v, 0<=t<count; j=N-77b; w=j/v; kappa=chi13(w)',
   'multiplicity_retained_no_physical_capacity_created':True})
 assert sum(row['count'] for row in products)==multiplicities[1]+2*multiplicities[2]
 both_first=BLO+((s.N*pow(D,-1,17*19))-BLO)%(17*19);both_last=BHI-(BHI-s.N*pow(D,-1,17*19))%(17*19)
 assert (both_last-both_first)//(17*19)+1==multiplicities[2]
 unit_difference=Fraction(II_beta)-AP_actual-Fraction(chiN*(Aall-A),12)*hV
 assert Fraction(II_beta)==Fraction(-chiN*A,12)*hV+AP_residual+unit_difference
 assert AP_reference==Fraction(-chiN*Aall,12)*hV
 weights={'theta':(theta_beta,theta_U),'II':(II_beta,II_U),'II_raw':(rawII_beta,rawII_U)}
 functionals={};prices={};models={};normalization=Fraction(X,A) if A else None
 for weight,(f_beta,f_U) in weights.items():
  is_scalar=weight=='II'
  def subtract(a,b):return a-b if is_scalar else s.difference(a,b)
  def plus(a,b):
   if is_scalar:return a+b
   result=dict(a);s.add(result,b);return result
  def scale(a,b):return a*b if is_scalar else scaled(a,b)
  def summary(value,expression):
   return {'exact_rational':str(value),'sign_certificate':scalar_certificate(value),'expression':expression} if is_scalar else {'exact_expression':expression,'sign_certificate':s.resolved(value)}
  refs={k:scale(f_U[k],densities[k]) for k in masks};z={k:subtract(f_beta,refs[k]) for k in masks}
  rows={}
  for k in masks:
   rows[k]={'reference':summary(refs[k],{'primitive':k,'weight':weight,'scale':str(densities[k])}),
    'z_functional':summary(z[k],{'beta_weight':weight,'reference':k,'reference_scale':str(-densities[k])})}
   if normalization is not None:rows[k]['normalized_x_over_A']=summary(scale(z[k],normalization),{'z_ref':k,'weight':weight,'scale':str(normalization)})
  E={h:subtract(refs[key(77,h)],refs[key(0,h)]) for h in HVALUES}
  L3={scope:subtract(refs[key(scope,3)],refs[key(scope,1)]) for scope in SCOPES}
  L13={scope:subtract(refs[key(scope,39)],refs[key(scope,3)]) for scope in SCOPES}
  for h in HVALUES:assert z[key(0,h)]==plus(z[key(77,h)],E[h])
  for scope in SCOPES:
   assert z[key(scope,1)]==plus(z[key(scope,3)],L3[scope])
   assert z[key(scope,3)]==plus(z[key(scope,39)],L13[scope])
  assert subtract(L3[77],L3[0])==subtract(E[3],E[1])
  assert subtract(L13[77],L13[0])==subtract(E[39],E[3])
  assert z[key(0,1)]==plus(plus(plus(z[key(77,39)],L3[77]),L13[77]),E[1])
  price={'E77':{str(h):summary(E[h],{'reference_plus':key(77,h),'reference_minus':key(0,h),'weight':weight}) for h in HVALUES},
   'L3':{str(scope):summary(L3[scope],{'reference_plus':key(scope,3),'reference_minus':key(scope,1),'weight':weight}) for scope in SCOPES},
   'L13':{str(scope):summary(L13[scope],{'reference_plus':key(scope,39),'reference_minus':key(scope,3),'weight':weight}) for scope in SCOPES},
   'U1_U2_and_full_telescope_exact':True,'prices_have_this_weight_only':weight}
  functionals[weight]={'beta_primitive':summary(f_beta,{'primitive':'beta','weight':weight}),
   'unscaled_mask_primitives':{k:summary(f_U[k],{'primitive':k,'weight':weight}) for k in masks},'by_mask':rows}
  prices[weight]=price
  if weight=='II':
   for scope in SCOPES:
    principal3=Fraction(-chiN*A,12)*hV;principal39=Fraction(-chiN*A,12)*(hV-h0)
    reference39principal=Fraction(-chiN*A,12)*h0
    front3=refs[key(scope,3)];front39=refs[key(scope,39)]-reference39principal
    error3=z[key(scope,3)]-principal3;error39=z[key(scope,39)]-principal39
    assert error3==AP_residual+unit_difference-front3 and error39==AP_residual+unit_difference-front39
    models[str(scope)]={'T3':str(z[key(scope,3)]),'T39':str(z[key(scope,39)]),
     'principal_T3':str(principal3),'principal_T39':str(principal39),'error_T3_exact':str(error3),'error_T39_exact':str(error39),
     'reference3_front_exact':str(front3),'reference39_principal':str(reference39principal),'reference39_front_exact':str(front39),
     'B2_B6_or_U4_exact_decomposition':True,'BV_bound_not_applied':True}
 theta_models={}
 for scope in SCOPES:
  for h in HVALUES:
   k=key(scope,h);model,coefficient=theta_AP_model(scope,h);main=coefficient*length
   residual=s.difference(theta_U[k],{():main});model['actual_theta_minus_AP_main_certificate']=s.resolved(residual)
   model['actual_theta_primitive_ref']=k;model['residual_exact_recipe']={'theta_primitive':k,'constant':str(-main)}
   theta_models[k]=model
 classrows={}
 for modulus in (3,13):
  rows=[]
  for residue in range(modulus):
   indexes=[i for i in range(size) if (BLO+i)%modulus==residue]
   rows.append({'b_residue':residue,'all_b_count':len(indexes),'beta_count':sum(beta[i] for i in indexes),
    'theta_prime_count':sum(prime_mask[i] for i in indexes),
    'unit_mask_counts':{k:sum(mask[i] for i in indexes) for k,mask in masks.items()},
    'raw_proper_power_b':[row['b'] for row in rawpp if row['b']%modulus==residue]})
  classrows[str(modulus)]=rows
 assert all(sum(row['unit_mask_counts'][k] for row in classrows['13'])==Js[k] for k in masks)
 assert (s.N*pow(D,-1,13))%13==4
 return {'status':'PASS_NEW_REAL_TYPEII_CHARACTER_MODE_TWO_UNIT_CONVENTIONS_ONLY',
  'contract_FINAL1_sha256':REPORT_SHA,'unit_mask_addendum_sha256':ADDENDUM_SHA,'N':s.N,'c':C,'r':R,'d':D,'x':X,'V':V,
  'alpha':s.ALPHA,'a':s.A,'Q':s.Q,'M':s.M,
  'progression_complete':{'b_low':BLO,'b_high':BHI,'integer_count':size,'n_low':nlo,'n_high':nhi,'length_X':length,
   'X_minus77_integer_count':length-D*size,'phi77':60,'phi231':120,'phi3003':1440,
   'b_and_j_row_recipe':'row i: b=974026+i, j=N-77b, 0<=i<162338',
   'b_factorizations_complete_column':factor_column(range(BLO,BHI+1)),
   'j_factorizations_complete_column':factor_column(ns),'factor_column_grammar':'semicolon-separated rows; factors p^exponent separated by *',
   'theta_prime_mask_hex':bithex(prime_mask),'bit_order':'bit i is low bit i%8 of byte i//8; same row indexing',
   'theta_candidate_count':candidate_theta_count,'candidate_prime_count':candidate_prime_count},
  'own_completeness':{'s_first':smin,'s_cap':smax,'q_cap':qcap,'factor_j_trial_primes_limit':5000,'factor_j_own_primes':own_primes,
   's_all_primes':svalues,'old_qcap9889_not_used':True,'all_b_primality_and_raw_examined':True},
  'beta_structural':{'A':A,'mask_hex':bithex(beta),'canonical_vertices':beta_vertices,'no_candidate_prime_filter':True,
   'unique_m_count':len(beta_m),'physical_caps_and_units_verified':True},
  'unit_conventions':{k:{'scope':int(k.split(':')[0]),'h':int(k.split(':')[1]),'J':Js[k],'rho_exact':str(densities[k]),
   'mask_hex':bithex(masks[k]),'gcd_modulus':(77 if k.startswith('77:') else 1)*int(k.split(':')[1])*s.N} for k in masks},
  'class_counts':classrows,'b0_removed_by_U39_distinct_from_b4_candidate13_exclusion':True,
  'character13':{'values':[chi(t) for t in range(13)],'chiN':chiN,'coefficients_abs_le1':True,'multiplicativity_verified_on_all_products':True},
  'v_complete':{'all_integers_V_lt_v_le2V':ptested,'eligible':P,'products_by_v_complete_recipes':products,
   'multiplicity_counts':{str(k):value for k,value in multiplicities.items()},
   'double_products_323_b_recipe':{'first':both_first,'last':both_last,'step':323,'count':multiplicities[2]},
   'candidate_primes_have_zero_product_multiplicity':True,'no_physical_resource_multiplicity_created':True},
  'AP_physical_fibres':fibres,'AP_decomposition':{'A_all_prime_before_unit_removal':Aall,'A_unit_beta':A,
   'actual_character_sum_before_unit_removal':str(AP_actual),'principal_exact':str(AP_reference),'residual_AP_exact':str(AP_residual),
   'unit_residual_exact':str(unit_difference),'B2_actual_beta_character_sum':str(II_beta),'hV':str(hV),'h0':str(h0),
   'hV_minus_h0':str(hV-h0),'hV_minus_h0_le_hV_overV_verified':True,'BV_not_applied':True},
  'functionals_exact':functionals,'prices_by_weight':prices,'typeII_source_decompositions_with_finite_errors':models,
  'theta_AP_references_and_exact_errors':theta_models,'normalization_x_over_A':str(normalization) if normalization is not None else None,
  'raw_Lambda_N':{'all_proper_power_factorizations':allpp,'unit_proper_power_vertices':rawpp,'unit_proper_power_count':len(rawpp),
   'no_mu_n_squared_filter':True,'prime_contribution_to_TypeII_raw_zero_verified':True,'II_raw_prices_retained':True},
  'exact_expression_evaluation':{'theta':'sum log(j) over theta_prime_mask intersect beta/mask hex',
   'II':'sum over complete v/w recipes chi13(v)*chi13(w) times beta or unit mask',
   'II_raw':'same complete products weighted raw Lambda_N from unit proper power catalog; candidate primes contribute zero'},
  'new_mode_only_no_complete_TypeII_estimate':True,'Gamma39_unestimated':True,'no_BV_onset_certified':True,
  'D_W_errors_literal_uncomputed':'all physical image kernels and other vertices remain outside this TypeII mode; no W bound transferred',
  'S_bN_and_whole_D_N_not_replaced':True,'imports_sha256':s.IMPORTS,'conservation_before':before,'conservation_after':s.conservation.verify(),
  'strict_rational_only':True,'global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'victory':False}

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=s.ROOT);args=parser.parse_args()
 data=run();out=s.conservation.output_directory(args.output_dir)
 (out/'typeii.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'b_count':data['progression_complete']['integer_count'],'beta':data['beta_structural']['A'],
  'J':{k:v['J'] for k,v in data['unit_conventions'].items()},'theta_candidates':data['progression_complete']['theta_candidate_count'],
  'TypeII_by_convention':{k:v['z_functional']['exact_rational'] for k,v in data['functionals_exact']['II']['by_mask'].items()},
  'theta_L13_signs':{k:v['sign_certificate']['sign'] for k,v in data['prices_by_weight']['theta']['L13'].items()},
  'properpowers':data['raw_Lambda_N']['unit_proper_power_count'],'victory':False}),flush=True)
