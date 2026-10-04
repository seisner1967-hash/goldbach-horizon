"""New complete d141 first-incidence contrast, with explicitly sampled kernels."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from math import gcd,isqrt
import argparse,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s

def historical_numeric_integers():
 out=set()
 def walk(v):
  if isinstance(v,dict):
   for w in v.values():walk(w)
  elif isinstance(v,list):
   for w in v:walk(w)
  elif isinstance(v,int) and not isinstance(v,bool) and v>=s.M:out.add(v)
  elif isinstance(v,str) and v.isdigit() and int(v)>=s.M:out.add(int(v))
 for relative,digest in s.PROTECTED.items():
  if relative.endswith('.json'):
   p=s.BASE/relative;assert s.sha256(p.read_bytes()).hexdigest()==digest
   walk(json.loads(p.read_text(encoding='utf-8')))
 return out

def run():
 before=s.conservation.verify();c,r,d=3,47,141
 assert s.prime(c) and s.prime(r) and d==c*r and gcd(d,s.N)==1
 low=(s.M+d-1)//d;B=(s.N-s.Q-1)//d;length=B-low+1
 assert (low,B,length)==(7093,702127,695035)
 min_n=s.N-d*B;max_n=s.N-d*low
 assert s.M<=d*low<=d*B<=s.N-2 and min_n>s.Q and min_n>isqrt(s.N)
 primes=s.historical.parity.PRIMES
 prime_flags=bytearray(b'\1')*length
 for ell in primes:
  if d%ell==0:
   assert s.N%ell!=0;continue
  residue=(s.N*pow(d,-1,ell))%ell
  first=low+(residue-low)%ell
  if first<=B:prime_flags[first-low::ell]=b'\0'*((B-first)//ell+1)
 unit_flags=bytearray(gcd(b,s.N)==1 for b in range(low,B+1));J=sum(unit_flags)
 assert J==278014
 beta={}
 for sp in primes:
  if not (c<r<sp and c*r<=s.A and c*sp<=s.A<r*sp):continue
  for q in primes:
   if not (r*sp<q and q>s.A):continue
   b=sp*q
   if b<low:continue
   if b>B:break
   if gcd(c*r*sp*q,s.N)!=1:continue
   assert unit_flags[b-low] and b not in beta
   assert s.prime(sp) and s.prime(q)
   beta[b]={'b':b,'s':sp,'q':q,'m':d*b,'n':s.N-d*b,'theta_prime':bool(prime_flags[b-low]),'structural_without_first_prime_filter':True}
 Mbeta=len(beta);rho=Fraction(Mbeta,J);rho_integer=Fraction(Mbeta,length)
 assert Mbeta>0 and rho!=rho_integer
 theta_U={};theta_beta={};prime_count=0
 for index,flag in enumerate(prime_flags):
  if flag and unit_flags[index]:
   b=low+index;n=s.N-d*b;assert gcd(n,s.N)==1
   theta_U[(n,)]=Fraction(1);prime_count+=1
   if b in beta:theta_beta[(n,)]=Fraction(1)
 Gamma=dict(theta_beta);s.add(Gamma,theta_U,-rho)
 projection=dict(theta_U);projection={k:rho*v for k,v in projection.items()};s.add(projection,Gamma)
 assert projection==theta_beta
 centered_sum=Fraction(Mbeta)-rho*J;assert centered_sum==0
 centered_theta_mean={k:v/J for k,v in theta_U.items()}
 covariance=dict(Gamma);s.add(covariance,s.multiply(centered_theta_mean,{():centered_sum}),-1);assert covariance==Gamma
 norm=Fraction(Mbeta)*(1-rho)**2+Fraction(J-Mbeta)*rho**2
 assert norm==Fraction(Mbeta)*(1-rho)
 gamma_cert=s.resolved(Gamma);assert gamma_cert['sign'] in ('POSITIVE','NEGATIVE')
 naive_gamma=dict(theta_beta);s.add(naive_gamma,theta_U,-rho_integer)
 bias=s.difference(naive_gamma,Gamma);expected_bias={k:(rho-rho_integer)*v for k,v in theta_U.items()}
 assert bias==expected_bias
 proper_powers=[];extra_raw_U={};extra_raw_beta={}
 for p in primes:
  value=p*p;exponent=2
  while value<=max_n:
   if value>=min_n and (s.N-value)%d==0:
    b=(s.N-value)//d
    if low<=b<=B and gcd(value,s.N)==1:
     assert unit_flags[b-low] and not prime_flags[b-low]
     record={'b':b,'n':value,'base_prime':p,'exponent':exponent,'beta':b in beta,'raw_Lambda_N':s.serialize(s.log_vector(p))}
     proper_powers.append(record);s.add(extra_raw_U,s.log_vector(p))
     if b in beta:s.add(extra_raw_beta,s.log_vector(p))
   value*=p;exponent+=1
 raw_beta=dict(theta_beta);s.add(raw_beta,extra_raw_beta)
 assert s.difference(raw_beta,theta_beta)==extra_raw_beta
 loga=s.log_vector(s.A);loga_minus8=dict(loga);s.add(loga_minus8,{():Fraction(-8)})
 domain_cert=s.resolved(loga_minus8);assert domain_cert['sign']=='POSITIVE'
 budget={():Fraction(64*B)};s.add(budget,loga,-Mbeta)
 bound_cert=s.resolved(budget);assert bound_cert['sign']=='POSITIVE'
 old_integers=historical_numeric_integers();sample=[];skipped=[]
 for b,v in sorted(beta.items()):
  if not (v['theta_prime'] and v['q']>=4001):continue
  if v['m'] in old_integers:skipped.append(v['m']);continue
  assert s.prime(v['n'])
  profile,Breal,C,W=s.source_profile(v['m'])
  assert profile['mu_m']==1 and profile['short_prefix']==s.serialize(s.log_vector(3))
  assert C==s.difference(W,s.log_vector(3))
  capacity={k:-x for k,x in Breal.items()}
  sample.append({'structure':v,'profile':profile,'actual_capacity':s.serialize(capacity),'actual_capacity_sign_certificate':s.resolved(capacity),'sample_only_no_extrapolation':True})
  if len(sample)==5:break
 assert len(sample)==5
 matched_prime_images=[v for v in beta.values() if v['theta_prime']]
 assert len(matched_prime_images)==len(theta_beta)
 return {'status':'PASS_NEW_COMPLETE_141_MASK_PROJECTION_AND_COVARIANCE_ONLY','N':s.N,'alpha':s.ALPHA,'a':s.A,'Q':s.Q,'M':s.M,'c':c,'r':r,'d':d,'interval_complete':{'low':low,'high':B,'integer_count':length,'unit_count_J':J,'all_integer_b_examined':True,'unit_gcd_b_N_equals_unit_gcd_n_N':True,'min_n':min_n,'max_n':max_n},'exact_prime_sieve':{'primes_through_isqrt_N':len(primes),'largest_sieving_prime':primes[-1],'no_floating_point':True,'n_greater_than_all_sieving_primes':True,'unit_prime_first_axes':prime_count},'structural_beta_without_n_prime_filter':list(beta.values()),'M_beta':Mbeta,'rho_unit':str(rho),'rho_integer_interval':str(rho_integer),'rho_unit_bias':str(rho-rho_integer),'all_beta_unit':True,'theta_unit_sum':s.serialize(theta_U),'theta_beta_sum':s.serialize(theta_beta),'Gamma_centered':s.serialize(Gamma),'Gamma_sign_certificate':gamma_cert,'projection_identity_exact':True,'centered_beta_sum':str(centered_sum),'centered_theta_covariance_equals_Gamma':True,'centered_beta_norm_sq_direct':str(norm),'centered_beta_norm_sq_M_one_minus_rho':str(Fraction(Mbeta)*(1-rho)),'unit_bias_exact_vector_recipe':{'Gamma_naive_minus_Gamma':'(rho_unit-rho_integer_interval)*theta_unit_sum','coefficient':str(rho-rho_integer)},'raw_Lambda_N':{'theta_unit_vector_ref':'theta_unit_sum','proper_powers_extra_unit':s.serialize(extra_raw_U),'proper_powers_extra_beta':s.serialize(extra_raw_beta),'proper_power_records_complete':proper_powers,'raw_beta':s.serialize(raw_beta),'raw_minus_theta_beta_exact':s.serialize(extra_raw_beta),'proper_powers_retained_separately':True,'mu_n_sq_filter_used':False},'written_cardinality_bound_finite_check':{'B':B,'M_beta_log_a_le_64B':True,'log_a_at_least_8_certificate':domain_cert,'64B_minus_Mbeta_log_a_certificate':bound_cert,'asymptotic_bound_not_certified_here':True,'finite_bound_is_vacuous':64*B>J*8},'physical_raccord_sample':{'selection':'first five by b among beta with first n prime, q>=4001 and m absent from protected historical JSON numeric values','sample_count':5,'skipped_old_numeric_m_values':skipped,'historical_values_removed_only_from_sample_not_from_complete_beta_or_Gamma':True,'vertices':sample,'unsampled_prime_image_m':[v['m'] for v in matched_prime_images if v['m'] not in {x['profile']['m'] for x in sample}],'unsampled_W_errors_literal_uncomputed_and_unpaid':True},'principal_weight_symbolic':{'kappa':'log(3)+S(N)','masked_principal':'kappa*theta_beta_sum','density_principal':'kappa*rho_unit*theta_unit_sum','centered_principal':'kappa*Gamma_centered','S_cN_bilateral_not_substituted':True,'Gamma_is_first_incidence_covariance_not_total_residue':True},'ERROR_FALSIFIER':[{'claim':'replace the structural beta mask exactly by its unit density because d141 is small','status':'REFUTED_NEW_COMPLETE_GAMMA_NONZERO','Gamma_sign':gamma_cert['sign']}],'imports_sha256':s.IMPORTS,'conservation_before':before,'conservation_after':s.conservation.verify(),'strict_rational_only':True,'finite_N_outside_source':True,'source_u_minimum':'10^24','global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'victory':False}
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=s.ROOT)
 args=parser.parse_args();data=run();directory=s.conservation.output_directory(args.output_dir)
 (directory/'incidence.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'I':data['interval_complete']['integer_count'],'J':data['interval_complete']['unit_count_J'],'M_beta':data['M_beta'],'beta_prime_axes':len(data['theta_beta_sum']),'Gamma_sign':data['Gamma_sign_certificate']['sign'],'proper_powers':len(data['raw_Lambda_N']['proper_power_records_complete']),'sample':5,'victory':False}))
