"""NEW full d77 candidate progression: uniform Type I drift and local correction."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from math import gcd,isqrt
import argparse,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s
REPORT_SHA='f60827e9e72e73cde93512448bd6acc289807d43180b844040326456a5e2d754'

def run():
 before=s.conservation.verify()
 assert s.sha256((s.ROOT/'agent1_bilinear_covariance.md').read_bytes()).hexdigest()==REPORT_SHA
 c,r,d,x=7,11,77,20000000;low,high=1038962,1168831;length=high-low+1
 assert c*r==d and s.prime(c) and s.prime(r) and gcd(231,s.N)==1
 assert low==(s.N-x+d-1)//d and high==((s.N-x//2)+d-1)//d-1
 assert length==129870 and length%30==0
 nlo=s.N-d*high;nhi=s.N-d*low;X=nhi-nlo+1
 assert (nlo,nhi,X)==(10000013,19999926,9999914) and x//2<nlo<=nhi<=x
 assert d*low>=s.M and nlo>s.Q and X-d*length==-76
 possible_s_min=s.A//r+1;small_s=[p for p in s.historical.parity.PRIMES if c<r<p and c*p<=s.A<r*p]
 assert possible_s_min==288 and min(small_s)==293 and max(small_s)<=451
 qcap=high//min(small_s);assert qcap==3989
 enumeration_primes=[p for p in s.historical.parity.PRIMES if p<=qcap]
 sieve_primes=[p for p in s.historical.parity.PRIMES if p<=isqrt(nhi)]
 assert isqrt(x)==4472 and isqrt(nhi)<=4472 and nlo>4472
 primeflags=bytearray(b'\1')*length
 for ell in sieve_primes:
  if d%ell==0:assert s.N%ell!=0;continue
  residue=(s.N*pow(d,-1,ell))%ell;first=low+(residue-low)%ell
  if first<=high:primeflags[first-low::ell]=b'\0'*((high-first)//ell+1)
 unit=bytearray(gcd(b,s.N)==1 for b in range(low,high+1))
 J=sum(unit);Jt=[sum(unit[b-low] for b in range(low,high+1) if b%3==t) for t in range(3)]
 assert J==51948 and Jt==[17316]*3
 beta={};At=[0,0,0]
 for sp in small_s:
  for q in enumeration_primes:
   b=sp*q
   if b<low:continue
   if b>high:break
   if not(r*sp<q and q>s.A and gcd(c*r*sp*q,s.N)==1):continue
   assert b not in beta and unit[b-low] and b%3!=0
   beta[b]={'b':b,'s':sp,'q':q,'m':d*b,'j':s.N-d*b,'class_b_mod3':b%3,'theta_prime':bool(primeflags[b-low]),
    'structural_without_candidate_prime_filter':True};At[b%3]+=1
 A=len(beta);assert At[0]==0 and A==sum(At)
 rho=Fraction(A,J);Jstar=Jt[1]+Jt[2];rhostar=Fraction(A,Jstar)
 assert rhostar==Fraction(3,2)*rho
 f=(s.N*pow(d,-1,3))%3;g=3-f;assert (f,g)==(2,1)
 uniform_drift=Fraction(At[f])-rho*Jt[f]
 corrected_drift=Fraction(At[f])-rhostar*Jt[f]
 assert uniform_drift==corrected_drift+(rhostar-rho)*Jt[f]
 T=[{}, {}, {}];theta_beta={};prime_counts=[0,0,0]
 for offset,flag in enumerate(primeflags):
  if flag and unit[offset]:
   b=low+offset;j=s.N-d*b;t=b%3
   T[t][(j,)]=Fraction(1);prime_counts[t]+=1
   if b in beta:theta_beta[(j,)]=Fraction(1)
 assert T[f]=={} and prime_counts[f]==0
 Tall=s.add_many(T);Tstar=s.add_many([T[1],T[2]])
 Gamma=dict(theta_beta);s.add(Gamma,Tall,-rho)
 Gammastar=dict(theta_beta);s.add(Gammastar,Tstar,-rhostar)
 local3={};s.add(local3,T[g],rhostar);s.add(local3,s.add_many([T[0],T[g]]),-rho)
 assert Gamma==s.add_many([Gammastar,local3])
 norm=Fraction(A)*(1-rho)**2+Fraction(J-A)*rho*rho
 normstar=Fraction(A)*(1-rhostar)**2+Fraction(Jstar-A)*rhostar*rhostar
 assert norm==A*(1-rho) and normstar==A*(1-rhostar)
 pp=[];raw_extra=[{}, {}, {}];raw_beta_extra={}
 for p in sieve_primes:
  value=p*p;exponent=2
  while value<=nhi:
   if value>=nlo and (s.N-value)%d==0:
    b=(s.N-value)//d
    if low<=b<=high and gcd(value,s.N)==1:
     assert unit[b-low] and not primeflags[b-low]
     pp.append({'b':b,'j':value,'base_prime':p,'exponent':exponent,'class_b_mod3':b%3,'beta':b in beta,'raw_Lambda_N':s.serialize(s.log_vector(p))})
     s.add(raw_extra[b%3],s.log_vector(p))
     if b in beta:s.add(raw_beta_extra,s.log_vector(p))
   value*=p;exponent+=1
 rawT=[s.add_many([T[t],raw_extra[t]]) for t in range(3)];rawbeta=s.add_many([theta_beta,raw_beta_extra])
 rawGamma=dict(rawbeta);s.add(rawGamma,s.add_many(rawT),-rho)
 rawGstar=dict(rawbeta);s.add(rawGstar,s.add_many([rawT[1],rawT[2]]),-rhostar)
 rawL3={};s.add(rawL3,s.add_many([rawT[1],rawT[2]]),rhostar);s.add(rawL3,s.add_many(rawT),-rho)
 assert rawGamma==s.add_many([rawGstar,rawL3])
 assert s.phi(d)==60 and s.phi(3*d)==120
 APprincipal=Fraction(X,s.phi(3*d));local_coefficient=rhostar-2*rho
 APcorrection=local_coefficient*APprincipal;uniform_AP=rho*Fraction(X,s.phi(d))
 assert APcorrection==-uniform_AP/4
 exception=[p for p,_ in s.factor(s.N) if nlo<=p<=nhi];assert exception==[]
 drift_sign='POSITIVE' if uniform_drift>0 else 'NEGATIVE' if uniform_drift<0 else 'ZERO'
 corrected_sign='POSITIVE' if corrected_drift>0 else 'NEGATIVE' if corrected_drift<0 else 'ZERO'
 certs={name:s.resolved(v) for name,v in [('Gamma',Gamma),('Gamma_star',Gammastar),('L3',local3),('theta_beta',theta_beta),('raw_Gamma',rawGamma),('raw_Gamma_star',rawGstar),('raw_L3',rawL3)]}
 normalized_uniform=Fraction(x,A)*uniform_drift if A else Fraction(0)
 return {'status':'PASS_NEW_FULL_D77_TYPEI3_DRIFT_AND_LOCAL_CORRECTION_ONLY','contract_FINAL1_sha256':REPORT_SHA,
  'N':s.N,'alpha':s.ALPHA,'a':s.A,'Q':s.Q,'M':s.M,'c':c,'r':r,'d':d,'x':x,
  'complete_candidate_window':{'j_lower_exclusive':x//2,'j_upper_inclusive':x,'b_low':low,'b_high':high,'integer_count':length,
   'n_lo':nlo,'n_hi':nhi,'X_exact':X,'X_minus_d_times_integer_count':X-d*length,'bulk_all':True,'j_above_Q_all':True,'all_integer_b_examined':True},
  'complete_prime_bounds':{'s_integer_minimum':possible_s_min,'first_admissible_prime_s':min(small_s),'s_upper':s.A//c,'q_upper':qcap,
   's_and_q_enumeration_prime_limit':qcap,'candidate_factor_prime_limit':4472,'own_bounds_not_inherited_from_d141':True,
   'integer_sieve_complete_to_isqrt_n_hi':True,'n_greater_than_all_sieve_primes':True},
  'unit_counts':{'J':J,'J_classes_mod3':Jt,'J_star':Jstar,'exact_blocks_of30':length//30},
  'structural_beta':list(beta.values()),'A_beta':A,'A_classes_mod3':At,'rho':str(rho),'rho_star':str(rhostar),'f_candidate_divisible3':f,'g_other_nonzero_class':g,
  'TypeI3_exact':{'uniform_drift_Af_minus_rho_Jf':str(uniform_drift),'uniform_drift_sign':drift_sign,
   'corrected_drift_Af_minus_rho_star_Jf':str(corrected_drift),'corrected_drift_sign':corrected_sign,
   'difference_exact':str((rhostar-rho)*Jt[f]),'normalized_uniform_x_over_A_drift':str(normalized_uniform),
   'source_x_over8_not_applied_at_finite_N':True},
  'theta_prime_counts_classes':prime_counts,'theta_sums_classes':{str(t):s.serialize(T[t]) for t in range(3)},
  'theta_beta':s.serialize(theta_beta),'theta_f_exact_zero_because_j_divisible3_above3':True,
  'Gamma_uniform':s.serialize(Gamma),'Gamma_corrected_star':s.serialize(Gammastar),'L3_reference_difference':s.serialize(local3),
  'Gamma_equals_Gamma_star_plus_L3_exact':True,'sign_certificates':certs,
  'centered_norms_exact':{'uniform_A_one_minus_rho':str(norm),'corrected_A_one_minus_rho_star':str(normstar)},
  'raw_Lambda_N':{'proper_power_records_complete':pp,'proper_power_count_classes':[sum(v['class_b_mod3']==t for v in pp) for t in range(3)],
   'proper_power_extra_classes':{str(t):s.serialize(raw_extra[t]) for t in range(3)},'proper_power_extra_beta':s.serialize(raw_beta_extra),
   'raw_beta':s.serialize(rawbeta),'raw_Gamma_uniform':s.serialize(rawGamma),'raw_Gamma_corrected_star':s.serialize(rawGstar),
   'raw_reference_difference':s.serialize(rawL3),'raw_decomposition_exact_even_if_raw_f_nonzero':True,'no_mu_n_squared_filter':True},
  'AP_front_and_principal':{'phi77':60,'phi231':120,'X_over_phi231':str(APprincipal),'uniform_rho_X_over_phi77':str(uniform_AP),
   'L3_principal_coefficient_rho_star_minus_2rho':str(local_coefficient),'L3_principal':str(APcorrection),
   'L3_principal_exact_minus_one_quarter_uniform':True,'E_divN_exceptions':exception,
   'two_AP_class_endpoints_and_errors_literal':'T_t=X/phi231+E_t-E_divN_t for t=0,g',
   'source_AP_bounds_and_onset_not_applied_to_finite_bank':True},
  'ERROR_FALSIFIER':[{'claim':'the uniform unit reference is exactly centered for Type I at divisor3 of the candidate',
   'status':'REFUTED_NEW_TYPEI3_NONZERO_DRIFT' if uniform_drift else 'NO_COUNTEREXAMPLE_IN_WINDOW','actual_drift':str(uniform_drift),'actual_sign':drift_sign}],
  'D_W_kernels_recomputed':False,'physical_brackets_not_tested_in_this_bank':True,
  'unpaid':['Gamma_star and full TypeII','weighted aggregate Gamma and true parent comparison','all W errors and whole ledger'],
  'imports_sha256':s.IMPORTS,'conservation_before':before,'conservation_after':s.conservation.verify(),
  'strict_rational_only':True,'finite_N_outside_source':True,'source_u_minimum':'10^24','global_D_N':False,'asymptotic':False,
  'payments':False,'Lean_called':False,'victory':False}

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=s.ROOT)
 args=parser.parse_args();data=run();out=s.conservation.output_directory(args.output_dir)
 (out/'typei.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'A':data['A_beta'],'A_classes':data['A_classes_mod3'],'J':data['unit_counts']['J'],
  'drifts':data['TypeI3_exact'],'theta_classes':data['theta_prime_counts_classes'],
  'Gamma_signs':{k:v['sign'] for k,v in data['sign_certificates'].items()},'proper_powers':len(data['raw_Lambda_N']['proper_power_records_complete']),'victory':False}))
