"""Read-only supplement of frozen incidence15: missing L4 moment and AP fronts."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from math import gcd
import argparse,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s

INCIDENCE_SHA='8c3506c4f51cca70d03b16ed5c82a13d40a01966e36770e24a51aea94e96aead'
PRODUCER_SHA='edb58961dca27429b934f74899928fc38aabdb45f16ebe679fea5c19e3e880f4'

def bounds_linear(vector,terms=6,bits=96):
 scale=1<<bits;lo=hi=Fraction(0)
 for text,cstr in vector.items():
  key=tuple(map(int,text.split(',')));assert len(key)==1
  a,b=s.historical.arithmetic.log_grid(key[0],terms,bits);c=Fraction(cstr)
  lo+=c*Fraction(a if c>0 else b,scale);hi+=c*Fraction(b if c>0 else a,scale)
 assert lo<=hi;return lo,hi

def run():
 before=s.conservation.verify();gate=s.ROOT/'incidence.json';producer=s.ROOT/'incidence_checks.py'
 assert s.sha256(gate.read_bytes()).hexdigest()==INCIDENCE_SHA
 assert s.sha256(producer.read_bytes()).hexdigest()==PRODUCER_SHA
 source=json.loads(gate.read_text(encoding='utf-8'))
 assert source['status']=='PASS_NEW_COMPLETE_141_MASK_PROJECTION_AND_COVARIANCE_ONLY'
 J=source['interval_complete']['unit_count_J'];Mbeta=source['M_beta'];rho=Fraction(source['rho_unit'])
 norm=Fraction(source['centered_beta_norm_sq_direct']);assert norm==Mbeta*(1-rho)
 T=source['theta_unit_sum'];Gamma=source['Gamma_centered'];theta_beta=source['theta_beta_sum']
 assert all(Fraction(x)==1 for x in T.values()) and set(theta_beta)<=set(T)
 # The exact quadratic forms remain factorized, avoiding a quadratic-size expansion of T^2.
 theta_sq={n+','+n:'1' for n in T}
 Tlo,Thi=bounds_linear(T);Glo,Ghi=bounds_linear(Gamma)
 assert Glo<=Ghi<0 and 0<Tlo<=Thi
 scale=1<<96;sqlo=sqhi=Fraction(0)
 for n in T:
  low,high=s.historical.arithmetic.log_grid(int(n),6,96)
  sqlo+=Fraction(low*low,scale*scale);sqhi+=Fraction(high*high,scale*scale)
 variance_lo=sqlo-Thi*Thi/J;variance_hi=sqhi-Tlo*Tlo/J
 assert 0<variance_lo<=variance_hi
 # Gamma is negative; its square has reversed endpoints.
 gamma_sq_lo=Ghi*Ghi;gamma_sq_hi=Glo*Glo
 gap_lo=norm*variance_lo-gamma_sq_hi;gap_hi=norm*variance_hi-gamma_sq_lo
 assert 0<gap_lo<=gap_hi
 d=source['d'];I=source['interval_complete'];nlo=I['min_n'];nhi=I['max_n'];X=nhi-nlo+1
 assert gcd(d,s.N)==1 and d==141 and s.phi(d)==92
 assert X==d*(I['integer_count']-1)+1
 assert (nlo,nhi)==(1000093,98999887)
 assert all(int(n)%d==s.N%d and nlo<=int(n)<=nhi and gcd(int(n),s.N)==1 for n in T)
 exceptional=[p for p,_ in s.factor(s.N) if nlo<=p<=nhi and p%d==s.N%d]
 assert exceptional==[]
 exact_AP_reference=Fraction(X,s.phi(d));wrong_reference=Fraction(d*I['integer_count'],s.phi(d))
 assert exact_AP_reference-wrong_reference==Fraction(1-d,s.phi(d))
 # This is a literal finite discrepancy, with no BV estimate applied.
 APlo=Tlo-exact_AP_reference;APhi=Thi-exact_AP_reference
 assert APlo<=APhi
 ap_sign='POSITIVE' if APlo>0 else 'NEGATIVE' if APhi<0 else 'UNRESOLVED'
 assert ap_sign!='UNRESOLVED'
 return {'status':'PASS_NEW_READ_ONLY_INCIDENCE_L4_AND_EXACT_AP_FRONT_SUPPLEMENT',
  'reason_new_check':'Frozen incidence gate verified covariance, norm and projection but did not serialize the theta second moment, Cauchy gap or exact AP interval front.',
  'input_gate_sha256':INCIDENCE_SHA,'input_producer_sha256':PRODUCER_SHA,'input_gate_unchanged':True,
  'theta_second_moment_exact_vector':theta_sq,'theta_unit_sum_ref':'incidence.json/theta_unit_sum',
  'Gamma_ref':'incidence.json/Gamma_centered','theta_variance_exact_expression':'theta_second_moment_exact_vector - theta_unit_sum^2/J',
  'Gamma_centered_covariance_checked_in_input':source['centered_theta_covariance_equals_Gamma'],
  'J':J,'M_beta':Mbeta,'rho':str(rho),'centered_beta_norm_sq':str(norm),
  'log_interval_terms':6,'log_interval_bits':96,'strict_rational_intervals':{
   'T':[str(Tlo),str(Thi)],'Gamma':[str(Glo),str(Ghi)],'theta_second_moment':[str(sqlo),str(sqhi)],
   'theta_variance':[str(variance_lo),str(variance_hi)],'Gamma_squared':[str(gamma_sq_lo),str(gamma_sq_hi)],
   'norm_squared_times_variance_minus_Gamma_squared':[str(gap_lo),str(gap_hi)]},
  'Cauchy_L4':{'exact_factorized_gap':'M_beta*(1-rho)*(sum_theta_squared - T^2/J)-Gamma^2',
   'strict_positive_gap_certified':True,'no_expansion_or_kernel_recomputation':True,'no_payment_for_Gamma':True},
  'AP_front':{'d':d,'phi_d':s.phi(d),'n_lo':nlo,'n_hi':nhi,'X_exact':X,'I_integer_count':I['integer_count'],
   'X_equals_d_times_I_minus_d_plus_one':True,'principal_X_over_phi_d':str(exact_AP_reference),
   'incorrect_d_times_I_over_phi_d':str(wrong_reference),'front_difference_exact':str(Fraction(1-d,s.phi(d))),
   'E_divN_exceptional_prime_list':exceptional,'T_exact_reconstruction':'Psi_theta(n_hi;d,N)-Psi_theta(n_lo-1;d,N)-E_divN',
   'literal_interval_AP_error_bounds':[str(APlo),str(APhi)],'literal_interval_AP_error_sign':ap_sign,
   'BV_not_certified_at_this_bank':True,'BV_onset_and_K_N_remain_unpaid':True},
  'producer_incidence_not_executed':True,'D_W_kernels_not_recomputed':True,'old_PASS_not_executed':True,
  'strict_rational_only':True,'imports_sha256':s.IMPORTS,'conservation_before':before,'conservation_after':s.conservation.verify(),
  'global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'victory':False}

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=s.ROOT)
 args=parser.parse_args();data=run();out=s.conservation.output_directory(args.output_dir)
 (out/'incidence_moment.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'L4_gap':'POSITIVE','AP_error':data['AP_front']['literal_interval_AP_error_sign'],
  'X':data['AP_front']['X_exact'],'front_difference':data['AP_front']['front_difference_exact'],'kernels_recomputed':False,'victory':False}))
