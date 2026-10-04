"""NEW finite C4 moment and retained tail only; no source C4/C6 application."""
import sys
sys.dont_write_bytecode=True
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
from pathlib import Path
from fractions import Fraction
from math import prod
import argparse,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as c
s=c.s
PRIMES=(2,3,5,7);ZCUT=100
def run():
 before=c.verify();rough=json.loads((c.ROUND/'rough.json').read_text(encoding='utf-8'))
 inputs=[row for row in rough['finite_selberg_by_core'] if row['status']=='EXACT_FINITE_SELBerg_SQUARE_VERIFIED']
 assert len(inputs)==16 and rough['N']==100000000 and rough['z']==ZCUT
 rows=[];positions=0
 for old in inputs:
  effective={};g={};h={}
  for p in PRIMES:
   rho=old['rho_roots_all_primes_le100'][str(p)]['rho'];assert 0<rho<p
   g[p]=Fraction(rho,p);h[p]=g[p]/(1-g[p]);assert h[p]==Fraction(old['h_exact'][str(p)])
   effective[str(p)]={'rho':rho,'g':str(g[p]),'h':str(h[p])}
  subsets=[];moment={};sumweights=Fraction(0);GP=Fraction(0);tail=Fraction(0);head=[];tailcerts=[]
  for bits in range(16):
   selected=[p for i,p in enumerate(PRIMES) if bits&(1<<i)]
   natural=prod(selected);weight=prod((h[p] for p in selected),start=Fraction(1))
   logs={(p,):Fraction(1) for p in selected};assert logs==s.log_vector(natural)
   sumweights+=weight;s.add(moment,logs,weight)
   item={'bits':bits,'primes':selected,'natural_product':natural,'weight_exact':str(weight),'log_product_exact':s.serialize(logs)}
   if natural<=ZCUT:
    assert natural in old['support_squarefree_d_le100'] and weight==Fraction(old['h_exact'][str(natural)])
    GP+=weight;head.append(natural);item['cell']='HEAD_INCLUDED_IN_ACTUAL_G100'
   else:
    tail+=weight;item['cell']='TAIL_RETAINED_PRODUCT_GT100'
    margin=s.difference(logs,s.log_vector(ZCUT));cert=s.resolved(margin);assert cert['sign']=='POSITIVE'
    item['log_product_minus_log100_exact']=s.serialize(margin);item['strict_tail_certificate']=cert
    tailcerts.append(cert);positions+=1
   subsets.append(item)
  Z=prod((1+h[p] for p in PRIMES),start=Fraction(1));assert Z==sumweights==GP+tail
  expected={(p,):Z*g[p] for p in PRIMES};assert moment==expected
  M={(p,):g[p] for p in PRIMES};assert moment=={key:Z*v for key,v in M.items()}
  actualG=Fraction(old['G_exact']);assert GP<=actualG
  condition=s.difference({key:v/2 for key,v in s.log_vector(ZCUT).items()},M)
  cert=s.resolved(condition);positions+=1
  status='CONDITION_FALSE_FINITE' if cert['sign']=='NEGATIVE' else 'CONDITION_TRUE_FINITE'
  markov=dict(moment);s.add(markov,s.log_vector(ZCUT),GP-Z)
  mcert=s.resolved(markov);positions+=1;assert mcert['sign'] in ('POSITIVE','ZERO')
  if status=='CONDITION_TRUE_FINITE':assert GP>=Z/2
  rows.append({'e':old['e'],'effective_local_values':effective,'all16_subsets':subsets,
   'Z_sum_and_product_exact':str(Z),'weighted_log_product_sum_exact':s.serialize(moment),
   'coefficient_identity_each_logp_Z_times_g_verified':True,'M_sum_g_logp_exact':s.serialize(M),
   'G_P_exact':str(GP),'Tail_weight_exact':str(tail),'G_P_plus_Tail_equals_Z':True,
   'head_products_support_inclusion':head,'G_actual100_from_frozen_catalog':str(actualG),'G_P_le_actual_G_by_inclusion':True,
   'condition_M_le_half_log100_status':status,'half_log100_minus_M_exact':s.serialize(condition),'condition_sign_certificate':cert,
   'markov_no_division_exact':s.serialize(markov),'markov_no_division_certificate':mcert,
   'markov_formula':'(G_P-Z)*log100+Z*M >=0; equivalent G_P >= Z*(1-M/log100)',
   'observed_G_P_ge_half_Z':GP>=Z/2,'half_G_not_inferred_from_false_condition':True,
   'source_C4_C6_U4_BV_not_applied':True})
  print(json.dumps({'e':old['e'],'condition':status,'Markov_sign':mcert['sign'],'G_P':str(GP),'Z':str(Z),'tail':str(tail)}),flush=True)
 return {'status':'PASS_NEW_C4_FINITE_MOMENT_AND_TAIL_ONLY','N':100000000,'P':PRIMES,'z':ZCUT,
  'input_rough_sha256':c.ROUGH_SHA,'initial_numeric_manifest_sha256':c.MANIFEST_SHA,
  'core_count':len(rows),'rows':rows,'new_interval_certificate_positions':positions,'initial390_positions_not_recounted':True,
  'true_condition_cores':[r['e'] for r in rows if r['condition_M_le_half_log100_status']=='CONDITION_TRUE_FINITE'],
  'false_condition_cores':[r['e'] for r in rows if r['condition_M_le_half_log100_status']=='CONDITION_FALSE_FINITE'],
  'no_W_kernel_or_old_bank_recomputed':True,'no_source_estimate_applied_to_finite_N':True,
  'imports_sha256':s.IMPORTS,'conservation_before':before,'conservation_after':c.verify(),
  'whole_D_N_uncontrolled':True,'global_D_N':False,'Lean_called':False,'payments':False,'asymptotic':False,'score':0,'victory':False}
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=c.ROOT);args=parser.parse_args()
 data=run();out=c.output_directory(args.output_dir)
 (out/'moment.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'cores':data['core_count'],'positions_new':data['new_interval_certificate_positions'],
  'condition_true':data['true_condition_cores'],'condition_false':data['false_condition_cores'],'initial390_not_recounted':True,'victory':False}),flush=True)
