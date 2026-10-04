"""NEW complete finite small-core fusion union; no incidence or sign assumed."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from math import gcd,prod
import argparse,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s

def local_arithmetic(e,q):
 m=e*q;n=s.N-m
 fs=s.factor(m);nf=s.factor(n)
 assert e>=2 and e<=s.A<q and s.prime(q) and s.mu(e)!=0
 assert gcd(e*q,s.N)==gcd(e,q)==1 and s.M<=m<=s.N-s.Q-1
 assert gcd(n,s.N)==1 and n>s.Q and all(ex==1 for _,ex in fs)
 shorts=[d for d in s.divisors(m) if d<=s.A]
 assert shorts==list(s.divisors(e))
 Ua=s.prefix(m,s.A);assert Ua=={k:-v for k,v in s.Lambda(e).items()}
 assert s.mu(m)==-s.mu(e) and s.Lambda(m)=={}
 theta=s.theta(n);raw=s.Lambda(n) if gcd(n,s.N)==1 and n>1 else {}
 return {'e':e,'q':q,'m':m,'n':n,'e_factorization':s.factor(e),'m_factorization':fs,'n_factorization':nf,
  'mu_e':s.mu(e),'mu_m':s.mu(m),'Lambda_e':s.serialize(s.Lambda(e)),'Lambda_m':s.serialize(s.Lambda(m)),
  'short_divisors_complete':shorts,'short_divisor_terms':[{'d':d,'mu':s.mu(d),'log_d':s.serialize(s.log_vector(d))} for d in shorts],
  'U_a':s.serialize(Ua),'theta_N_n':s.serialize(theta),'raw_Lambda_N_n':s.serialize(raw),
  'n_prime':s.prime(n),'n_proper_power':bool(raw) and not bool(theta),'unit':True,'bulk':True,'n_above_original_Q':True},theta,raw

def bilateral_indices(m):
 indices=[]
 for ell,exponent in s.factor(m):
  assert exponent==1
  b=m//ell;ratio=Fraction(1)
  for prime,_ in s.factor(b):
   if s.N%prime:ratio*=Fraction(prime-1,prime-2)
  indices.append({'deleted_prime':ell,'cofactor_b':b,'model_index_bN':b*s.N,
   'symbol':'S('+str(b*s.N)+')','positive_ratio_to_S_N_from_distinct_unit_prime_factors':str(ratio),
   'exact_weight':'log('+str(ell)+')/log('+str(m)+')','cofactor_above_a':b>s.A,
   'symbol_preserved_not_substituted_by_S_N':True})
 return indices

def run():
 before=s.conservation.verify();E=3003;cs=[21,33,39,77,91,143]
 assert s.factor(E)==((3,1),(7,1),(11,1),(13,1)) and E<=s.A and s.mu(E)==1
 labels=[];union={}
 for c in cs:
  t=E//c;assert c*t==E and s.mu(c)==1 and len(s.factor(c))==2
  for p in range(2,t):
   if not(s.prime(p) and gcd(p,c*s.N)==1):continue
   e=c*p;assert e<E and s.mu(e)==-1 and len(s.factor(e))==3
   label={'c':c,'p':p,'removed_semiprime_t':t,'removed_factorization':s.factor(t),'e':e,'mu_c':s.mu(c)}
   labels.append(label);union.setdefault(e,[]).append(label)
 assert {tuple((v['c'],v['p'])) for v in union[231]}=={(21,11),(33,7),(77,3)}
 assert 2751 in union and any(v['c']==21 and v['p']==131 for v in union[2751])
 qs=[q for q in range(8000,8201) if s.prime(q) and gcd(q,s.N)==1]
 assert qs and all(q>s.A for q in qs)
 cores=sorted(set(union)|{E,131,2751});controls={E,131,2751}
 local={};vectors={};vertex_m=set();profile_count=0;proper_power_count=0
 print(json.dumps({'stage':'complete_union_fixed','q_count':len(qs),'labels':len(labels),'distinct_parent_cores':len(union),'candidate_vertices':len(qs)*len(cores)}),flush=True)
 for q in qs:
  for e in cores:
   ar,theta,raw=local_arithmetic(e,q);m=ar['m']
   assert m not in vertex_m;vertex_m.add(m)
   assert [p for p,_ in s.factor(m) if p>s.A]==[q]
   ar['canonical_large_prime_q']=q;ar['canonical_core_e']=m//q
   ar['parent_labels_before_first_incidence']=union.get(e,[])
   ar['bilateral_deleted_prime_indices']=bilateral_indices(m)
   ar['theta_and_raw_independent_of_bulk_filter']=True
   if e in controls or theta or raw:
    profile,Bactual,C,W=s.source_profile(m);profile_count+=1
    expected=dict(s.Lambda(e));s.add(expected,W,s.mu(m));assert expected==C
    assert profile['short_prefix']==ar['U_a'] and profile['mu_m']==ar['mu_m']
    if e in (E,2751):assert s.Lambda(e)=={} and ar['U_a']=={}
    if e==131:assert C==s.add_many([s.log_vector(131),W]) and ar['U_a']==s.serialize({k:-v for k,v in s.log_vector(131).items()})
    rawB=s.multiply(raw,C);assert s.serialize(rawB)==profile['B_raw_source']
    ar['physical_profile']=profile;ar['actual_B_prime_sign_certificate']=s.resolved(Bactual)
    ar['actual_B_raw_sign_certificate']=s.resolved(rawB)
    ar['kernel_computed']=True;ar['physical_C_formula_checked']=True
    vectors[(q,e)]=(theta,raw,Bactual,rawB,W,C)
   else:
    assert not theta and not raw
    ar['kernel_computed']=False;ar['kernel_literal']='W_a(N-eq,eq) with Q and gcd(k,(N-eq)N)=1 and ak<eq'
    ar['actual_B_prime_exact_zero']=True;ar['actual_B_raw_exact_zero']=True
    ar['uncomputed_W_not_free_not_estimated']=True
    vectors[(q,e)]=(theta,raw,{}, {},None,None)
   if ar['n_proper_power']:proper_power_count+=1
   local[(q,e)]=ar
  print(json.dumps({'stage':'q_complete','q':q,'profiled_so_far':profile_count}),flush=True)
 principal={};actual={};raw_actual={};orphan_mass={};rows=[];edges=[];unused=[];pp_records=[]
 principal_pair_signs={};actual_pair_signs={};parent_prime_count=target_prime_count=0;raw_extra={}
 for q in qs:
  target=local[(q,E)];IE=bool(vectors[(q,E)][0]);active=[e for e in sorted(union) if vectors[(q,e)][0]]
  Dq=len(active);target_prime_count+=int(IE);parent_prime_count+=Dq
  delta=dict(vectors[(q,E)][0]);Bq=dict(vectors[(q,E)][2]);rawq=dict(vectors[(q,E)][3])
  for e in active:s.add(delta,vectors[(q,e)][0],-1)
  for e in union:s.add(Bq,vectors[(q,e)][2]);s.add(rawq,vectors[(q,e)][3])
  # Target actual C=-W and parent C=+W; Bq is their entire sum.
  Oq=dict(vectors[(q,E)][0]) if IE and Dq==0 else {}
  F4gap=s.difference(Oq,delta);F4cert=s.resolved(F4gap)
  assert F4cert['sign'] in ('ZERO','POSITIVE')
  s.add(principal,delta);s.add(actual,Bq);s.add(raw_actual,rawq);s.add(orphan_mass,Oq)
  for e in active:
   parent=local[(q,e)]
   if not IE:unused.append({'q':q,'e':e,'m':parent['m'],'target_n_composite':True,'retained_in_entire_principal_and_actual':True})
   else:
    pair=s.add_many([vectors[(q,e)][2],vectors[(q,E)][2]])
    delta_pair=s.difference(vectors[(q,E)][0],vectors[(q,e)][0]);pcert=s.resolved(delta_pair)
    assert pcert['sign']=='NEGATIVE' and parent['n']-target['n']==(E-e)*q>0
    Wparent,Wtarget=vectors[(q,e)][4],vectors[(q,E)][4]
    source_identity=s.multiply({k:-v for k,v in Wtarget.items()},delta_pair)
    s.add(source_identity,s.multiply(vectors[(q,e)][0],s.difference(Wparent,Wtarget)))
    assert source_identity==pair
    ac=s.resolved(pair);principal_pair_signs[pcert['sign']]=principal_pair_signs.get(pcert['sign'],0)+1
    actual_pair_signs[ac['sign']]=actual_pair_signs.get(ac['sign'],0)+1
    edges.append({'q':q,'e':e,'parent_m':parent['m'],'target_m':target['m'],'parent_n':parent['n'],'target_n':target['n'],
     'n_parent_minus_target':(E-e)*q,'parent_core_strictly_smaller':True,'labels':union[e],
     'physical_edge_count':1,'label_multiplicity':len(union[e]),'target_counted_once_in_entire_sum':True,
     'actual_pair':s.serialize(pair),'actual_pair_sign_certificate':ac,'principal_coefficient':s.serialize(delta_pair),
     'principal_sign_certificate':pcert,'source_pair_identity':'-W_target*(theta_target-theta_parent)+theta_parent*(W_parent-W_target)',
     'source_pair_identity_exact':True,'U4_error_literal':'log(n_parent)*delta_parent-log(n_target)*delta_target',
     'U4_error_unpaid':True})
  rows.append({'q':q,'I_E':int(IE),'D_distinct_parent_prime_vertices':Dq,'active_parent_cores':active,
   'active_label_count':sum(len(union[e]) for e in active),'active_physical_edges':Dq if IE else 0,
   'target_orphan':IE and Dq==0,'principal_Delta_q':s.serialize(delta),'principal_sign_certificate':s.resolved(delta),
   'orphan_majorant_F4_q':s.serialize(Oq),'F4_gap_orphan_minus_Delta':s.serialize(F4gap),'F4_gap_sign_certificate':F4cert,
   'F4_exact_for_empty_neighbors':Dq==0,'entire_actual_B_q':s.serialize(Bq),'entire_actual_sign_certificate':s.resolved(Bq),
   'entire_actual_raw_B_q':s.serialize(rawq),'retains_prime_parents_when_target_composite':True})
 for (q,e),ar in local.items():
  if ar['n_proper_power']:
   pp_records.append({'q':q,'e':e,'n':ar['n'],'factorization':ar['n_factorization'],'raw_Lambda_N_n':ar['raw_Lambda_N_n'],
    'B_raw':s.serialize(vectors[(q,e)][3]),'theta_N_n':{}})
  if e in union or e==E:s.add(raw_extra,s.difference(vectors[(q,e)][3],vectors[(q,e)][2]))
 assert s.difference(raw_actual,actual)==raw_extra
 totalgap=s.difference(orphan_mass,principal);gapcert=s.resolved(totalgap);assert gapcert['sign'] in ('ZERO','POSITIVE')
 maincert=s.resolved(principal);actualcert=s.resolved(actual);rawcert=s.resolved(raw_actual)
 orphans=[r['q'] for r in rows if r['target_orphan']]
 maxmultiplicity=max(len(x) for x in union.values())
 labels_prime_capacity=sum(sum(len(union[e]) for e in row['active_parent_cores']) for row in rows)
 assert labels_prime_capacity>=parent_prime_count
 all_vertex_uniqueness=len(vertex_m)==len(qs)*len(cores)
 unit_small_primes=[p for p in range(2,s.A+1) if s.prime(p) and gcd(p,s.N)==1]
 rank_min=prod(unit_small_primes[:5])*(s.A+1)
 assert unit_small_primes[:5]==[3,7,11,13,17] and rank_min==161525364>s.N
 J2_cmax=(s.N-s.Q-1)//((s.A+1)**2)
 J2_c=[c for c in range(1,J2_cmax+1) if s.mu(c) and gcd(c,s.N)==1]
 assert J2_cmax==9 and J2_c==[1,3,7]
 falsifiers=[{'claim':'count each cofactor label as distinct parent capacity','status':'REFUTED_NEW_UNION_MULTIPLICITY',
  'structural_labels':len(labels),'structural_distinct_cores':len(union),'prime_label_count':labels_prime_capacity,
  'prime_distinct_vertex_count':parent_prime_count,'witness_e231_labels':union[231]},
  {'claim':'all source-principal signs can be identified with the actual finite pair signs',
   'status':'REFUTED_NEW_REAL_PAIR_SIGN' if any(k!='NEGATIVE' for k in actual_pair_signs) else 'NO_COUNTEREXAMPLE_IN_WINDOW',
   'principal_pair_sign_counts':principal_pair_signs,'actual_pair_sign_counts':actual_pair_signs},
  {'claim':'every first-prime target has a first-prime parent in this structural union',
   'status':'REFUTED_NEW_ORPHAN_TARGET' if orphans else 'NO_COUNTEREXAMPLE_IN_WINDOW',
   'orphan_q':orphans,'no_universal_availability_inferred':True},
  {'claim':'a six-distinct-unit-factor split with a large q>a can lie below N in this finite bank',
   'status':'REFUTED_NEW_RANK_MINIMUM','minimum_product':rank_min,'N':s.N,'source_no_go':False}]
 return {'status':'PASS_NEW_COMPLETE_SMALL_CORE_FUSION_UNION_AND_PRINCIPAL_MAJORANT_ONLY',
  'N':s.N,'alpha':s.ALPHA,'a':s.A,'Q':s.Q,'M':s.M,'E':E,'q_window_complete':{'low':8000,'high':8200,'q_primes_unit':qs,'all_q_integers_tested':True},
  'structural_cofactor_labels_before_incidence':labels,'structural_parent_core_union':sorted(union),'structural_core_to_labels':{str(e):union[e] for e in sorted(union)},
  'physical_vertices_all_candidates':[local[key] for key in sorted(local)],'candidate_vertex_count':len(local),'computed_D_W_profiles':profile_count,
  'actual_zero_vertices_with_literal_W':len(local)-profile_count,'sample_used_for_nonzero_terms':False,
  'controls':{'2751':'common c21 p131 mu(c)=+1; C=W','3003':'canonical c231 p13 mu(c)=-1; C=-W',
   '131':'common c1 p131; C=log131+W; semiprime','physical_e1_prime_branch':'outside selected support; C_q=-logq-W',
   'bilateral_b1':'outside selected support and retained in source complement','F1_domain_e_at_least_2':True},
  'canonicality':{'unique_large_prime_q_all_vertices':True,'all_distinct_m':all_vertex_uniqueness,'core_unique_after_q_deleted':True,
   'targets_counted_once_per_q':True,'parent_cores_fused_before_incidence_and_capacity':True,'maximum_structural_label_multiplicity':maxmultiplicity,
   'first_prime_label_count':labels_prime_capacity,'first_prime_physical_vertex_count':parent_prime_count,'bilateral_model_indices_are_actual_deleted_prime_cofactors':True},
  'per_q':rows,'active_physical_edges':edges,'unused_prime_parents_target_composite':unused,
  'target_prime_count':target_prime_count,'parent_prime_vertex_count':parent_prime_count,'orphan_target_q':orphans,
  'principal_entire_Delta':s.serialize(principal),'principal_entire_sign_certificate':maincert,'orphan_mass_F6':s.serialize(orphan_mass),
  'F4_total_gap_orphan_minus_Delta':s.serialize(totalgap),'F4_total_gap_sign_certificate':gapcert,
  'entire_actual_B_prime':s.serialize(actual),'entire_actual_sign_certificate':actualcert,
  'raw_Lambda_N':{'proper_power_count':proper_power_count,'proper_power_vertices':pp_records,'entire_actual_B_raw':s.serialize(raw_actual),
   'entire_raw_sign_certificate':rawcert,'raw_minus_prime_exact':s.serialize(raw_extra),'no_mu_n_squared_filter':True},
  'U4_model_kept_symbolic':{'principal':'S(N)*principal_entire_Delta','S_N_positive_source_symbol_only':True,
   'exact_error':'sum_distinct_prime_parents theta(n)*delta_parent - sum_prime_targets theta(n)*delta_target',
   'delta_vertex_definition':'W_a(n,m)+S(N)','distinct_vertex_error_unpaid':True,'real_W_not_substituted_by_S_N':True,
   'common_N_mask_used_only_for_n_prime_above_Q':True,'no_global_union_over_other_E_paid':True},
  'rank_cut_finite':{'five_small_distinct_unit_prime_minima':unit_small_primes[:5],'q_lower_bound':s.A+1,'minimum_six_factor_product':rank_min,
   'above_N':True,'inverse_fusion_not_excluded':True,'asymptotic_no_go':False},
  'J2_composite_cofactor_empty_finite':{'c_max':J2_cmax,'squarefree_unit_c':J2_c,'no_composite_c':True,'original_a_not_changed':True},
  'ERROR_FALSIFIER':falsifiers,'imports_sha256':s.IMPORTS,'conservation_before':before,'conservation_after':s.conservation.verify(),
  'strict_rational_only':True,'finite_N_outside_source':True,'source_u_minimum':'10^24','global_D_N':False,'asymptotic':False,
  'payments':False,'Lean_called':False,'victory':False}

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=s.ROOT)
 args=parser.parse_args();data=run();directory=s.conservation.output_directory(args.output_dir)
 (directory/'fusion.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'q_count':len(data['q_window_complete']['q_primes_unit']),
  'parent_cores':len(data['structural_parent_core_union']),'target_prime':data['target_prime_count'],'parent_prime':data['parent_prime_vertex_count'],
  'active_edges':len(data['active_physical_edges']),'orphan_targets':len(data['orphan_target_q']),
  'principal_sign':data['principal_entire_sign_certificate']['sign'],'actual_sign':data['entire_actual_sign_certificate']['sign'],
  'proper_powers':data['raw_Lambda_N']['proper_power_count'],'victory':False}),flush=True)
