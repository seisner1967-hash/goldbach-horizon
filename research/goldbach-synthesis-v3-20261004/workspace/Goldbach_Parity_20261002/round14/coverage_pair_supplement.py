"""Necessary new read-only vector check of frozen coverage receipts; no kernels."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
import json
ROOT=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
import shared as s
expected='d1d9c3a4c34d7fcb9971d3f7e23bf24eed7abd52369f04ff13990fd12cf0946f'
inputpath=ROOT/'coverage.json';assert sha256(inputpath.read_bytes()).hexdigest()==expected
dest=ROOT/'coverage_pair_supplement.json';assert not dest.exists(),'Supplement is already frozen'
data=json.loads(inputpath.read_text(encoding='utf-8'));before=s.conservation.verify()
def parse(v):return {tuple(map(int,k.split(','))):Fraction(c) for k,c in v.items()}
profiles=data['complete_fibre_window']['all_vertices_profiles'];q=data['q_new'];c=3
pairs={}
for label,edges in [('E_H',data['H_window']['edges']),('G_all',data['graph_all']['matching']),('G_int',data['graph_interior']['matching'])]:
 for p,t in edges:pairs.setdefault((p,t),[]).append(label)
checks=[]
for (p,t),memberships in sorted(pairs.items()):
 P=profiles[f'P:{p}'];T=profiles[f'T:{t}'];n0,n1=P['n'],T['n']
 assert P['n_prime'] and T['n_prime'] and P['bulk'] and T['bulk'] and P['unit'] and T['unit']
 assert p>t and (p-t)%2==0;h=(p-t)//2
 assert n1-n0==2*h*c*q and P['m']-T['m']==2*h*c*q
 W0,W1=parse(P['W']),parse(T['W']);C0,C1=parse(P['C']),parse(T['C'])
 theta0,theta1=parse(P['theta_n']),parse(T['theta_n']);logc=s.log_vector(c)
 assert theta0==s.log_vector(n0) and theta1==s.log_vector(n1)
 C0_expected=s.difference(logc,W0);C1_expected=s.difference(W1,logc)
 assert C0==C0_expected and C1==C1_expected
 B0,B1=parse(P['B_prime_source']),parse(T['B_prime_source'])
 assert B0==s.multiply(theta0,C0) and B1==s.multiply(theta1,C1)
 assert B0==parse(P['B_raw_source']) and B1==parse(T['B_raw_source'])
 actual=s.add_many([B0,B1]);ratio=s.difference(theta1,theta0)
 entropy={k:-v for k,v in s.multiply(C0,ratio).items()}
 commutator=s.multiply(theta1,s.difference(W1,W0));rhs=s.add_many([entropy,commutator])
 assert actual==rhs
 principal_constant={k:-v for k,v in s.multiply(logc,ratio).items()}
 principal_S={k:-v for k,v in ratio.items()}
 direct_principal_constant=s.difference(s.multiply(theta0,logc),s.multiply(theta1,logc))
 direct_principal_S=s.difference(theta0,theta1)
 assert principal_constant==direct_principal_constant and principal_S==direct_principal_S
 cert_const=s.assert_resolved(s.sign_certificate(principal_constant));cert_S=s.assert_resolved(s.sign_certificate(principal_S))
 assert cert_const['sign']==cert_S['sign']=='NEGATIVE'
 cert_actual=s.assert_resolved(s.sign_certificate(actual))
 checks.append({'p':p,'t':t,'h':h,'memberships':memberships,'n_parent':n0,'n_image':n1,'exact_displacement':2*h*c*q,'literal_C_parent':s.serialize(C0),'literal_C_image':s.serialize(C1),'literal_actual_pair_B':s.serialize(actual),'X5_retained_entropy':s.serialize(entropy),'X5_retained_commutator':s.serialize(commutator),'C3_C4_X5_exact':True,'raw_and_prime_axes_equal_for_these_two_primes':True,'principal_S_symbolic':{'constant':s.serialize(principal_constant),'S_N_coefficient':s.serialize(principal_S),'constant_sign_certificate':cert_const,'S_coefficient_sign_certificate':cert_S,'negative_for_S_N_nonnegative_only_principal_statement':True},'actual_pair_sign_certificate':cert_actual,'principal_sign_not_promoted_to_actual_sign':True})
result={'status':'PASS_NEW_STORED_ACTUAL_PAIR_AND_SYMBOLIC_PRINCIPAL_SUPPLEMENT_ONLY','frozen_coverage_sha256':expected,'checked_unique_pairs':len(checks),'E_H_count':len(data['H_window']['edges']),'G_all_count':len(data['graph_all']['matching']),'G_int_count':len(data['graph_interior']['matching']),'checks':checks,'stored_vectors_only_no_kernel_recalculation':True,'canonical_or_old_bank_rerun':False,'conservation_before':before,'conservation_after':s.conservation.verify(),'strict_rational_only':True,'source_u_minimum':'10^24','finite_N_outside_source':True,'global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'victory':False}
dest.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps({'status':result['status'],'checked_unique_pairs':len(checks),'counts':{'E_H':result['E_H_count'],'G_all':result['G_all_count'],'G_int':result['G_int_count']},'actual_sign_counts':{v:sum(x['actual_pair_sign_certificate']['sign']==v for x in checks) for v in ('POSITIVE','NEGATIVE','ZERO')},'sha256':sha256(dest.read_bytes()).hexdigest(),'victory':False}))
