"""New round14 H=2 family and complete ordered fibre; not an asymptotic test."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from math import gcd
import argparse,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s

def full_graph(P,T,profiles):
 edges=[(p,t) for p in P for t in T if t<p]
 used=set();matching=[];unmatched=[];steps=[];deficit=0;mass={}
 for j,p in enumerate(P,1):
  neighbors=[t for t in T if t<p]
  available=[t for t in neighbors if t not in used]
  previous=deficit;deficit=max(deficit,j-len(neighbors),0)
  indicator=deficit-previous;assert indicator in (0,1)
  if available:
   t=available[0];used.add(t);matching.append((p,t));assert indicator==0
  else:unmatched.append(p);assert indicator==1
  s.add(mass,s.log_vector(s.N-3*3581*p),indicator)
  steps.append({'j':j,'p':p,'T_j':len(neighbors),'D_previous':previous,'D_j':deficit,'unmatched_indicator':indicator,'neighbors':neighbors})
 assert len(unmatched)==deficit and all(set(steps[i]['neighbors'])<=set(steps[i+1]['neighbors']) for i in range(max(0,len(steps)-1)))
 leftover=[t for t in T if t not in used]
 whole=s.add_many([profiles[('P',p)][1] for p in P]+[profiles[('T',t)][1] for t in T])
 pair=s.add_many([s.add_many([profiles[('P',p)][1],profiles[('T',t)][1]]) for p,t in matching])
 remP=s.add_many([profiles[('P',p)][1] for p in unmatched]);remT=s.add_many([profiles[('T',t)][1] for t in leftover])
 assert whole==s.add_many([pair,remP,remT])
 degreeP={str(p):sum(x==p for x,_ in edges) for p in P};degreeT={str(t):sum(y==t for _,y in edges) for t in T}
 return {'parents':P,'images':T,'edges':edges,'degree_parent':degreeP,'degree_image':degreeT,'nested_neighborhoods':True,'prefix_steps_complete':steps,'prefix_deficit':deficit,'maximum_matching_size':len(matching),'matching':matching,'unmatched_parents':unmatched,'unmatched_images':leftover,'unmatched_prime_log_mass':s.serialize(mass),'whole_actual_B':s.serialize(whole),'matched_actual_B':s.serialize(pair),'unmatched_parent_actual_B':s.serialize(remP),'unmatched_image_actual_B':s.serialize(remT),'entire_partition_identity_exact':True,'coverage_claim_false':bool(unmatched),'unpaid_complement_retained':True}

def run():
 before=s.conservation.verify();c,q,p=3,3581,3323
 assert s.prime(q) and s.prime(p) and s.prime(3319)
 parent=s.source_profile(c*p*q);assert parent[0]['n_prime'] and parent[0]['unit'] and parent[0]['bulk']
 candidates=[]
 for h in range(1,s.H+1):
  t=p-2*h;fs=s.factor(t)
  neighbors=s.image_candidates(c,q,t,t)
  assert not neighbors
  candidates.append({'h':h,'t':t,'factorization':s.factors_json(t),'prime':s.prime(t),'squarefree':s.mu(t)!=0,'neighbors':neighbors,'failure':'not_squarefree_and_shared_factor_c' if h==1 else 'prime_not_distinct_semiprime'})
 assert s.factor(3321)==((3,4),(41,1)) and s.factor(3319)==((3319,1),)
 L=min(q-1,(s.N-s.Q-1)//(c*q));assert L==3580
 complete_integer_window=list(range(s.A+1,L+1))
 P=[x for x in complete_integer_window if s.prime(x) and gcd(c*x*q,s.N)==1 and s.prime(s.N-c*x*q) and s.N-c*x*q>s.Q and s.M<=c*x*q<=s.N-2]
 images=s.image_candidates(c,q,s.A+1,L);T=[v['t'] for v in images]
 assert 3167 in P and 3323 in P
 profiles={('P',x):s.source_profile(c*x*q) for x in P}
 profiles.update({('T',x):s.source_profile(c*x*q) for x in T})
 for x in P:assert profiles[('P',x)][0]['short_prefix']==s.serialize({k:-v for k,v in s.log_vector(c).items()}) and profiles[('P',x)][0]['mu_m']==-1
 for x in T:assert profiles[('T',x)][0]['short_prefix']==s.serialize(s.log_vector(c)) and profiles[('T',x)][0]['mu_m']==1
 E_H=[(x,t) for x in P for t in T if x-t in (2,4)]
 degP={x:sum(p==x for p,_ in E_H) for x in P};degT={x:sum(t==x for _,t in E_H) for x in T}
 assert all(v<=s.H for v in (*degP.values(),*degT.values())) and degP[3323]==0
 charge=s.add_many([{k:Fraction(v,s.H) for k,v in s.add_many([profiles[('P',x)][1],profiles[('T',t)][1]]).items()} for x,t in E_H])
 deficitP=s.add_many([{k:(1-Fraction(degP[x],s.H))*v for k,v in profiles[('P',x)][1].items()} for x in P])
 deficitT=s.add_many([{k:(1-Fraction(degT[x],s.H))*v for k,v in profiles[('T',x)][1].items()} for x in T])
 whole=s.add_many([v[1] for v in profiles.values()]);assert whole==s.add_many([charge,deficitP,deficitT])
 front=[x for x in P if x<=s.A+2*s.H];assert front==[3167]
 interior=[x for x in P if x not in front]
 obstruction=[{'t':t,'factorization':s.factors_json(t),'gcd_with_N':gcd(t,s.N)} for t in range(s.A+1,3167)]
 assert len(obstruction)==3 and all(v['gcd_with_N']>1 for v in obstruction)
 allgraph=full_graph(P,T,profiles);intgraph=full_graph(interior,T,profiles)
 assert 3167 in allgraph['unmatched_parents'] and not allgraph['prefix_steps_complete'][0]['neighbors']
 data={'status':'PASS_NEW_SHORT_SHIFT_AND_COMPLETE_FIBRE_IDENTITIES_ONLY','N':s.N,'alpha':s.ALPHA,'a':s.A,'Q':s.Q,'M':s.M,'H':s.H,'q_new':q,'parent_zero_H':parent[0],'H_candidates_complete':candidates,'H_window':{'parents':P,'images':T,'edges':E_H,'degrees_parent':{str(x):v for x,v in degP.items()},'degrees_image':{str(x):v for x,v in degT.items()},'normalized_parent_load':{str(x):str(Fraction(v,s.H)) for x,v in degP.items()},'normalized_image_load':{str(x):str(Fraction(v,s.H)) for x,v in degT.items()},'joint_edge_charge':s.serialize(charge),'parent_deficit_actual':s.serialize(deficitP),'image_deficit_actual':s.serialize(deficitT),'whole_actual_B':s.serialize(whole),'two_sided_normalized_identity_exact':True,'degrees_bounded_by_H':True},'complete_fibre_window':{'c':c,'q':q,'L':L,'integer_candidates_examined':complete_integer_window,'candidate_count':len(complete_integer_window),'P_all':P,'P_int':interior,'T':T,'front_parents':front,'front_not_promoted_to_interior_obstruction':True,'image_factorizations':images,'all_vertices_profiles':{f'{side}:{x}':v[0] for (side,x),v in profiles.items()}},'graph_all':allgraph,'graph_interior':intgraph,'new_front_parent_zero_all':{'parent':profiles[('P',3167)][0],'all_possible_t_before_p':obstruction,'neighbors':[],'claim_scope':'P_all, not P_int after removal of paid front'},'ERROR_FALSIFIER':[{'claim':'every admissible parent has a neighbor in H=2','status':'REFUTED_NEW_ZERO_FULL_H_FAMILY','parent':p,'q':q},{'claim':'the complete expanded fibre P_all has universal coverage','status':'REFUTED_NEW_ZERO_FRONT_PREFIX','parent':3167,'q':q,'interior_claim_not_refuted_by_this_witness':True}],'strict_rational_only':True,'imports_sha256':s.IMPORTS,'conservation_before':before,'conservation_after':s.conservation.verify(),'front_written_payment':'28*N^(37/64)*u^3*(1+u), not tested or certified here','source_u_minimum':'10^24','finite_N_outside_source':True,'global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'victory':False}
 return data
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=s.ROOT)
 args=parser.parse_args();data=run();d=s.conservation.output_directory(args.output_dir)
 (d/'coverage.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
 print(json.dumps({'status':data['status'],'P':len(data['graph_all']['parents']),'T':len(data['graph_all']['images']),'H_edges':len(data['H_window']['edges']),'full_edges':len(data['graph_all']['edges']),'all_deficit':data['graph_all']['prefix_deficit'],'interior_deficit':data['graph_interior']['prefix_deficit'],'victory':False}))
