"""Necessary final consistency checks of stored receipt vectors, never kernels."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from hashlib import sha256
import json
ROOT=Path(__file__).resolve().parents[1]
def parse(v):return {tuple(map(int,k.split(','))):Fraction(c) for k,c in v.items()}
def add(*vectors):
 out={}
 for v in vectors:
  for k,c in v.items():out[k]=out.get(k,Fraction(0))+c
 return {k:c for k,c in out.items() if c}
def neg(v):return {k:-c for k,c in v.items()}
def mul(v,w):
 out={}
 for k,c in v.items():
  for j,d in w.items():
   key=tuple(sorted(k+j));out[key]=out.get(key,Fraction(0))+c*d
 return {k:c for k,c in out.items() if c}
coverage=json.loads((ROOT/'coverage.json').read_text(encoding='utf-8'))
complement=json.loads((ROOT/'complement.json').read_text(encoding='utf-8'))
vertices=[]
for key,v in coverage['complete_fibre_window']['all_vertices_profiles'].items():vertices.append((3,key.startswith('P:'),v))
for group in ('C1','C2'):
 for v in complement[group]['all_actual_parent_profiles'].values():vertices.append((7,True,v))
 for v in complement[group]['all_descent_image_profiles'].values():vertices.append((7,False,v))
for c,parent,v in vertices:
 assert v['n_prime'] and v['unit'] and v['bulk'] and v['original_cap_Q']==999999 and v['front_strict']
 theta=parse(v['theta_n']);assert theta=={(v['n'],):Fraction(1)}==parse(v['raw_Lambda_N_n'])
 C,W=parse(v['C']),parse(v['W']);logc={(c,):Fraction(1)}
 assert C==(add(logc,neg(W)) if parent else add(neg(logc),W))
 assert parse(v['short_prefix'])==(neg(logc) if parent else logc)
 assert parse(v['B_prime_source'])==mul(theta,C)==parse(v['B_raw_source'])
 assert v['k1_D']==v['k1_W'] and v['k1_joint_D_minus_W']=={}
assert len({v['m'] for _,_,v in vertices})==len(vertices)==78
edge_count=0
for group in ('C1','C2'):
 G=complement[group];Ps=G['all_actual_parent_profiles'];Ts=G['all_descent_image_profiles']
 assert len({v['m'] for v in Ts.values()})==len(Ts)==G['Gamma_all_distinct_count']
 for e in G['all_descent_edges']:
  P,T=Ps[e['parent']],Ts[e['image']];h,y=e['h'],e['y']
  assert P['m']-T['m']==T['n']-P['n']==2*h*7*y
  C0=parse(P['C']);W0,W1=parse(P['W']),parse(T['W'])
  theta0,theta1=parse(P['theta_n']),parse(T['theta_n']);ratio=add(theta1,neg(theta0))
  pair=add(parse(P['B_prime_source']),parse(T['B_prime_source']))
  assert pair==add(neg(mul(C0,ratio)),mul(theta1,add(W1,neg(W0))))
  edge_count+=1
 assert parse(G['actual_cut_minus_all_neighbor_capacity'])==add(parse(G['actual_unmatched_finite_family_debt']),neg(parse(G['actual_distinct_image_capacity'])))
dest=ROOT/'role6'/'read_only_audit.json'
assert not dest.exists(),'Read-only audit already frozen'
data={'status':'PASS_NEW_STORED_VECTOR_CONSISTENCY_ONLY','vertices_checked':len(vertices),'distinct_actual_vertices':78,'complement_all_descent_X5_edges_checked':edge_count,'unique_images_and_multiplicity_verified_from_fields':True,'C_parent_image_source_raw_theta_and_k1_verified':True,'kernels_recalculated':False,'bank_reexecuted':False,'input_sha256':{f:sha256((ROOT/f).read_bytes()).hexdigest() for f in ('coverage.json','complement.json','coverage_pair_supplement.json','numerical_replay.json')},'global_D_N':False,'payments':False,'Lean_called':False,'victory':False}
dest.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps(data))
