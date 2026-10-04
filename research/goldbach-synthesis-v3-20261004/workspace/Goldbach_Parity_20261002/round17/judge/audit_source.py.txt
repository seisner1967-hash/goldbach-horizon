"""Independent Judge17. Stored arithmetic only, then five fresh new Lean builds.
No author Python imported/executed; no W/D kernel or logarithmic sign recalculated.
"""
import sys
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
import ast,hashlib,json,os,re,subprocess,time
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from math import gcd,lcm,prod
from collections import Counter
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent;ROUND=HERE.parent;BASE=ROUND.parent
INPUT=json.loads((HERE/'input_sha256.json').read_text(encoding='utf-8'))
def emit(phase,**kw):print(json.dumps({'phase':phase,**kw}),flush=True)
def digest(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for block in iter(lambda:f.read(1<<20),b''):h.update(block)
 return h.hexdigest()
def load(n):return json.loads((ROUND/n).read_text(encoding='utf-8'))
def save(n,d):(HERE/n).write_text(json.dumps(d,indent=2,sort_keys=True)+'\n',encoding='utf-8')
def verify_inputs():
 for n,h in INPUT['sha256'].items():assert digest(ROUND/n)==h,('Changed author input',n)
 for group in ('external_originals_sha256','fixed_contexts_sha256'):
  for n,h in INPUT[group].items():assert digest(Path(n))==h,n
 assert digest(INPUT['lean_executable'])==INPUT['lean_sha256']
def preservation():
 registry=load('previous_artifacts_sha256.json');assert len(registry['sha256'])==registry['file_count']==799
 for n,h in registry['sha256'].items():assert digest(BASE/n)==h,('Changed old input',n)
 actual=set();skip={'.lake','.git','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}
 for root,dirs,files in os.walk(BASE):
  dirs[:]=[d for d in dirs if d not in skip and not (re.fullmatch(r'round\d+',d) and int(d[5:])>=17)]
  for f in files:
   p=Path(root)/f
   if p!=BASE/'REPORT.md':actual.add(p.relative_to(BASE).as_posix())
 assert actual==set(registry['sha256']),{'extra':sorted(actual-set(registry['sha256'])),'missing':sorted(set(registry['sha256'])-actual)}
 return {'status':'PRESERVED','files':799,'previous':701,'round16':98,'exact_inventory':True,
  'originals':{n:digest(Path(n)) for n in INPUT['external_originals_sha256']},'old_producer_PASS_Lean_dependency_PDF_W_executed':False}
@lru_cache(maxsize=None)
def prime(n):
 if n<2:return False
 for p in (2,3,5,7,11,13,17,19,23,29,31,37):
  if n==p:return True
  if n%p==0:return False
 d=n-1;s=0
 while d%2==0:s+=1;d//=2
 for a in (2,3,5,7,11):
  if a>=n:continue
  x=pow(a,d,n)
  if x in (1,n-1):continue
  for _ in range(s-1):
   x=x*x%n
   if x==n-1:break
  else:return False
 return True
@lru_cache(maxsize=None)
def smallfactors(n):
 result=[];p=2
 while p*p<=n:
  if n%p==0:
   a=0
   while n%p==0:n//=p;a+=1
   result.append((p,a))
  p=3 if p==2 else p+2
 if n>1:result.append((n,1))
 return tuple(result)
def fact(n,fs):
 assert n>=1 and prod(p**a for p,a in fs)==n,n
 assert len({p for p,a in fs})==len(fs) and all(a>=1 and prime(p) for p,a in fs),n
 return fs
def mu(fs):return 0 if any(a>1 for p,a in fs) else (-1)**len(fs)
def divisors(fs):
 out=[1]
 for p,a in fs:out=[d*p**j for d in out for j in range(a+1)]
 return sorted(out)
def vec(v):return {k:F(c) for k,c in v.items() if F(c)}
def add(*items):
 d={}
 for v,s in items:
  for k,c in v.items():d[k]=d.get(k,F(0))+s*c
 return {k:c for k,c in d.items() if c}
def logv(n):return {str(p):F(a) for p,a in smallfactors(n)}
def lambda_v(fs):return {str(fs[0][0]):F(1)} if len(fs)==1 else {}
def bitmask(h,size):
 b=bytes.fromhex(h);assert len(b)==(size+7)//8
 assert all(not (b[i//8]>>(i%8)&1) for i in range(size,len(b)*8))
 return [bool(b[i//8]>>(i%8)&1) for i in range(size)]
def walk_signs(node,path,out):
 assert not isinstance(node,float),('Float',path)
 if isinstance(node,dict):
  if {'sign','lower','upper'}<=node.keys():
   lo,hi=F(node['lower']),F(node['upper']);s=node['sign'];assert lo<=hi and s in ('POSITIVE','NEGATIVE','ZERO')
   assert lo>0 if s=='POSITIVE' else hi<0 if s=='NEGATIVE' else lo==hi==0,path
   if node.get('rational_exact'):assert lo==hi
   out[path]={'sign':s,'lower':str(lo),'upper':str(hi)}
  for k,v in node.items():walk_signs(v,path+'.'+str(k),out)
 elif isinstance(node,list):
  for i,v in enumerate(node):walk_signs(v,path+'.'+str(i),out)
def abs_bindings(rows):
 for item in rows:assert digest(item['path'])==item['sha256'] and Path(item['path']).stat().st_size==item['bytes'],item['path']
emit('AUDIT_STARTED',utc=datetime.now(timezone.utc).isoformat())
verify_inputs();before=preservation();emit('FROZEN_INPUTS_AND_799_PRESERVED')
for n in INPUT['sha256']:
 if n.endswith('.py'):ast.parse((ROUND/n).read_text(encoding='utf-8-sig'),filename=n)
NM=load('numeric_manifest.json');F6=load('role6_final_receipt.json')
assert len(NM['sha256'])==NM['files']==33 and NM['protected_previous_files']==799
for n,h in NM['sha256'].items():assert digest(ROUND/n)==h,n
for n,h in F6['own_assets_sha256'].items():assert digest(ROUND/n)==h,n
assert F6['canonical_attempts']==3 and F6['isolated_replays']==2 and F6['real_failed_numeric_attempts']==1
assert F6['post_replay_runs']==0 and F6['interval_certificate_positions']==390
CM=load('role6_c4/manifest.json');CF=load('role6_c4/final_receipt.json')
assert len(CM['sha256_relative_role6_c4'])==CM['files']==15
for n,h in CM['sha256_relative_role6_c4'].items():assert digest(ROUND/'role6_c4'/n)==h,n
for n,h in CF['own_assets_sha256'].items():assert digest(ROUND/'role6_c4'/n)==h,n
assert digest(ROUND/CM['report_relative_round17'])==CM['report_sha256']==CF['report_sha256']
assert CF['canonical_attempts']==CF['isolated_replays']==1 and CF['real_failed_attempts']==CF['post_replay_runs']==0
assert CM['new_positions']==CF['new_positions']==64 and CM['initial390_not_recounted']
gates={};bank_audits={}
for name in ('rough','typeii'):
 p=ROUND/(name+'.json');q=ROUND/('isolated_'+name)/(name+'.json');replay=load('role6/'+name+'_replay_receipt.json');marker=load('role6/'+name+'_canonical_success.json')
 assert replay['exit_code']==marker['exit_code']==0 and replay['bytes_identical'] and replay['all_fields_identical']
 assert p.read_bytes()==q.read_bytes() and json.loads(p.read_bytes())==json.loads(q.read_bytes())
 assert digest(p)==digest(q)==replay['output_sha256']==marker['output_sha256']
 assert digest(ROUND/(name+'_checks.py'))==replay['source_sha256']==marker['producer_sha256']==digest(marker['source_snapshot'])
 for row in (replay,marker):assert digest(row['log'])==row['log_sha256']
 gate=json.loads(p.read_bytes());assert (gate['N'],gate['alpha'],gate['a'],gate['Q'],gate['M'])==(100000000,100,3163,999999,1000000)
 for n,h in gate['imports_sha256'].items():assert digest(BASE/n)==h,n
 for k in ('global_D_N','asymptotic','payments','Lean_called','victory'):assert gate[k] is False
 assert gate['strict_rational_only']
 gates[name]=gate;bank_audits[name]={'gate_sha256':digest(p),'producer_sha256':replay['source_sha256'],'bytes_identical':True,'fields_identical':True,'stored_replay_verified':True,'producer_executed_by_judge':False}
C=load('role6_c4/moment.json');cr=load('role6_c4/replay_receipt.json');cs=load('role6_c4/canonical_success.json')
assert cr['exit_code']==cs['exit_code']==0 and cr['bytes_identical'] and cr['all_fields_identical']
assert (ROUND/'role6_c4/moment.json').read_bytes()==(ROUND/'role6_c4/isolated/moment.json').read_bytes()
assert digest(ROUND/'role6_c4/moment.json')==digest(ROUND/'role6_c4/isolated/moment.json')==cr['output_sha256']==cs['output_sha256']
assert digest(ROUND/'role6_c4/moment_checks.py')==digest(ROUND/'role6_c4/attempt01_source.txt')==cr['source_sha256']==cs['source_sha256']
assert digest(ROUND/'role6_c4/attempt01.log')==cs['log_sha256'] and digest(ROUND/'role6_c4/isolated_replay.log')==cr['log_sha256']
assert C['input_rough_sha256']==digest(ROUND/'rough.json') and C['initial_numeric_manifest_sha256']==digest(ROUND/'numeric_manifest.json')
signs={};c4signs={}
for name,gate in gates.items():walk_signs(gate,name,signs)
walk_signs(C,'C4',c4signs)
assert len(signs)==390 and len(c4signs)==64 and Counter(v['sign'] for v in c4signs.values())=={'POSITIVE':54,'NEGATIVE':10}
save('rational_certificates.json',{'initial':signs,'distinct_C4':c4signs,'recomputed_signs':False,'float_or_unresolved':False})
emit('INITIAL33_AND_C4_15_BINDINGS_AND_454_STRICT_POSITIONS_VERIFIED',initial=390,distinct_C4=64)
R=gates['rough'];N=R['N'];qwin=R['q_window_complete'];cwin=R['core_window_complete']
assert (qwin['low'],qwin['high'],qwin['integer_count'])==(1200100,1200300,201)
assert [x['q'] for x in qwin['all_q_tested']]==list(range(1200100,1200301))
for row in qwin['all_q_tested']:
 fs=fact(row['q'],row['factorization']);assert row['prime']==(fs==[[row['q'],1]]) and row['unit']==(gcd(row['q'],N)==1)
qs=[x['q'] for x in qwin['all_q_tested'] if x['prime'] and x['unit']];assert qs==qwin['prime_unit_q'] and len(qs)==9
assert cwin['cap_all_201_q']==82 and [x['e'] for x in cwin['all_e_examined']]==list(range(1,83))
for row in cwin['all_e_examined']:
 fs=fact(row['e'],row['factorization']);assert row['squarefree']==bool(mu(fs)) and row['unit']==(gcd(row['e'],N)==1)
es=[x['e'] for x in cwin['all_e_examined'] if x['squarefree'] and x['unit']];assert es==cwin['squarefree_unit_cores'] and len(es)==28
for e in es:
 row=cwin['core_catalog'][str(e)];fs=fact(e,row['factorization']);assert row['mu_e']==mu(fs) and row['rank']==len(fs)
 assert vec(row['Lambda_e_exact'])==lambda_v(fs) and row['divisors_complete']==divisors(fs)
cat=R['physical_candidates_catalog'];kernels=R['kernel_catalog'];assert len(cat)==252 and len(kernels)==47
assert {int(m) for m in cat}=={e*q for e in es for q in qs}
for key,row in cat.items():
 e,q,m,n=row['e'],row['q'],row['m'],row['n'];assert int(key)==m==e*q and n==N-m and m<=N-2 and m>R['Q'] and gcd(m,N)==1
 assert row['canonical_e']==e and row['unique_large_prime_q']==q and row['physical_count']==1
 fs=fact(n,row['n_factorization']);th={str(n):F(1)} if fs==[[n,1]] else {};raw=lambda_v(fs)
 assert vec(row['theta_exact'])==th and vec(row['raw_Lambda_N_exact'])==raw
 assert row['prime_axis_active']==bool(th) and row['proper_power_axis_active']==bool(raw and not th)
 assert row['short_divisors_complete']==divisors(smallfactors(e)) and vec(row['U_a_exact'])==add((lambda_v(smallfactors(e)),-1))
 assert row['mu_m']==-mu(smallfactors(e)) and vec(row['Lambda_m_exact'])==({str(q):F(1)} if e==1 else {})
 assert row['unit'] and row['bulk'] and row['n_above_original_Q'] and row['small_factor_exclusion_verified']
 for item in row['bilateral_actual_deleted_prime_indices']:
  p=item['deleted_prime'];b=m//p;assert b==item['b'] and item['S_index_bN']==b*N and item['S_bN_not_substituted']
  ratio=prod((F(l-1,l-2) for l,a in smallfactors(b) if N%l),start=F(1));assert F(item['ratio_to_S_N'])==ratio
 if 'kernel_ref' in row:
  assert row['kernel_ref']==key and key in kernels
  recipe=row['C_recipe'];assert recipe['W_ref']==key and F(recipe['W_scale'])==row['mu_m']
  assert vec(recipe['constant_exact'])==({str(q):F(-1)} if e==1 else lambda_v(smallfactors(e)))
for key,k in kernels.items():
 assert k['m']==int(key) and k['n']==N-int(key) and k['R']==min(R['Q'],(int(key)-1)//R['a']) and k['original_Q']==R['Q']
 assert k['front_strict_verified'] and k['k1_joint_cancels'] and k['physical_source_identity_verified']
 assert vec(k['whole_U_a'])==vec(cat[key]['U_a_exact'])
 assert vec(k['annulus'])==add((vec(k['whole_U_a']),1),(vec(k['U_alpha']),-1))
 assert vec(k['D_exact'])==add((vec(k['whole_U_a']),1),(vec(cat[key]['Lambda_m_exact']),-1))
 assert vec(k['k1_D_and_W_exact'])==add((logv(int(key)),-1))
 # Stored W is an immutable primitive, never a new harmonic evaluation.
 assert all(isinstance(v,str) and F(v) for v in k['W_exact'].values())
assert sum('kernel_ref' not in row for row in cat.values())==R['literal_zero_axis_W_count']==205
resource_cells={row['q']:row for row in R['q_resources_and_small_factor_cells']};parts=R['partition_active_demands']
assert len(resource_cells)==9
for q,row in resource_cells.items():
 for j in (1,3):
  n=N-j*q;fs=fact(n,row['n'+str(j)+'_factorization']);assert row['n'+str(j)]==n
  small=[p for p,a in fs if p<=100];assert row['n'+str(j)+'_small_prime_factors']==small and row['I'+str(j)]==(fs==[[n,1]])
 cell='A' if row['I1'] or row['I3'] else ('R' if not row['n1_small_prime_factors'] and not row['n3_small_prime_factors'] else 'S')
 assert row['cell_for_active_demands']==cell and row['resource_m_ids']==[q,3*q]
 if cell=='S':
  w=row['small_factor_witness'];j=1 if row['n1_small_prime_factors'] else 3
  assert w['j']==j and w['ell_least_prime_factor']==row['n'+str(j)+'_small_prime_factors'][0]
for e in es:
 if e<=3:continue
 p=parts[str(e)]
 for cell in ('A','R','S'):assert p[cell]==[q for q in qs if cat[str(e*q)]['prime_axis_active'] and resource_cells[q]['cell_for_active_demands']==cell]
counts={s:sum(len(p[s]) for p in parts.values()) for s in ('A','R','S')};assert counts=={'A':11,'R':0,'S':18}
assert R['whole_positive_demand_minus_resources']['sign_certificate']['sign']=='POSITIVE'
def check_recipes(node):
 if isinstance(node,dict):
  if 'exact_recipe' in node:
   rows=node['exact_recipe'];assert len({(r['m'],r['axis']) for r in rows})==len(rows)
   for r in rows:assert str(r['m']) in cat and r['axis'] in ('theta','raw') and F(r['scale'])
  for v in node.values():check_recipes(v)
 elif isinstance(node,list):
  for v in node:check_recipes(v)
check_recipes(R)
primes=[p for p in range(2,101) if prime(p)];assert R['all_local_primes_le100']==primes
sieve_by_e={row['e']:row for row in R['finite_selberg_by_core']};sat=[];unsat=[];crtpositions=0
support=[d for d in range(1,101) if mu(smallfactors(d))]
for e,row in sieve_by_e.items():
 delta=N*e*3*(e-1)*(e-3)*2;assert row['Delta_e']==delta
 roots={p:row['rho_roots_all_primes_le100'][str(p)]['roots'] for p in primes}
 for p,rs in roots.items():
  assert rs==[x for x in range(p) if x*(N-e*x)*(N-x)*(N-3*x)%p==0]
  assert row['rho_roots_all_primes_le100'][str(p)]['rho']==len(rs) and 1<=len(rs)<=min(4,p)
  if delta%p:assert len(rs)==4
 rough=[q for q in range(1200100,1200301) if all(q*(N-e*q)*(N-q)*(N-3*q)%p for p in primes)]
 assert row['rough_integer_q']==rough and row['physical_R_prime_q']==parts[str(e)]['R']
 saturated=[p for p,rs in roots.items() if len(rs)==p]
 if saturated:
  sat.append(e);assert row['saturating_primes']==saturated and row['G_or_lambda_not_formed'] and not rough
  continue
 unsat.append(e);assert row['support_squarefree_d_le100']==support
 h={d:F(row['h_exact'][str(d)]) for d in support};lam={d:F(row['lambda_exact'][str(d)]) for d in support};G=F(row['G_exact'])
 assert G==sum(h.values(),F(0)) and G>0 and lam[1]==1 and all(abs(v)<=1 for v in lam.values())
 for d in support:
  fs=smallfactors(d);assert h[d]==prod((F(len(roots[p]),p-len(roots[p])) for p,a in fs),start=F(1))
  tail=sum((h[r] for r in support if r<=100//d and gcd(r,d)==1),F(0))
  assert lam[d]==mu(fs)*prod((F(p,p-len(roots[p])) for p,a in fs),start=F(1))*tail/G
  diag=sum((lam[t]*F(prod(len(roots[p]) for p,a in smallfactors(t)),t) for t in support if t%d==0),F(0))
  assert diag==F(row['mobius_diagonal_inner_sums'][str(d)])==mu(fs)*h[d]/G
 grouped={};absgroup={}
 for d in support:
  for t in support:
   k=lcm(d,t);value=lam[d]*lam[t];grouped[k]=grouped.get(k,F(0))+value;absgroup[k]=absgroup.get(k,F(0))+abs(value)
 assert [x['lcm'] for x in row['CRT_lcm_catalog']]==sorted(grouped)
 gram=F(0);signed=F(0);abserror=F(0);crtbound=F(0)
 for cr in row['CRT_lcm_catalog']:
  k=cr['lcm'];rs=[0];previous=1
  for p,a in smallfactors(k):
   assert a==1;inv=pow(previous,-1,p);rs=[x+previous*((y-x)*inv%p) for x in rs for y in roots[p]];previous*=p
  rs.sort();assert previous==k and len(set(rs))==len(rs)==cr['rho_product']
  assert hashlib.sha256(json.dumps(rs,separators=(',',':')).encode()).hexdigest()==cr['CRT_roots_sha256']
  count=sum((1200300-x)//k-(1200099-x)//k for x in rs);rho=cr['rho_product'];rem=F(count)-F(201*rho,k)
  assert count==cr['integer_count_exact'] and rem==F(cr['remainder_exact']) and abs(rem)<=rho
  assert F(cr['lambda_pair_sum'])==grouped[k] and F(cr['absolute_lambda_pair_sum'])==absgroup[k]
  gram+=grouped[k]*F(rho,k);signed+=grouped[k]*rem;abserror+=absgroup[k]*abs(rem);crtbound+=absgroup[k]*rho;crtpositions+=1
 assert gram==F(row['principal_quadratic_exact'])==1/G
 assert signed==F(row['signed_CRT_remainder_exact']) and abserror==F(row['absolute_pairwise_remainder_error']) and crtbound==F(row['CRT_plus1_absolute_bound'])
 sq=F(0)
 for x in row['integer_squares_201']:
  q=x['q'];f=q*(N-e*q)*(N-q)*(N-3*q);inner=sum((lam[d] for d in support if f%d==0),F(0));assert inner==F(x['divisor_lambda_sum'])
  assert F(x['square'])==inner**2 and x['rough_mask']==int(q in rough) and inner**2>=x['rough_mask'];sq+=inner**2
 assert sq==F(row['square_sum_exact'])==F(201)/G+signed and len(rough)<=sq<=F(201)/G+abserror<=F(201)/G+crtbound
assert len(sat)==10 and len(unsat)==16
bank_audits['rough'].update(q_integers=201,q_primes=9,cores=28,candidates=252,kernels47_read_only=True,active_partition=counts,saturated10=sat,unsaturated16=unsat,CRT_stored_rows_verified=crtpositions,whole_deficit_sign='POSITIVE',finite_C6_not_applied=True,global_payment=False)
emit('ROUGH_STORED_SUPPORT_ROOTS_WEIGHTS_CRT_AND_PARTITIONS_VERIFIED',CRT_rows=crtpositions,saturated=len(sat),unsaturated=len(unsat))
T=gates['typeii'];pg=T['progression_complete'];lo,hi=pg['b_low'],pg['b_high'];size=hi-lo+1
assert (lo,hi,size)==(974026,1136363,162338) and (pg['n_low'],pg['n_high'],pg['length_X'])==(12500049,24999998,12499950)
def columns(s):return [[tuple(map(int,t.split('^'))) for t in row.split('*')] if row else [] for row in s.split(';')]
bfs=columns(pg['b_factorizations_complete_column']);jfs=columns(pg['j_factorizations_complete_column']);assert len(bfs)==len(jfs)==size
pm=bitmask(pg['theta_prime_mask_hex'],size);bm=bitmask(T['beta_structural']['mask_hex'],size);masks={k:bitmask(v['mask_hex'],size) for k,v in T['unit_conventions'].items()}
assert set(masks)=={'0:1','0:3','0:39','77:1','77:3','77:39'}
ch=T['character13']['values'];assert ch==[0]+[1 if a in (1,3,4,9,10,12) else -1 for a in range(1,13)] and T['character13']['chiN']==1
for a in range(13):
 for b in range(13):assert ch[(a*b)%13]==ch[a]*ch[b]
primecount=0;pp=[];multip=Counter();vertices=[]
for i in range(size):
 b=lo+i;j=N-77*b;fsb=fact(b,bfs[i]);fsj=fact(j,jfs[i]);isprime=fsj==[(j,1)]
 primecount+=isprime;assert pm[i]==bool(isprime and gcd(j,N)==1)
 structural=(len(fsb)==2 and all(a==1 for p,a in fsb) and 7*fsb[0][0]<=3163<11*fsb[0][0]<fsb[1][0] and fsb[0][0]>11 and fsb[1][0]>3163 and gcd(77*b,N)==1)
 assert bm[i]==structural
 if structural:vertices.append((b,fsb[0][0],fsb[1][0],77*b,j))
 for k,mask in masks.items():assert mask[i]==(gcd(b,T['unit_conventions'][k]['gcd_modulus'])==1)
 vs=[v for v in (17,19) if j%v==0];multip[str(len(vs))]+=1
 for v in vs:
  w=j//v;assert j==v*w and w>1 and ch[v%13]*ch[w%13]==ch[j%13]
 if isprime:assert not vs
 if len(fsj)==1 and fsj[0][1]>1:pp.append((b,j,fsj[0][0],fsj[0][1]))
assert primecount==pg['candidate_prime_count'] and sum(pm)==pg['theta_candidate_count']==12460
assert sum(bm)==T['beta_structural']['A']==181 and len(vertices)==181
stored=[(x['b'],x['s'],x['q'],x['m'],x['j']) for x in T['beta_structural']['canonical_vertices']];assert sorted(stored)==sorted(vertices) and len(set(stored))==181
assert multip==T['v_complete']['multiplicity_counts'] and multip=={'0':144747,'1':17088,'2':503}
assert T['v_complete']['eligible']==[17,19]
for k,mask in masks.items():
 u=T['unit_conventions'][k];scope,h=map(int,k.split(':'));assert u['scope']==scope and u['h']==h and u['gcd_modulus']==(77 if scope else 1)*h*N
 assert sum(mask)==u['J'] and F(u['rho_exact'])==F(181,u['J']) and all(not bm[i] or mask[i] for i in range(size))
assert [T['unit_conventions'][k]['J'] for k in ('0:1','0:3','0:39','77:1','77:3','77:39')]==[64936,43291,39961,50599,33732,31136]
for row in T['v_complete']['products_by_v_complete_recipes']:
 v=row['v'];first=lo+(N*pow(77,-1,v)-lo)%v;last=hi-(hi-N*pow(77,-1,v))%v
 assert (row['b_first'],row['b_last'],row['b_step'],row['count'])==(first,last,v,(last-first)//v+1)
 assert row['w_at_first']==(N-77*first)//v and row['w_at_last']==(N-77*last)//v and row['w_step_when_b_increases']==-77
rows=T['raw_Lambda_N']['all_proper_power_factorizations'];assert [(x['b'],x['j'],x['factorization'][0][0],x['factorization'][0][1]) for x in rows]==pp
assert len(pp)==T['raw_Lambda_N']['unit_proper_power_count']==8 and all(gcd(j,N)==1 for b,j,p,a in pp)
for row in rows:assert vec(row['raw_Lambda_N_exact'])=={str(row['factorization'][0][0]):F(1)}
for row in T['AP_physical_fibres']:
 s=row['s'];L=max(3163,11*s,11,(lo+s-1)//s-1);H=hi//s
 assert row['L_phys_strict']==L and row['H_phys_inclusive']==H
 assert row['L_source_strict']==(3*N+4*77*s-1)//(4*77*s)-1 and row['H_source_inclusive']==(7*N+8*77*s-1)//(8*77*s)-1
 qs=[q for q in range(L+1,H+1) if prime(q)];assert qs==row['q_primes_all'] and len(qs)==row['C_s_all']
 assert row['q_unit_retained']==[q for q in qs if gcd(7*11*s*q,N)==1]
 for ap in row['AP_by_v']:
  v=ap['v'];a=N*pow(77*s,-1,v)%v;assert ap['q_class_required_mod_v']==a and len(ap['classes_unit_mod13'])==12
  for cr in ap['classes_unit_mod13']:
   t=cr['t_mod13'];res=cr['q_residue_mod13v'];assert res%v==a and res%13==t and gcd(res,13*v)==1
   ct=sum(q%(13*v)==res for q in qs);ref=F(len(qs),12*(v-1));assert ct==cr['count_prime_exact'] and F(cr['C_s_all_over_phi13v'])==ref and F(cr['exact_count_residual'])==ct-ref
   assert cr['character_weight']==ch[(N-77*s*t)%13]
  assert ap['B1_character_sum']==-1
for weight in ('theta','II','II_raw'):
 fun=T['functionals_exact'][weight];prices=T['prices_by_weight'][weight];assert prices['prices_have_this_weight_only']==weight and prices['U1_U2_and_full_telescope_exact']
 for k,row in fun['by_mask'].items():
  assert row['reference'].get('expression',row['reference'].get('exact_expression'))['weight']==weight
  assert row['normalized_x_over_A'].get('expression',row['normalized_x_over_A'].get('exact_expression'))['scale']=='25000000/181'
 if weight=='II':
  beta=F(fun['beta_primitive']['exact_rational']);refs={k:F(v['reference']['exact_rational']) for k,v in fun['by_mask'].items()};z={k:F(v['z_functional']['exact_rational']) for k,v in fun['by_mask'].items()}
  assert beta==-4
  for k,row in fun['by_mask'].items():
   u=F(fun['unscaled_mask_primitives'][k]['exact_rational']);assert refs[k]==F(T['unit_conventions'][k]['rho_exact'])*u and z[k]==beta-refs[k]
   assert F(row['normalized_x_over_A']['exact_rational'])==F(25000000,181)*z[k]
  for h in (1,3,39):assert F(prices['E77'][str(h)]['exact_rational'])==refs['77:'+str(h)]-refs['0:'+str(h)]
  for scope in ('0','77'):
   assert F(prices['L3'][scope]['exact_rational'])==refs[scope+':3']-refs[scope+':1']
   assert F(prices['L13'][scope]['exact_rational'])==refs[scope+':39']-refs[scope+':3']
  assert [z[k] for k in ('0:1','0:3','0:39','77:1','77:3','77:39')]==list(map(F,['-259563/64936','-173345/43291','-93236/39961','-202939/50599','-11425/2811','-18647/7784']))
for k,model in T['theta_AP_references_and_exact_errors'].items():
 assert model['actual_theta_primitive_ref']==k and model['finite_AP_reference_only_no_BV']
 assert F(model['length_X_principal'])==F(model['coefficient_exact'])*pg['length_X']
assert T['Gamma39_unestimated'] and T['no_BV_onset_certified'] and T['AP_decomposition']['BV_not_applied']
bank_audits['typeii'].update(integers=size,theta12460=True,beta181=True,six_actual_unit_masks=True,real_j_vw=True,double323=503,proper_powers8=True,weight_specific_prices=True,physical_caps=True,full_TypeII_Gamma_global_unproved=True)
emit('TYPEII_STORED_FULL_COLUMNS_SIX_MASKS_CAPS_REAL_PRODUCTS_AND_PRICES_VERIFIED',integers=size,beta=181)
assert (C['N'],C['P'],C['z'],C['core_count'])==(N,[2,3,5,7],100,16)
assert sorted(x['e'] for x in C['rows'])==sorted(unsat)
true=[];false=[]
for row in C['rows']:
 e=row['e'];g={};h={};sieve=sieve_by_e[e]
 for p in C['P']:
  rho=sieve['rho_roots_all_primes_le100'][str(p)]['rho'];g[p]=F(rho,p);h[p]=F(rho,p-rho)
  local=row['effective_local_values'][str(p)];assert local['rho']==rho and F(local['g'])==g[p] and F(local['h'])==h[p]
 Z=F(row['Z_sum_and_product_exact']);GP=F(row['G_P_exact']);Tail=F(row['Tail_weight_exact'])
 assert Z==prod((1+h[p] for p in C['P']),start=F(1)) and GP+Tail==Z and F(row['G_actual100_from_frozen_catalog'])==F(sieve['G_exact'])
 head=[];tails=[];weights=[];coeff={str(p):F(0) for p in C['P']}
 assert len(row['all16_subsets'])==16
 for b,subset in enumerate(row['all16_subsets']):
  ps=[p for i,p in enumerate(C['P']) if b>>i&1];m=prod(ps);w=prod((h[p] for p in ps),start=F(1))
  assert subset['bits']==b and subset['primes']==ps and subset['natural_product']==m and F(subset['weight_exact'])==w and vec(subset['log_product_exact'])=={str(p):F(1) for p in ps}
  for p in ps:coeff[str(p)]+=w
  if m<=100:
   head.append(m);assert subset['cell'].startswith('HEAD') and m in sieve['support_squarefree_d_le100'] and F(sieve['h_exact'][str(m)])==w
  else:
   tails.append(m);assert subset['cell'].startswith('TAIL') and subset['strict_tail_certificate']['sign']=='POSITIVE'
   assert vec(subset['log_product_minus_log100_exact'])==add((logv(m),1),(logv(100),-1))
  weights.append((m,w))
 assert tails==[105,210] and head==row['head_products_support_inclusion']
 assert GP==sum((w for m,w in weights if m<=100),F(0)) and Tail==sum((w for m,w in weights if m>100),F(0))
 assert vec(row['weighted_log_product_sum_exact'])==coeff=={str(p):Z*g[p] for p in C['P']}
 M={str(p):g[p] for p in C['P']};assert vec(row['M_sum_g_logp_exact'])==M
 assert vec(row['half_log100_minus_M_exact'])==add((logv(100),F(1,2)),(M,-1))
 assert vec(row['markov_no_division_exact'])==add((logv(100),GP-Z),(M,Z)) and row['markov_no_division_certificate']['sign']=='POSITIVE'
 assert GP<=F(sieve['G_exact']) and row['G_P_le_actual_G_by_inclusion'] and row['G_P_plus_Tail_equals_Z'] and row['source_C4_C6_U4_BV_not_applied']
 assert row['observed_G_P_ge_half_Z']==(2*GP>=Z)
 if row['condition_sign_certificate']['sign']=='POSITIVE':assert row['condition_M_le_half_log100_status']=='CONDITION_TRUE_FINITE';true.append(e)
 else:assert row['condition_M_le_half_log100_status']=='CONDITION_FALSE_FINITE';false.append(e)
assert true==C['true_condition_cores'] and false==C['false_condition_cores'] and len(true)==6 and len(false)==10
c4audit={'gate_sha256':digest(ROUND/'role6_c4/moment.json'),'stored_replay_verified':True,'initial33_unchanged':True,'new_positions':64,'sign_distribution':dict(Counter(v['sign'] for v in c4signs.values())),
 'true_condition_cores':true,'false_condition_cores':false,'all_markov16_positive':True,'all_tails105_210_retained':True,'observed_G_P_half_Z_even_false_condition':True,'source_C4_C6_U4_BV_not_applied':True,'producer_reexecuted':False}
emit('DISTINCT_C4_STORED_MOMENT_TAIL_AND_FALSE_CONDITIONS_VERIFIED',TRUE=6,FALSE=10)
FR3=load('role3/final_receipt.json');FR4=load('role4/final_receipt.json');abs_bindings(FR3['files']);abs_bindings(FR4['bindings'])
assert FR3['theorem_count']==42 and FR3['definition_count']==23 and FR4['totals']=={'modules':4,'theorems':51,'defs':17,'instances':1,'axioms_printed':69}
failures=[];warnings=[];author_invocations=[]
for role,expected,failed in [('role3',14,12),('role4',16,11)]:
 br=load(role+'/build_receipt.json');assert len(br['attempts'])==expected
 for a in br['attempts']:
  assert digest(a['snapshot'])==a['snapshot_sha256']==a['source_sha256'] and digest(a['log'])==a['log_sha256']
  text=Path(a['log']).read_text(encoding='utf-8');entry={'role':role,'attempt':a['attempt'],'exit_code':a['exit_code'],'snapshot':a['snapshot'],'snapshot_sha256':a['snapshot_sha256'],'log':a['log'],'log_sha256':a['log_sha256']}
  author_invocations.append(entry)
  if a['exit_code']!=0:
   assert 'error:' in text;entry['classification']='TECHNICAL_LEAN_API_CAST_FINITESET_OR_PROOF_ELABORATION';entry['analytic_parity_failure']=False
   entry['actual_error_lines']=[line for line in text.splitlines() if 'error:' in line];failures.append(entry)
  elif 'warning:' in text:warnings.append(entry)
 assert sum(a['exit_code']!=0 for a in br['attempts'])==failed
assert len(author_invocations)==30 and len(failures)==23 and len(warnings)==1 and warnings[0]['role']=='role4' and warnings[0]['attempt']==15
numeric_failure=load('role6/typeii_attempt01_failure.json');assert numeric_failure['exit_code']!=0
save('author_failures.json',{'Lean_invocations':author_invocations,'real_Lean_failures23':failures,'PASS15_warning':warnings,'numeric_failure':numeric_failure,
 'numeric_classification':'TECHNICAL_FACTOR_DOMAIN_RAD_HN_EXCEEDS_N_CORRECTED_BY_BOUNDED_FACTOR_UNION','parity_deduction_failure_invented':False})
emit('AUTHOR_30_INVOCATIONS_23_REAL_FAILURES_AND_PASS15_WARNING_ARCHIVED')
LEAN=Path(INPUT['lean_executable']);CACHE=Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
cachecommit=subprocess.run(['git','rev-parse','HEAD'],cwd=CACHE/'mathlib',capture_output=True,text=True,check=True).stdout.strip();assert cachecommit=='9837ca9d65d9de6fad1ef4381750ca688774e608'
build=HERE/'build';build.mkdir(exist_ok=False)
libs=[p/'.lake/build/lib' for p in sorted(CACHE.iterdir()) if (p/'.lake/build/lib').is_dir()];assert len(libs)==8
module_specs=[('role4/FourFormRoots.lean',33,10,1),('role4/PowersetMoment.lean',5,2,0),('role3/SelbergFourForms.lean',42,23,0),('role4/FourFormTruncation.lean',8,2,0),('role4/FourFormCollisionLoss.lean',5,3,0)]
modules=[];allaxioms={};allowed={'propext','Classical.choice','Quot.sound'};newcounts=Counter()
for name,nt,nd,ni in module_specs:
 original=ROUND/name;source=build/original.name;source.write_bytes(original.read_bytes());text=source.read_text(encoding='utf-8')
 stripped=re.sub(r'/\-.*?\-/','',text,flags=re.S);stripped=re.sub(r'--[^\n]*','',stripped)
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|sorryAx)\b',stripped),name
 declarations=re.findall(r'^\s*(?:private\s+)?(?:noncomputable\s+)?(theorem|lemma|def|instance)\s+([A-Za-z_][\w\u0080-\uffff]*)',stripped,re.M)
 ct=Counter('theorem' if k=='lemma' else k for k,n in declarations);assert (ct['theorem'],ct['def'],ct['instance'])==(nt,nd,ni),(name,ct)
 prints=re.findall(r'^\s*#print axioms\s+(\S+)',stripped,re.M);assert len(prints)==len(declarations) and Counter(prints)==Counter(n for k,n in declarations),(name,prints,declarations)
 imports=re.findall(r'^import\s+(\S+)',stripped,re.M)
 for imp in imports:assert imp=='Mathlib' or (build/(imp+'.olean')).is_file(),(name,imp)
 snapshot=HERE/(original.stem+'_source.lean.txt');snapshot.write_bytes(source.read_bytes());assert digest(snapshot)==digest(original)
 output=build/(original.stem+'.olean');log=HERE/(original.stem+'.log');env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join(map(str,[build]+libs))
 command=[str(LEAN),'-o',str(output),str(source)]
 emit('FRESH_LEAN_STARTED',module=original.stem,source_sha256=digest(source),imports=imports)
 t0=time.monotonic();p=subprocess.run(command,cwd=build,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace');log.write_text(p.stdout+p.stderr,encoding='utf-8')
 entry={'module':original.stem,'source_original':str(original),'source':str(source),'source_sha256':digest(source),'snapshot':str(snapshot),'snapshot_sha256':digest(snapshot),'output':str(output),'log':str(log),'log_sha256':digest(log),'exit_code':p.returncode,'command':command,'seconds':round(time.monotonic()-t0,3),'theorems':nt,'defs':nd,'instances':ni,'imports':imports}
 modules.append(entry);save('independent_compilations.json',{'modules':modules,'cache_mathlib_commit':cachecommit,'LEAN_PATH':env['LEAN_PATH'],'dependencies_compiled':False})
 assert p.returncode==0 and output.is_file() and 'error:' not in p.stdout+p.stderr and 'warning:' not in p.stdout+p.stderr,(original.stem,p.returncode)
 entry['olean_sha256']=digest(output);parsed={}
 for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",p.stdout+p.stderr,re.S):parsed[match.group(1)]=[x.strip() for x in match.group(2).split(',') if x.strip()]
 for match in re.finditer(r"'([^']+)' does not depend on any axioms",p.stdout+p.stderr):parsed[match.group(1)]=[]
 assert len(parsed)==len(declarations),(original.stem,len(parsed),len(declarations))
 assert Counter(n.rsplit('.',1)[-1] for n in parsed)==Counter(n for k,n in declarations)
 for n,axes in parsed.items():assert set(axes)<=allowed,(n,axes)
 entry['axioms_printed']=len(parsed);entry['axioms']=parsed;allaxioms.update(parsed);newcounts.update(ct)
 save('independent_compilations.json',{'modules':modules,'cache_mathlib_commit':cachecommit,'LEAN_PATH':env['LEAN_PATH'],'dependencies_compiled':False})
 emit('FRESH_LEAN_PASS',module=original.stem,axioms=len(parsed),exit_code=p.returncode,olean_sha256=entry['olean_sha256'])
assert newcounts=={'theorem':93,'def':40,'instance':1} and len(allaxioms)==134 and len(modules)==5
save('axioms.json',{'all_new_declarations134':allaxioms,'allowed_only':sorted(allowed),'custom_axioms':False,'sorryAx':False})
verify_inputs();after=preservation()
result={'status':'PASS_INDEPENDENT_ROUND17_FROZEN_PARTIAL_AUDIT','timestamp_utc':datetime.now(timezone.utc).isoformat(),
 'input_manifest_sha256':digest(HERE/'input_sha256.json'),'input_sha256':INPUT['sha256'],'frozen_files':len(INPUT['sha256']),
 'independent_new_compiles':modules,'producer_Lean_failures':failures,'producer_PASS15_warning':warnings,
 'producer_Lean_invocations':30,'producer_Lean_real_failures':23,'producer_numeric_real_failures':1,
 'rational_signs':len(signs),'rational_sign_distribution':dict(Counter(v['sign'] for v in signs.values())),
 'distinct_C4_rational_signs':len(c4signs),'distinct_C4_sign_distribution':dict(Counter(v['sign'] for v in c4signs.values())),
 'bank_audits':bank_audits,'distinct_C4_bank_audit':c4audit,'preservation_before':before,'preservation_after':after,
 'new_counts':{'modules':5,'theorems':93,'defs':40,'instances':1,'axioms_printed':134},
 'previous_counts':{'modules':17,'theorems':244},'cumulative_counts':{'modules':22,'theorems':337},
 'author_FINAL_files_changed':False,'old_or_new_numeric_producer_called':False,'W_or_log_sign_recomputed':False,'old_Lean_or_dependency_compiled':False,
 'actual_G_h_rho_unconditional_definitions':True,'G_equivalent_conclusion_assumed':False,'G_lower_derived_conditional_on_independent_prime_log_input':True,
 'source_C4_full_constants_Mertens_totient_CRT_plus1_C6_unformalized':True,'whole_D_N_uncontrolled':True,
 'availability_assumed':False,'A7_acquired16_unchanged':True,'A_S_global_capacity_Gamma_full_TypeII_unpaid':True,
 'finite_N_source_onset_not_applied':True,'parity_obstacle_bypass_proved':False,'score':0,'victory':False}
save('audit_receipt.json',result)
emit('AUDIT_COMPLETE_PARTIAL_ONLY',new_modules=5,new_theorems=93,new_defs=40,axioms134=True,score=0,victory=False,receipt_sha256=digest(HERE/'audit_receipt.json'))
