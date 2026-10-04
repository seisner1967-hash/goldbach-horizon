"""New round14 contracts; historical helpers loaded inertly only after SHA checks."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from importlib.util import spec_from_file_location,module_from_spec
from fractions import Fraction
from math import gcd,isqrt
import json
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parent
PROTECTED=json.loads((ROOT/'previous_artifacts_sha256.json').read_text(encoding='utf-8'))['sha256']
IMPORTS={}
def load(name,relative):
 p=(BASE/relative).resolve();h=sha256(p.read_bytes()).hexdigest()
 assert PROTECTED[relative]==h,(relative,h)
 spec=spec_from_file_location(name,p);m=module_from_spec(spec);sys.modules[name]=m
 saved=list(sys.path)
 try:spec.loader.exec_module(m)
 finally:sys.path[:]=saved
 IMPORTS[relative]=h;return m
historical=load('goldbach_round14_historical_helpers','round13/shared.py')
for f,h in historical.IMPORTS.items():assert PROTECTED[f]==h;IMPORTS[f]=h
spec=spec_from_file_location('goldbach_round14_conservation',ROOT/'conservation.py')
conservation=module_from_spec(spec);spec.loader.exec_module(conservation)
N,ALPHA,A,Q,M,H=100000000,100,3163,999999,1000000,2
assert N==historical.N and (ALPHA-1)**4<N<=ALPHA**4
assert (A-1)**16<N**7<=A**16 and Q==(N-1)//ALPHA
assert (M-1)**4<N**3<=M**4 and (H-1)**64<N<=H**64
factor,divisors,mu=historical.factor,historical.divisors,historical.mu
prime,phi,Lambda,theta=historical.prime,historical.phi,historical.Lambda,historical.theta
prefix,kernels,sign_certificate=historical.prefix,historical.kernels,historical.sign_certificate
add,multiply=historical.vector_add,historical.multiply_vectors
log_vector,serialize=historical.log_vector,historical.serialize
def difference(left,right):
 out=dict(left);add(out,right,-1);return out
def source_profile(m):
 assert 0<m<=N-2
 n=N-m;D,W,R=kernels(m);C=difference(D,W)
 C={k:-mu(m)*v for k,v in C.items() if v}
 B=multiply(theta(n),C)
 raw=multiply(Lambda(n) if n>1 and gcd(n,N)==1 else {},C)
 U=prefix(m,A);low=prefix(m,ALPHA);annulus=difference(U,low)
 identity={k:mu(m)**2*v for k,v in difference({k:-v for k,v in Lambda(m).items()},U).items()}
 add(identity,W,mu(m));assert C==identity
 k1={k:-v for k,v in log_vector(m).items()}
 assert phi(1)==1 and mu(1)==1 and R>=1
 return {'m':m,'n':n,'m_factorization':factor(m),'n_factorization':factor(n),'unit':gcd(m,N)==gcd(n,N)==1,'bulk':M<=m<=N-2 and n>Q,'n_prime':prime(n),'mu_m':mu(m),'Lambda_m':serialize(Lambda(m)),'theta_n':serialize(theta(n)),'raw_Lambda_N_n':serialize(Lambda(n) if n>1 and gcd(n,N)==1 else {}),'short_prefix':serialize(U),'low_prefix':serialize(low),'annulus':serialize(annulus),'D':serialize(D),'W':serialize(W),'C':serialize(C),'B_prime_source':serialize(B),'B_raw_source':serialize(raw),'R':R,'k1_D':serialize(k1),'k1_W':serialize(k1),'k1_joint_D_minus_W':{},'front_strict':A*R<m<=A*(R+1) if R<Q else A*R<m,'original_cap_Q':Q},B,C,W
def select_q(c,p,start,stop,extra_parents=()):
 for q in range(max(start,p+1),stop+1):
  if not prime(q):continue
  if all(M<=c*t*q<=N-2 and prime(N-c*t*q) and N-c*t*q>Q and gcd(c*t*q,N)==1 for t in (p,*extra_parents)):
   return q
 raise AssertionError(('no candidate',c,p,start,stop,extra_parents))
def factors_json(n):return [[p,e] for p,e in factor(n)]
def add_many(items):
 out={}
 for item in items:add(out,item)
 return out
def assert_resolved(cert):assert cert['sign']!='UNRESOLVED',cert;return cert
def image_candidates(c,q,lower,upper):
 """Every ordered semiprime t in the stated complete integer window."""
 out=[]
 for t in range(lower,upper+1):
  fs=factor(t)
  if len(fs)!=2 or any(e!=1 for _,e in fs):continue
  r,s=fs[0][0],fs[1][0]
  if not (c<r<s<=A and c*r<=A and c*s<=A<t and c*t>A):continue
  m=c*t*q;n=N-m
  if not (gcd(c*r*s*q,N)==1 and M<=m<=N-2 and n>Q and prime(n)):continue
  out.append({'t':t,'r':r,'s':s,'m':m,'n':n})
 return out
