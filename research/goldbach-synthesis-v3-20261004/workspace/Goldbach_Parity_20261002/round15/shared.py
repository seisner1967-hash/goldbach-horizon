"""Strict arithmetic helpers for concrete NEW round15 contracts only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from importlib.util import spec_from_file_location,module_from_spec
from fractions import Fraction
from math import gcd,isqrt
import json
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parent
spec=spec_from_file_location('goldbach_round15_conservation',ROOT/'conservation.py')
conservation=module_from_spec(spec);spec.loader.exec_module(conservation)
INITIAL_CONSERVATION=conservation.verify()
PROTECTED=json.loads((ROOT/'previous_artifacts_sha256.json').read_text(encoding='utf-8'))['sha256']
IMPORTS={}
def load(name,relative):
 p=(BASE/relative).resolve();h=sha256(p.read_bytes()).hexdigest();assert PROTECTED[relative]==h
 spec=spec_from_file_location(name,p);m=module_from_spec(spec);sys.modules[name]=m;saved=list(sys.path)
 try:spec.loader.exec_module(m)
 finally:sys.path[:]=saved
 IMPORTS[relative]=h;return m
historical=load('goldbach_round15_inert_historical_helpers','round13/shared.py')
for f,h in historical.IMPORTS.items():assert PROTECTED[f]==h;IMPORTS[f]=h
N,ALPHA,A,Q,M=100000000,100,3163,999999,1000000
assert N==historical.N and (ALPHA-1)**4<N<=ALPHA**4
assert (A-1)**16<N**7<=A**16 and Q==(N-1)//ALPHA and (M-1)**4<N**3<=M**4
factor,divisors,mu=historical.factor,historical.divisors,historical.mu
prime,phi,Lambda,theta=historical.prime,historical.phi,historical.Lambda,historical.theta
prefix,kernels,sign_certificate=historical.prefix,historical.kernels,historical.sign_certificate
add,multiply=historical.vector_add,historical.multiply_vectors
log_vector,serialize=historical.log_vector,historical.serialize
def difference(left,right):
 out=dict(left);add(out,right,-1);return out
def add_many(items):
 out={}
 for v in items:add(out,v)
 return out
def resolved(value):
 cert=sign_certificate(value);assert cert['sign']!='UNRESOLVED',cert;return cert
def source_profile(m):
 assert 0<m<=N-2
 n=N-m;assert gcd(n,N)==1,'The physical D equality requires the source unit guard'
 D,W,R=kernels(m);C=difference(D,W);C={k:-mu(m)*v for k,v in C.items() if v}
 U=prefix(m,A);low=prefix(m,ALPHA);annulus=difference(U,low)
 identity={k:mu(m)**2*v for k,v in difference({k:-v for k,v in Lambda(m).items()},U).items()}
 add(identity,W,mu(m));assert C==identity
 B=multiply(theta(n),C);rawLambda=Lambda(n) if n>1 and gcd(n,N)==1 else {};raw=multiply(rawLambda,C)
 k1={k:-v for k,v in log_vector(m).items()}
 assert mu(1)==phi(1)==1 and R>=1
 return {'m':m,'n':n,'m_factorization':factor(m),'n_factorization':factor(n),'unit':gcd(m,N)==gcd(n,N)==1,'bulk':M<=m<=N-2 and n>Q,'n_prime':prime(n),'mu_m':mu(m),'Lambda_m':serialize(Lambda(m)),'theta_n':serialize(theta(n)),'raw_Lambda_N_n':serialize(rawLambda),'short_prefix':serialize(U),'low_prefix':serialize(low),'annulus':serialize(annulus),'D':serialize(D),'W':serialize(W),'C':serialize(C),'B_prime_source':serialize(B),'B_raw_source':serialize(raw),'R':R,'k1_D':serialize(k1),'k1_W':serialize(k1) if gcd(n*N,1)==1 else {},'k1_joint_D_minus_W':{},'front_strict':A*R<m<=A*(R+1) if R<Q else A*R<m,'original_cap_Q':Q},B,C,W
