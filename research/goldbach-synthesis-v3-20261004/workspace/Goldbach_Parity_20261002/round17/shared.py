"""Strict arithmetic for selected NEW round17 contracts; historical imports inert."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from importlib.util import spec_from_file_location,module_from_spec
from fractions import Fraction
from math import gcd,isqrt
import json
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parent
spec=spec_from_file_location('goldbach_round17_conservation',ROOT/'conservation.py')
conservation=module_from_spec(spec);spec.loader.exec_module(conservation)
INITIAL_CONSERVATION=conservation.verify()
PROTECTED=json.loads((ROOT/'previous_artifacts_sha256.json').read_text(encoding='utf-8'))['sha256']
IMPORTS={}
def load(name,relative):
 path=(BASE/relative).resolve();digest=sha256(path.read_bytes()).hexdigest();assert PROTECTED[relative]==digest
 spec=spec_from_file_location(name,path);module=module_from_spec(spec);sys.modules[name]=module;saved=list(sys.path)
 try:spec.loader.exec_module(module)
 finally:sys.path[:]=saved
 IMPORTS[relative]=digest;return module
historical=load('goldbach_round17_inert_historical_helpers','round13/shared.py')
for relative,digest in historical.IMPORTS.items():assert PROTECTED[relative]==digest;IMPORTS[relative]=digest
N,ALPHA,A,Q,M=100000000,100,3163,999999,1000000
assert N==historical.N and (ALPHA-1)**4<N<=ALPHA**4
assert (A-1)**16<N**7<=A**16 and Q==(N-1)//ALPHA and (M-1)**4<N**3<=M**4
factor,divisors,mu=historical.factor,historical.divisors,historical.mu
prime,phi,Lambda,theta=historical.prime,historical.phi,historical.Lambda,historical.theta
prefix,kernels,sign_certificate=historical.prefix,historical.kernels,historical.sign_certificate
add,multiply=historical.vector_add,historical.multiply_vectors
log_vector,serialize=historical.log_vector,historical.serialize
def difference(left,right):
 result=dict(left);add(result,right,-1);return result
def resolved(value):
 certificate=sign_certificate(value);assert certificate['sign']!='UNRESOLVED',certificate;return certificate
def active_kernel(m):
 """Compute a NEW vertex only; one primitive W with exact source checks."""
 n=N-m;assert 0<m<=N-2 and gcd(m,N)==gcd(n,N)==1
 D,W,R=kernels(m);U=prefix(m,A);low=prefix(m,ALPHA)
 C={key:-mu(m)*value for key,value in difference(D,W).items() if value}
 expected={key:mu(m)**2*value for key,value in difference({key:-value for key,value in Lambda(m).items()},U).items()}
 add(expected,W,mu(m));assert C==expected
 assert mu(1)==phi(1)==1 and R>=1 and A*R<m and (R==Q or m<=A*(R+1))
 record={'m':m,'n':n,'R':R,'original_Q':Q,'W_exact':serialize(W),
  'D_exact':serialize(D),'whole_U_a':serialize(U),'U_alpha':serialize(low),'annulus':serialize(difference(U,low)),
  'k1_D_and_W_exact':serialize({key:-value for key,value in log_vector(m).items()}),
  'k1_joint_cancels':True,'front_strict_verified':True,'physical_source_identity_verified':True}
 return record,C,W
