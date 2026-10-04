"""Candidate discovery only; this is not a PASS bank or source-onset test."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s
before=s.conservation.verify()
q1=s.select_q(3,3323,3500,8000,(3167,))
q2=s.select_q(7,3359,3500,6000)
data={'status':'CANDIDATES_ONLY_NOT_GATE','N':s.N,'q1_shared_for_3323_3167':q1,'parents1':{str(p):{'c':3,'p':p,'q':q1,'p_factorization':s.factors_json(p),'q_factorization':s.factors_json(q1),'m':3*p*q1,'n':s.N-3*p*q1,'n_factorization':s.factors_json(s.N-3*p*q1)} for p in (3323,3167)},'q2_for_3359':q2,'parent2':{'c':7,'p':3359,'q':q2,'p_factorization':s.factors_json(3359),'q_factorization':s.factors_json(q2),'m':7*3359*q2,'n':s.N-7*3359*q2,'n_factorization':s.factors_json(s.N-7*3359*q2)},'imports_sha256':s.IMPORTS,'before':before,'after':s.conservation.verify(),'victory':False}
(s.ROOT/'candidate_proposal.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in data.items() if k not in ('before','after','imports_sha256')},indent=2))
