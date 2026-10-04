"""Select one fully read frozen concept19; coordinator metadata only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json, subprocess
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p):return json.loads(p.read_bytes())
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
obs=read(C/'messages/round19_ideations_root_observation.json')
assert obs['status']=='ROOT_FULL_READ_AND_BYTE_VERIFIED_FINAL1_FINAL2_19'
assert read(C/'messages/round19_conservation_root_observation.json')['status']=='ROOT_VERIFIED_ACTUAL_UNIQUE_CONSERVATION19'
role=int(sys.argv[1]); assert role in [1,2]
configs={
1:dict(node='13.11',parent='13',report='round19/agent1_weighted_aggregate.md',sha='d1cd64e27c46ad5aacfe2ee33c1b13681b77ae84e6d78c8585a3ef47acaf42bb',
 insight='Frozen FINAL1 fully read, all12 bindings verified after unique1361 conservation19. Fresh constraints read before selection. Genuine rank3 face excludes all actual canonical15 images; full unit-plus-rank price has negative written principal and AP level15/32 after paid large-unit losses. Gamma_rank and all other ledger families remain unpaid; independent P coprimeN and source normalization/onset guards explicit. NoWin or result presumed.',
 context='Read PROBE19, frozen FINAL1 and feedback18. Protect1361. Only NEW all-conductor bank N1e8, x24m, ALL candidates12m<j<=24m and ALL prime pairs c<r unitN/cr<=3163 authorized; physical beta no jprime filter. h39/P1771, all shareP cases and A0 fibres; d|N-j before quotient. R_source2/R_test17 kept distinct. Actualtheta/raw properpowers, full U0/Us/U/Usprime/Uprime, both unit/rank prices and Gamma_rank, all AP modules/representations IE/fronts and K6 normalized loss tested. Singular-series affine box acquired [2541/1536,11011/6144], no floats; no W/D producer required here. Formalization must derive rank3 exclusion on actual18 PhysicalWitness, remaining modulus, literal weighted price decomposition including empty branch, normalized variation, true small-unit level/multiplicity and actual IE/phi principal if possible. No K18 or Gamma-bound as free axiom, no proof by an assumed target. P coprimeN is guard not universal fact. Sourceu1e24/BVonset remain separate; Gamma_rank/capacity/ledger unpaid. Write sources now but NO Lean until canonical NEW numeric identity PASS inspected/root gate. Numeric source/launcher require full rootread and explicit first-run gate. Only freshnew modules; historical dependencies read-only.'),
2:dict(node='14.4',parent='14',report='round19/agent2_nonss.md',sha='20ca15ceba20b72459102b2da8429b7e6d72a7c4bd52dca7de7bc3a58a61cbc2',
 insight='Frozen FINAL2 and contract fully read, elevenbindings verified after unique1361 conservation19; fresh constraints read before selection. All-rank nonSS two-channel maximal-real-prime switch keeps moved primalities, repeated factors, signed CRT parameter, C<N and three conductor strata including long prices. Conditional rank3 short written H9 onset1e40 leaves sourcegap/mediumlong/allrank prices and capacity unpaid. NoWin or result presumed.',
 context='Read PROBE19, frozen FINAL2 and role2/test_contract.json, feedback18. Protect1361. Only NEW full1001integer q1600100..1601100 bank N1e8/allactualSFunitcore ranges authorized. Structural S minusSS tested before n_e prime selection. Extract actual maximal prime with multiplicities, no gcd(h,r)=1; canonical p0 gcdresources1 derived for allranks. D/P tag and equality/Donly, all selectors, signed y0/t, inverses, C<N notC<=sqrtN, three strata and literal prices. Move primality between parameter and variable accordingchannel; never allfourprime bydefinition. AUXshort B_hyp=floorN1/8=10 distinct originalB=N1/64; source shortempty guarded; independent B_test2048 onlyfinite harmonic uncut Omega1/2 products incl p^2 and cut bound. Real D/W/sourceBracket on active physicalvertices/m1 once, raw properpowers/candidate masks/k1/wholeUa preserved. Formalization derive actual largestPrimeExtraction, balanced resource coords/CRT inverse/fronts, actual sourceBracket sum reindex/strata and exact multiset harmonic diagonal; no arbitrary free domain/profiles promoted as source result. H9 remains conditional independent Mertens/G/root/cofactorbridge/sourcefront guards and onset1e40; no source1e24gap erased. Write sources now but NO Lean until canonical NEW numeric identity PASS inspected/rootgate. Numeric source/launcher require full rootread and explicit first-run gate. Only freshnew modules; historical imports read-only. No capacity credited by a demand estimate, all long/medium/rank>=4/T_A/Gamma/fullledger unpaid.')
}
cfg=configs[role]
receipt_path=C/f'messages/round19_role{role}_selection.json'
assert not receipt_path.exists(), 'No repeat of selected node'
assert cfg['node'] not in read(C/'idea_tree.json')['nodes']
data=(B/cfg['report']).read_bytes();assert sha256(data).hexdigest()==cfg['sha']
labels=['Mechanism:','Hypothesis:','Observable:','Conflicts:']
lines=[s for s in data.decode('utf-8').splitlines() if any(s.startswith(t) for t in labels)]
assert len(lines)==4 and all(s.startswith(t) for s,t in zip(lines,labels))
hyp='\n'.join(lines)
invoke('add','--parent-id',cfg['parent'],'--hypothesis',hyp)
assert read(C/'idea_tree.json')['nodes'][cfg['node']]['hypothesis']==hyp
invoke('update','--node-id',cfg['node'],'--status','running','--insight',cfg['insight'])
invoke('prompt-executor','--node-id',cfg['node'],'--workdir',str(B),'--additional-context',cfg['context'])
receipt=dict(role=role,node=cfg['node'],report=cfg['report'],report_sha256=cfg['sha'],
 fresh_constraints_full_read_before_selection=True,protected_artifacts=1361,
 numerical_contract_authorized=True,numerical_producer_waits_for_source_review=True,
 numerical_result_presumed=False,formal_source_writing_authorized=True,
 compiler_waits_for_new_canonical_numeric_PASS=True,victory=False,mathematical_execution_count=0)
receipt_path.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p)
cp.update(phase='ROUND19_SELECTED_FORMAL_WRITING_NEW_NUMERIC_PREPARATION',victory=False,objective_complete=False)
cp['current_nodes']=list(dict.fromkeys(cp.get('current_nodes',[])+[cfg['node']]))
cp['last_progress']+=' '+cfg['insight']+' New sourcewriting authorized; compilewaits canonicalnumericPASS; no mathematicalexecution.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+[cfg['report'],str(receipt_path.relative_to(B)).replace('\\','/'),f'.arbor/sessions/parity/experiments/{cfg["node"]}/executor_prompt.md']))
cp['current_protected_artifacts']=1361
cp['current_protected_registry']='round19/previous_artifacts_sha256.json'
cp['current_protected_registry_sha256']='8c0abf930ee8c47b64d335ed286af4566fc674b573216f82f12b05c4ec877150'
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(cfg['node']+' selected; new full contract authorized for preparation; writing only before canonicalnumericPASS; no math/Lean/audit invoked')
