"""Replace inherited evaluation18 metadata before any round19 evaluation."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json, subprocess
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
out=C/'messages/round19_eval_metadata_update.json'
assert not out.exists()
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
contexts={};before={}
for node in ['13.11','14.4']:
    p=B/f'.arbor/sessions/parity/experiments/{node}/executor_prompt.md'
    data=p.read_bytes();text=data.decode('utf-8').replace('\r\n','\n')
    assert 'round18\\judge\\run_once.py' in text
    capture=C/f'messages/round19_prompt_{node}_BEFORE_EVAL_METADATA_UPDATE.md'
    if capture.exists():
        assert node=='13.11' and capture.read_bytes()==data, 'Existing failure-stage capture must match unchanged original'
        assert (C/'messages/round19_eval_metadata_FAILED01.json').exists()
    else:
        with capture.open('xb') as f:f.write(data)
    before[node]=dict(sha256=sha256(data).hexdigest(),capture=str(capture.relative_to(B)))
    contexts[node]=text.split('## Additional Context\n\n',1)[1].split('\n\n## Instructions',1)[0]
evaluation='"'+sys.executable+'" -B -X utf8 "'+str(B/'round19/judge/run_once.py')+'"'
dataset='ROUND19 selected13.11/14.4, exact1361 conservationPASS; FINAL1/2 fullread23bindings; freshformal3/4 writing and R6 new1001q/allconductor12m..24m sourcespreparing; math/Lean/Judge19 count0. FutureB_dev19 Judgeonly after frozenFINAL/rootgate, neverexecuteold18. Cumul30/507 unchanged; u>=10^24; Gamma_rank/mediumlong/capacity/fullledger unpaid; noWin.'
invoke('meta','--set','eval_cmd='+evaluation,'--set','dataset_info='+dataset)
after={}
for node in ['13.11','14.4']:
    context=contexts[node]+' Evaluation metadata now points to the future independent Judge19 launcher, not an existing authorized run. Executors MUST NOT execute B_dev or any old audit. Generic quick-check wording is subordinate to the explicit root numeric/Lean gates. Root Judge19 only after all required frozen FINALs and separate full source/launcher review.'
    invoke('prompt-executor','--node-id',node,'--workdir',str(B),'--additional-context',context)
    p=B/f'.arbor/sessions/parity/experiments/{node}/executor_prompt.md'
    data=p.read_bytes();assert 'round19\\judge\\run_once.py' in data.decode('utf-8')
    after[node]=dict(sha256=sha256(data).hexdigest(),bytes=len(data))
receipt=dict(status='EVAL19_METADATA_UPDATED_BEFORE_ANY_MATH_EXECUTION',observed_utc=datetime.now(timezone.utc).isoformat(),
 inherited_old_eval_display_detected=True,old_evaluation_executions=0,before=before,after=after,
    future_eval_cmd=evaluation,new_eval_executed=False,math_producers=0,Lean_invocations=0,victory=False,
    root_metadata_failures=1,root_metadata_failure='round19_eval_metadata_FAILED01.json; CRLF reader-only, no math/Lean/audit',
    limited_continuation_reuses_existing_unchanged_before_capture=True)
out.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=json.loads(p.read_bytes())
cp['last_progress']+=' Inheritedeval18 display detected in newprompts before anyexecution; oldpromptbytes preserved as BEFORE_METADATA captures. Treemeta updated futureJudge19 and bothprompts regenerated retaining fullcontexts/explicitgates, no auditexecuted.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['.arbor/sessions/parity/.coordinator/messages/round19_eval_metadata_update.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('Future evaluation19 metadata/prompts updated; olddisplay preserved, zero old/newevaluation execution; compiler gates unchanged')
