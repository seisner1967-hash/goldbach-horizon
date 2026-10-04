"""Observe four finished author attempts and update status; no compiler calls."""
import json,hashlib,re
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round19'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
ledger=json.loads((R/'role3/build_receipt.json').read_text(encoding='utf-8'))
rows=ledger['attempts'][:4]; assert len(rows)==4 and [x['exit_code'] for x in rows]==[1,1,0,1]
records=[]
for row in rows:
    for p,d in [('source_capture','source_capture_sha256'),('launcher_capture','launcher_capture_sha256'),
                ('authorization_capture','authorization_capture_sha256'),('log','log_sha256')]:
        assert sha(Path(row[p]))==row[d],p
    log=Path(row['log']).read_text(encoding='utf-8')
    records.append({'attempt':row['attempt'],'module':row['module'],'exit_code':row['exit_code'],
     'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],
     'started_at_utc':row['started_at_utc'],'finished_at_utc':row['finished_at_utc'],
     'actual_error_headers':re.findall(r'^.*?:\d+:\d+: error:.*$',log,re.M),
     'actual_warning_headers':re.findall(r'^.*?:\d+:\d+: warning:.*$',log,re.M),
     'failed_internal_sorryAx_in_log':'sorryAx' in log})
face=rows[2]; assert sha(Path(face['source']))==face['source_sha256']
assert sha(Path(face['olean']))==face['olean_sha256']==sha(Path(face['preserved_olean']))
out={'status':'ROOT_READ_ACTUAL_ROLE3_FACE_PASS_AFTER_TWO_FAILS_PRICE_FIRST_FAIL',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'actual_records':records,
 'face_FINAL_source_FULL_root_read':True,'author_PASS_observed':1,'author_FAIL_observed':3,
 'all_actual_logs_FULL_root_read':True,'no_analytic_parity_failure_inferred':True,
 'root_compiler_or_math_producer_invocations':0,'official_Judge_counts_modified':False,'victory':False}
p=C/'messages/round19_formal3_first_attempts_root.json'
with p.open('x',encoding='utf-8') as f: f.write(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
with (C/'messages/round19_failure_feedback_in_progress.md').open('a',encoding='utf-8') as f:
    f.write('\n\n## ROLE3 : premières tentatives réelles\n\n')
    for x in records:
        if x['exit_code']:
            f.write(f"Tentative {x['attempt']:02d} {x['module']} exit1, log SHA{x['log_sha256']} : ")
            f.write(' ; '.join(y.split('error:',1)[1].strip() for y in x['actual_error_headers'])+'\n\n')
    f.write('Face03 PASS corrige les réécritures dépendantes par congrArg₂ et prouve le carré-libre par les trois facteurs effectifs. Price04 demeure une erreur de branche vide et de cast 2≤j vers 1≤j ; aucun petit prix ou Γ favorable postulé.\n')
cp=json.loads((C/'checkpoint.json').read_text(encoding='utf-8'))
cp['phase']='ROUND19_FORMAL3_ACTUAL_COMPILES_WITH_PRESERVED_TECHNICAL_FAILURES_JUDGE_PREPARING'
cp['last_progress']+=' Role3 Face03 actualPASS aftertwo realtechnicalFAIL, Price04 firstactualFAIL emptyreference/cast. Allfour sources/captures/logs/exit read andbound; noactualparityfailure inferred. Judgeaudit8aab/lancef7e FULLrootreadstable, finalprepawaitsFINAL3. Allofficialcountsunchanged,noWin.'
cp['previous_goal_turn_evidence'].append(p.relative_to(B).as_posix())
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
reportp=B/'REPORT.md'; report=reportp.read_text(encoding='utf-8')
left,_,tail=report.partition('**Boucle19 en cours :**'); _,_,right=tail.partition('## Sources et notations')
assert left and right
paragraph='''**Boucle19 en cours :** les nodes13.11 et14.4 sont sélectionnés après conservation des1361 archives. Les deux tests neufs à N=10^8 ont chacun terminé leur unique exécution exit0, sans replay. Le banc non-SS conserve1001 q,22022 axes SF/unitaires,5120 familles et124 demandes ; le banc rang conserve les12 millions de candidats,514 conducteurs dont485 fibres vides et28136 images physiques. Les vrais prix unitaires/de rang et la séparation θ/raw/puissances propres restent mesurés, sans crédit global gratuit. FINAL4 est figé : cinq PASS auteurs,100 théorèmes auxiliaires,55 définitions,3 structures et160 impressions d'axiomes standard ; sept FAIL Lean techniques et un échec préalable du lanceur sont conservés. La seconde formalisation compile maintenant : Face03 PASS après deux erreurs de réécriture/décision ; Price04 est en réparation technique. Le Juge19 préparé reconstruira les onze nouveaux modules après gel FINAL3 ; le cumul officiel reste30 modules507 conclusions. K14 effectif, conversion sourceK18/BV, Γ_rank et le ledger complet restent ouverts. L'onset écrit de la couche triprime courte10^40 ne remplace pas le seuil source10^24. Aucune victoire. [Candidat rang](round19/agent1_weighted_aggregate.md), [candidat non-SS](round19/agent2_nonss.md), [test non-SS figé](round19/agent6_nonss.md), [test rang figé](round19/agent6_rank.md), [formalisation non-SS](round19/agent4_formalisation.md).

'''
reportp.write_text(left+paragraph+'## Sources et notations'+right,encoding='utf-8')
print(json.dumps({'status':out['status'],'actual_author_records':len(records),'official_counts_changed':False,'victory':False}))
