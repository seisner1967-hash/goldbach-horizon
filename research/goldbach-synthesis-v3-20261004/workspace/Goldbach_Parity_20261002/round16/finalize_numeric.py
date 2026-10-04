"""FINAL role6 by read-only audit of frozen round16 gates and copies."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
import json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s

REPORTS={'agent1_bilinear_covariance.md':'f60827e9e72e73cde93512448bd6acc289807d43180b844040326456a5e2d754',
 'agent2_or_incidence.md':'f6f12c39afc445ce82482850c34482fa2450b9df1df7dbeef2089574b308128b'}
BANKS={'typei':('e59caddb2a123374a70e85686cdbe5d00677317b48d9f8c6fc2b7bbd934f9a6e','a1443ee83b346fc6a3cf330a09bf07a05a4e4a5d00230ed418aebeb8a9b65b1c'),
 'capacity':('abedd2b6494ebb684fcaeef2ca0d869003f2ee17271dbde1cd70f52820367128','7da550e67c38774e580dd6300b1c78a9d19cb4f49e3063483a6727d7ecd2a166')}
PREFLIGHT_NOTE='numeric_contract_round16_launched=false and mathematical_identity_round16_certified=false inside conservation records are static flags of the conservation preflight only; they do not track global execution. Actual two launches are proven by canonical receipts, logs and separate replay receipts. No stored PASS or conservation receipt was rewritten.'

def h(relative):return s.sha256((s.ROOT/relative).read_bytes()).hexdigest()
def load(relative):return json.loads((s.ROOT/relative).read_text(encoding='utf-8'))
def save(relative,data):(s.ROOT/relative).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
def check_cert(cert):
 lo,hi=Fraction(cert['lower']),Fraction(cert['upper']);assert lo<=hi
 assert (lo>0 if cert['sign']=='POSITIVE' else hi<0 if cert['sign']=='NEGATIVE' else lo==hi==0 if cert['sign']=='ZERO' else False)
def all_certs(value):
 if isinstance(value,dict):
  if {'sign','lower','upper'}<=value.keys():check_cert(value);return 1
  return sum(all_certs(v) for v in value.values())
 if isinstance(value,list):return sum(all_certs(v) for v in value)
 return 0

def run():
 assert not (s.ROOT/'numeric_manifest.json').exists(),'FINAL numeric already frozen'
 before=s.conservation.verify()
 for relative,digest in REPORTS.items():assert h(relative)==digest
 bindings={};data={};cert_count=0
 for name,(src_hash,gate_hash) in BANKS.items():
  marker=load('role6/'+name+'_canonical_success.json');replay=load('role6/'+name+'_replay_receipt.json')
  assert marker['attempt']==1 and marker['exit_code']==replay['exit_code']==0
  assert h(name+'_checks.py')==src_hash==marker['producer_sha256']==replay['source_sha256']
  assert h(name+'.json')==gate_hash==marker['output_sha256']==replay['output_sha256']
  assert h('role6/'+name+'_attempt01_source.txt')==src_hash
  assert h('role6/'+name+'_attempt01.log')==marker['log_sha256']
  assert h('role6/'+name+'_isolated_replay.log')==replay['log_sha256']
  assert (s.ROOT/(name+'.json')).read_bytes()==(s.ROOT/('isolated_'+name)/(name+'.json')).read_bytes()
  assert replay['bytes_identical'] and replay['all_fields_identical']
  data[name]=load(name+'.json');cert_count+=all_certs(data[name])
  assert not data[name]['victory'] and not data[name]['global_D_N'] and not data[name]['Lean_called']
  bindings[name]={'producer_sha256':src_hash,'gate_sha256':gate_hash,
   'canonical_receipt_sha256':h('role6/'+name+'_canonical_success.json'),'replay_receipt_sha256':h('role6/'+name+'_replay_receipt.json'),
   'canonical_attempts':1,'real_failed_attempts':0,'isolated_replays':1,'all_bytes_and_fields_identical':True}
 assert not list((s.ROOT/'role6').glob('*failure.json'))
 t,c=data['typei'],data['capacity']
 assert t['A_beta']==216 and t['A_classes_mod3']==[0,106,110]
 assert t['unit_counts']['J']==51948 and t['unit_counts']['J_classes_mod3']==[17316]*3
 assert t['rho']=='2/481' and t['rho_star']=='3/481'
 assert t['TypeI3_exact']['uniform_drift_Af_minus_rho_Jf']=='38' and t['TypeI3_exact']['corrected_drift_Af_minus_rho_star_Jf']=='2'
 assert t['theta_prime_counts_classes']==[5067,5079,0] and len(t['theta_beta'])==28
 assert t['raw_Lambda_N']['proper_power_count_classes']==[9,0,0]
 assert len(t['raw_Lambda_N']['proper_power_records_complete'])==9 and not any(v['beta'] for v in t['raw_Lambda_N']['proper_power_records_complete'])
 assert all(t['sign_certificates'][key]['sign']=='NEGATIVE' for key in ['Gamma','Gamma_star','L3'])
 assert t['complete_prime_bounds']['q_upper']==3989 and t['complete_prime_bounds']['candidate_factor_prime_limit']==4472
 assert t['AP_front_and_principal']['L3_principal']=='-4999957/28860'
 assert c['candidate_vertices']==612 and c['computed_D_W_profiles']==128 and c['exact_zero_literal_W_vertices']==484
 assert len(c['q_window_complete']['all_q_tested'])==201 and len(c['q_window_complete']['q_primes_unit'])==18
 assert [v['q'] for v in c['q_window_complete']['all_q_tested']]==list(range(1000100,1000301))
 assert len(c['core_window_complete']['squarefree_unit_cores'])==34 and c['core_window_complete']['ranks_counts']=={'0':1,'1':23,'2':10,'3':0,'4':0}
 first1=[v for v in c['physical_candidates'] if v['e']==1 and v['n_prime']]
 first3=[v for v in c['physical_candidates'] if v['e']==3 and v['n_prime']]
 assert len(first1)==0 and len(first3)==3
 assert sum(v['n_prime'] for v in c['physical_candidates'])==95
 assert c['whole_actual_Rother_resources_once']=={} and c['raw_Lambda_N']['proper_power_count']==0
 assert c['whole_actual_deficit_R13_sign_certificate']['sign']==c['whole_actual_entire_sign_certificate']['sign']=='POSITIVE'
 assert all(v['sign_certificate']['sign']=='POSITIVE' for v in c['whole_principal_deficit']['endpoints'].values())
 assert all(row['actual_entire_sign_certificate']['sign']=='POSITIVE' for row in c['per_q'])
 assert all(v['C_plus_1over288_sign_certificate']['sign']=='NEGATIVE' for v in c['finite_A9_comparisons_prime_e3'])
 assert len(c['ERROR_FALSIFIER'][2]['witnesses'])==3
 falsifiers=t['ERROR_FALSIFIER']+c['ERROR_FALSIFIER']
 assert sum(v['status'].startswith('REFUTED_') for v in falsifiers)==4
 assert sum(v['status']=='NO_COUNTEREXAMPLE_IN_WINDOW' for v in falsifiers)==1
 closure={'status':'READ_ONLY_FINAL_NEW16_GATES_AND_SCOPE_VERIFIED','bindings':bindings,'reports_FINAL_sha256':REPORTS,
  'certificates_positions_verified':cert_count,'falsifiers':falsifiers,'old701_preserved':True,
  'preflight_static_flag_scope_clarification':PREFLIGHT_NOTE,'producer_or_kernel_executed_by_closure':False,
  'input_gate_or_source_mutated':False,'conservation_before':before,'conservation_after':s.conservation.verify(),
  'real_failed_numeric_attempts':0,'post_replay_runs':0,'score':0,'victory':False}
 save('role6/closure_receipt.json',closure)
 report='''# Boucle16 — rôle6 numérique FINAL

Les deux nouvelles banques sélectionnées et leurs uniques copies isolées sont terminées, exit0 et octets/champs identiques. Quatre falsifications locales et un NO_COUNTEREXAMPLE_IN_WINDOW sont conservés. Les701 artefacts anciens sont intacts. Aucun Lean n’est appelé par ce rôle ; score0/victoryfalse, résidu entier non contrôlé.

## Conservation et compteurs réels

Protection exacte701=651+50 finaux15, avec les49 bindings du controller15, ses35 bindings numériques et ses trois copies intégrales. L’inventaire réel vérifie mutations/ajouts/suppressions ; rounds de numéro≥16, caches, .arbor, .git et REPORT.md vivant sont exclus. Registry SHA `5939d791139dbb3f9b26e5d1f372bbdf98d1927f9aaf2c5e9c22aa0a4e35d043`. Controller15 `7b2522fbeec0c17965b9bfba4df418552f0e31b2b4881c91edff00b79a81869f`. PDF `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24` et ZIP `32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd` originaux intacts.

Les helpers historiques sont SHA-vérifiés et chargés inertement ; aucun ancien main/PASS, Lean, dépendance ou rendu n’est exécuté. N=100000000, alpha100,a3163,Q999999,M1000000, ceil/floor entiers, vrais premiers/unités et logarithmes symboliques rationnels sont gardés. Les propres bornes de complétude de chaque support sont démontrées ; le cap9889 du d141 ancien n’est pas transporté. Deux essais canoniques, chacun essai1 exit0, sources snapshots/logs réels, puis deux rejeux isolés seulement. Zéro véritable échec numérique, zéro essai Lean de ce rôle, aucune erreur fabriquée. Les compteurs des formaliseurs3/4 sont indépendants et appartiennent au controller/Juge, pas à ce reçu numérique.

**Clarification des champs de conservation.** Les flags `numeric_contract_round16_launched=false` et `mathematical_identity_round16_certified=false` dans les objets conservation_before/after sont statiques : ils décrivent uniquement ce que le préflight de conservation lance ou certifie. Ils ne suivent pas l’exécution globale. Les deux launches effectifs sont prouvés par leurs reçus canoniques, commandes, journaux et reçus de copie isolée. Aucun PASS, préflight ou reçu stocké n’a été réécrit pour changer ces champs.

## Banque1 — candidat entier d77 et correction modulo3

FINAL1 `agent1_bilinear_covariance.md`, SHA `'''+REPORTS['agent1_bilinear_covariance.md']+'''`. Le support neuf c7/r11/d77, x20000000, j∈(10000000,20000000] donne I_b=[1038962,1168831],129870 entiers examinés, J51948 et J0=J1=J2=17316. Les fronts sont n_lo10000013,n_hi19999926,X9999914 ; X−77#I=−76,phi77=60,phi231=120. Tous points sont unitaires dans le masque approprié, bulk, j>Q. β est structurel sans filtre jpremier :216 incidences, classes[0,106,110]. Les caps donnent s≥288, premier admissible293, s≤451 et q≤3989 ; les bases des diviseurs/powers de j≤2·10^7 sont couvertes jusqu’à4472. Les listes sont complètes pour ces propres bornes.

rho=2/481 et rho*=3/481. Le vrai drift TypeI3 A2−rhoJ2 vaut38, celui corrigé A2−rho*J2 vaut2, différence exacte36. Le normalisé x/A vaut95000000/27 ; aucune borne source x/8 n’est appliquée à N=10^8. La promotion « référence uniforme exactement centrée TypeI3 » est réfutée par ce drift non nul. La réduction locale ne prouve pas TypeI entier ou TypeII.

Theta a les comptes[5067,5079,0], soit10146 axes premiers, dont28β. T2=0 vient de j divisible3 et j>3 ; cette annulation n’a pas été imposée au raw. Les neuf properpowers réellement présents sont tous en classe0 et horsβ, conservés avec bases/exposants/logp ; raw−theta est exact, sans mu(j)^2. Gamma uniforme, Gamma* corrigée et L3 sont strictement NEGATIVE ; Gamma=Gamma*+L3 est vérifié sur les vrais vecteurs. Les normes sont103464/481 et103248/481. Le raw garde sa propre décomposition, même si une classe interdite pour theta contenait des powers.

Le principal local AP garde coefficient rho*−2rho=−1/481 et L3_principal=−4999957/28860, exactement−1/4 du principal uniforme4999957/7215. Les deux endpoints AP de231, leurs erreurs et E_divN restent littéraux ; E_divN est vide ici car2/5 hors fenêtre. Aucun théorème AP/source n’est invoqué au banc. Aucun D/W n’est recomputé : Gamma*/TypeII, l’agrégat pondéré, les vrais parents et les erreurs W restent non estimés.

Source `typei_checks.py` SHA `'''+BANKS['typei'][0]+'''`, gate `typei.json` SHA `'''+BANKS['typei'][1]+'''`. Rejeu unique `role6/typei_replay_receipt.json` SHA `'''+h('role6/typei_replay_receipt.json')+'''`, copies intégrales identiques.

## Banque2 — demande entière et ressources physiques une fois

FINAL2 `agent2_or_incidence.md`, SHA `'''+REPORTS['agent2_or_incidence.md']+'''`. Tous201 entiers q1000100..1000300 sont factorisés/testés, donnant18 q réellement premiers unitaires. Cette énumération n’est pas limitée à une liste q≤10000 ; les diviseurs≤sqrtN=10000 suffisent à leurs factorisations et à celles de n≤N. Pour chaque q, TOUS e SF/unit1..98 sont retenus :34 cœurs, avec e1,23 cœurs premiers et10 rang2. Rangs≥3 vides au cap fini car minimum231>98. Tous612 vertices candidats ont leurs facteurs/unités/bulk/Q/theta/raw/courts entiers ;128 vrais profils D/W couvrent chaque axe actif plus tous les contrôles e1/e3. Les484 autres brackets sont exactement nuls, avec kernels littéraux non estimés. Le raw est testé intégralement ; aucun properpower dans cette fenêtre seulement.

Les vrais coefficients restent C_q=−logq−W pour e1 ; C_eq=loge+W pour eprime ; C_eq=−W pour rang2. Λ(e) est conservé sur chaque cœur premier. Whole U_a, ses diviseurs≤alpha, U_alpha+annulus, Q original, R/front strict, unités et k1 conjoint sont présents dans les profils physiques. Les modèles bilatéraux utilisent S(bN) au cofacteur réellement supprimé b=m/l, avec poids logl/logm et b1 conservés ; aucun S(bN) long n’est remplacé par S(N).

Le principal source demeure affine en S_N∈[847/512,11011/6144], enclosure issue des inputs C2 acquis et des facteurs N2/5. P1=theta(S_N−logq), P_eprime=theta(loge−S_N), P_rang2=thetaS_N. La demande principale somme tous e≠1,3 ; la ressource−P1−P3 est comptée une fois. Le déficit est leur différence EXACTE ΣTOUS P_e, positif strict aux deux endpoints de S_N. Cela ne fixe aucun W réel.

Le ledger réel mesure B_e=thetaC_e sans signe imposé : D+=Σmax(B_e,0), R13+=Σe1,3 max(−B_e,0), Rother+=Σautres max(−B_e,0). D+−R13+ est le déficit après les seules ressources sélectionnées ; D+−R13+−Rother+=ΣB_e est la somme entière. La comparaison orientée selon le source est aussi conservée signée, sans prétendre ses deux termes positifs. Chaque m a son unique q>a et e=m/q, et chaque ressource physique compte une fois.

Il y a95 premières incidences : e1 en a zéro et e3 en a trois, aux q1000117,1000133,1000159. Les92 autres vertices premiers sont des demandes. Rother+=0 ici ; D+−R13+ et la somme entière sont POSITIVE, sur chacun des18 q et globalement. La capacité du premier absent n’offre donc pas gratuitement une couverture de ce corps fini. Les trois C3+1/288 sont NEGATIVE mesurés : la promotion du signe source au fini a statut NO_COUNTEREXAMPLE_IN_WINDOW, sans preuve universelle ni application de U4 au banc.

Trois falsifiers banque2 ont de vrais témoins : capacité gratuite pour toute la famille (déficit principal positif sur toute l’enclosure), suppression du terme Λ(e) (différence theta loge strictement positive), et reuse d’un même e3 pour chaque autre cœur positif (trois témoins de capacité artificiellement multipliée). Aucune première incidence ou arête n’est inventée. Les comparaisons raw restent physiques séparées, sans U4 sur leurs n properpowers.

Source `capacity_checks.py` SHA `'''+BANKS['capacity'][0]+'''`, gate `capacity.json` SHA `'''+BANKS['capacity'][1]+'''`. Rejeu unique `role6/capacity_replay_receipt.json` SHA `'''+h('role6/capacity_replay_receipt.json')+'''`, copies intégrales identiques.

## Raccord et limites

Le seul ledger reste D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0). P5/K2 porte sur J2bulk ENTIER avant retraits ; U4/variation sont alternatives, sans deuxième NG54. c1/e1/b1,−S(N)N,S(bN),cofacteurs longs,J0/J1/J2 restants,célibataires/faces/nonbulk,fronts,terme couvert et onset BV effectif supplémentaire restent présents. Source54 garde−sqrt(u/60) et sa borne volontairement plus faible−sqrtu/60. Sourceu≥10^24 est distinct de N=10^8.

Les quatre falsifications concernent leurs promotions finies précises. La covariance corrigée, TypeII, la disponibilité du premier absent, F6 et les capacités globales après union restent sans estimation suffisante. Aucun no-go source n’est inféré. Les banques sont gelées et ne seront plus relancées ; `numeric_manifest.json`, `role6_final_receipt.json` et l’audit lecture seule `role6/closure_receipt.json` lient sources/gates/logs/copies et les deux FINAL conceptuels. Le certificat global D_N≤N/(256u ell) reste ouvert. Recherche active, score0,victoryfalse.
'''
 (s.ROOT/'agent6.md').write_text(report,encoding='utf-8')
 save('role6/conservation_after.json',s.conservation.verify())
 fixed=['conservation.py','previous_artifacts_sha256.json','conservation.json','shared.py','run_new.py','replay_new.py','finalize_numeric.py','agent6.md',
  'role6/conservation_attempt01_source.txt','role6/conservation_attempt01.log','role6/conservation_final_receipt.json','role6/closure_receipt.json','role6/conservation_after.json']
 for name in BANKS:
  fixed.extend([name+'_checks.py',name+'.json','isolated_'+name+'/'+name+'.json'])
  fixed.extend(['role6/'+name+'_'+suffix for suffix in ['attempt01_source.txt','attempt01.log','canonical_success.json','isolated_replay.log','replay_receipt.json']])
 assert len(fixed)==len(set(fixed));assets={relative:h(relative) for relative in sorted(fixed)}
 receipt={'status':'FINAL_ROUND16_ROLE6_NUMERIC_PARTIAL','own_assets_sha256':assets,'own_asset_count_before_receipt':len(assets),'reports_FINAL_sha256':REPORTS,
  'bindings':bindings,'new_candidate_banks':2,'canonical_attempts':2,'real_failed_numeric_attempts':0,'isolated_replays':2,'post_replay_runs':0,
  'local_falsifiers':4,'NO_COUNTEREXAMPLE_IN_WINDOW_promotions':1,'rational_certificate_positions':cert_count,
  'old_PASS_replays':0,'old_Lean_or_dependency_recompiles':0,'old_PDF_rerenders':0,
  'Lean_called_by_this_numeric_role':False,'new_Lean_modules_by_this_role':0,'new_Lean_theorems_by_this_role':0,
  'other_formal_roles_counted_separately_by_controller':True,'historical_208_auxiliaries_not_recounted':True,
  'preflight_static_flag_scope_clarification':PREFLIGHT_NOTE,'protected_previous_artifacts':701,
  'conservation_before':before,'conservation_after':s.conservation.verify(),'N':s.N,'source_u_minimum':'10^24',
  'unpaid':['Gamma_star/TypeII and true parent comparison','least-prime first-incidence availability','F6/source OR/global union reuse','all W errors and remaining ledger','whole D_N target'],
  'noGlobal':True,'numeric_noLean':True,'payments':False,'asymptotic':False,'score':0,'victory':False}
 save('role6_final_receipt.json',receipt);assets['role6_final_receipt.json']=h('role6_final_receipt.json')
 manifest={'status':'FINAL_FROZEN_NEW_ROUND16_NUMERIC_PARTIAL','sha256':assets,'files':len(assets),'reports_FINAL_sha256':REPORTS,
  'probe_sha256':h('PROBE_BLOCK.md'),'protected_registry_sha256':h('previous_artifacts_sha256.json'),'protected_previous_files':701,
  'controller15_sha256':'7b2522fbeec0c17965b9bfba4df418552f0e31b2b4881c91edff00b79a81869f','new_bank_bindings':bindings,
  'preflight_static_flag_scope_clarification':PREFLIGHT_NOTE,'new_banks':2,'new_canonical_attempts':2,'real_failed_attempts':0,'isolated_replays':2,
  'numeric_role_Lean_called':False,'other_formal_roles_counted_separately':True,'receipt_sha256':assets['role6_final_receipt.json'],
  'noGlobal':True,'payments':False,'asymptotic':False,'score':0,'victory':False}
 save('numeric_manifest.json',manifest)
 print(json.dumps({'status':receipt['status'],'protected701':'PRESERVED','numeric_bindings':len(assets),'certificate_positions':cert_count,
  'agent6_sha256':h('agent6.md'),'numeric_manifest_sha256':h('numeric_manifest.json'),'role6_final_receipt_sha256':h('role6_final_receipt.json'),
  'finalizer_source_sha256':h('finalize_numeric.py'),'closure_sha256':h('role6/closure_receipt.json'),'victory':False}))

if __name__=='__main__':run()
