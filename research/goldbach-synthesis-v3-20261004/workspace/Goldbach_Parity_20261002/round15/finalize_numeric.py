"""Finalize role6 by reading frozen NEW gates only; no producer or kernel call."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from collections import Counter
import json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s

ROLE1_SHA='8fa44b44dbb2c14fd4a5319840e26a4dc8d113d2db3c6b57dec5569e790bbf5d'
ROLE2_SHA='afe8511ce670dce4580837f444041159055addde605675cde328ba49a15f1fe7'
BANKS={'incidence':('edb58961dca27429b934f74899928fc38aabdb45f16ebe679fea5c19e3e880f4','8c3506c4f51cca70d03b16ed5c82a13d40a01966e36770e24a51aea94e96aead'),
 'fusion':('5cee100cad1f5bb3d725687e073f5d165f389c3a99643b51c30f81a912a063ce','00886e77d4ca6f25236e30e95f0a955ad80e74e0b3eabab64c05cf17a251b85e'),
 'incidence_moment':('d9f0043c13a303d06224fb9c41c98110ed4d83d001a588514fb4067ca9d59d48','e5101cd3838ef1db6f7e7d1ae56c686f29016be2c3e97274837b593c7f0bd4a8')}

def hash_file(relative):return s.sha256((s.ROOT/relative).read_bytes()).hexdigest()
def load(relative):return json.loads((s.ROOT/relative).read_text(encoding='utf-8'))
def save(relative,value):(s.ROOT/relative).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n',encoding='utf-8')
def cert_checked(cert):
 lo,hi=Fraction(cert['lower']),Fraction(cert['upper']);assert lo<=hi
 assert (lo>0 if cert['sign']=='POSITIVE' else hi<0 if cert['sign']=='NEGATIVE' else lo==hi==0 if cert['sign']=='ZERO' else False)

def run():
 assert not (s.ROOT/'numeric_manifest.json').exists(),'Numeric FINAL already frozen'
 before=s.conservation.verify();reports={'agent1_weighted_incidence.md':ROLE1_SHA,'agent2_signed_cofactors.md':ROLE2_SHA}
 for relative,digest in reports.items():assert hash_file(relative)==digest
 bindings={};data={}
 for name,(producer_hash,gate_hash) in BANKS.items():
  marker=load('role6/'+name+'_canonical_success.json');replay=load('role6/'+name+'_replay_receipt.json')
  assert marker['attempt']==1 and marker['exit_code']==0
  assert hash_file(name+'_checks.py')==producer_hash==marker['producer_sha256']==replay['source_sha256']
  assert hash_file(name+'.json')==gate_hash==marker['output_sha256']==replay['output_sha256']
  assert hash_file('role6/'+name+'_attempt01_source.txt')==producer_hash
  assert hash_file('role6/'+name+'_attempt01.log')==marker['log_sha256']
  assert hash_file('role6/'+name+'_isolated_replay.log')==replay['log_sha256']
  assert (s.ROOT/(name+'.json')).read_bytes()==(s.ROOT/('isolated_'+name)/(name+'.json')).read_bytes()
  assert replay['bytes_identical'] and replay['all_fields_identical'] and replay['exit_code']==0
  data[name]=load(name+'.json')
  assert data[name]['victory'] is False and data[name]['global_D_N'] is False and data[name]['Lean_called'] is False
  bindings[name]={'producer_sha256':producer_hash,'gate_sha256':gate_hash,
   'canonical_success_receipt_sha256':hash_file('role6/'+name+'_canonical_success.json'),
   'replay_receipt_sha256':hash_file('role6/'+name+'_replay_receipt.json'),
   'canonical_attempts':1,'real_failed_attempts':0,'isolated_replays':1,'bytes_and_fields_identical':True}
 i,f,moment=data['incidence'],data['fusion'],data['incidence_moment']
 assert not list((s.ROOT/'role6').glob('*failure.json'))
 assert i['M_beta']==4201 and i['interval_complete']['integer_count']==695035 and i['interval_complete']['unit_count_J']==278014
 assert i['exact_prime_sieve']['unit_prime_first_axes']==60982 and len(i['theta_beta_sum'])==912
 assert len(i['raw_Lambda_N']['proper_power_records_complete'])==49 and sum(v['beta'] for v in i['raw_Lambda_N']['proper_power_records_complete'])==4
 assert len(i['physical_raccord_sample']['vertices'])==5
 cert_checked(i['Gamma_sign_certificate']);assert i['Gamma_sign_certificate']['sign']=='NEGATIVE'
 # Completeness proof by bounds and the verified historical sieve definition; no beta or theta bank rerun.
 bounds={'s_integer_minimum_from_47s_above_a':s.A//47+1,'s_upper':s.A//3,
  'intermediate_composites':{str(x):s.factor(x) for x in (68,69,70)},'smallest_possible_prime_s':71,
  'q_upper':i['written_cardinality_bound_finite_check']['B']//71,'sieving_prime_limit':10000,
  'PRIMES_count':len(s.historical.parity.PRIMES),'PRIMES_largest':s.historical.parity.PRIMES[-1],
  'historical_sieve_source_sha256':s.PROTECTED['numerical/parity_checks.py'],
  'source_definition':'PRIMES = prime_list(isqrt(N)); integer Eratosthenes sieve',
  'all_s_and_q_possible_are_in_the_verified_prime_list':True,'all_raw_prime_power_bases_also_in_the_prime_list':True,
  'incidence_producer_not_rerun_for_this_audit':True}
 assert bounds['s_integer_minimum_from_47s_above_a']==68 and bounds['s_upper']==1054 and bounds['q_upper']==9889
 assert not any(s.prime(x) for x in (68,69,70)) and s.prime(71)
 assert s.historical.parity.PRIMES[-1]==9973 and len(s.historical.parity.PRIMES)==1229
 assert 'PRIMES = prime_list(isqrt(N))' in (s.BASE/'numerical/parity_checks.py').read_text(encoding='utf-8')
 assert all(71<=v['s']<=1054 and v['q']<=9889 for v in i['structural_beta_without_n_prime_filter'])
 assert moment['input_gate_sha256']==BANKS['incidence'][1] and moment['input_producer_sha256']==BANKS['incidence'][0]
 assert set(moment['theta_second_moment_exact_vector'])=={n+','+n for n in i['theta_unit_sum']}
 assert Fraction(moment['strict_rational_intervals']['norm_squared_times_variance_minus_Gamma_squared'][0])>0
 assert moment['AP_front']['front_difference_exact']=='-35/23'
 assert len(f['q_window_complete']['q_primes_unit'])==21 and len(f['structural_parent_core_union'])==78
 assert len(f['structural_cofactor_labels_before_incidence'])==86 and f['candidate_vertex_count']==1680
 assert f['computed_D_W_profiles']==416 and f['actual_zero_vertices_with_literal_W']==1264
 assert f['parent_prime_vertex_count']==360 and f['target_prime_count']==7 and len(f['active_physical_edges'])==112
 assert len(f['unused_prime_parents_target_composite'])==248 and f['orphan_target_q']==[] and f['raw_Lambda_N']['proper_power_count']==0
 assert f['canonicality']['first_prime_label_count']==400 and f['canonicality']['maximum_structural_label_multiplicity']==3
 for row in f['per_q']:
  cert_checked(row['principal_sign_certificate']);cert_checked(row['entire_actual_sign_certificate']);cert_checked(row['F4_gap_sign_certificate'])
  assert row['F4_gap_sign_certificate']['sign']=='POSITIVE'
 pair_signs=Counter()
 for edge in f['active_physical_edges']:
  cert_checked(edge['principal_sign_certificate']);cert_checked(edge['actual_pair_sign_certificate'])
  assert edge['principal_sign_certificate']['sign']=='NEGATIVE' and edge['n_parent_minus_target']>0
  pair_signs[edge['actual_pair_sign_certificate']['sign']]+=1
 assert dict(pair_signs)=={'POSITIVE':41,'NEGATIVE':71}
 cert_checked(f['principal_entire_sign_certificate']);cert_checked(f['entire_actual_sign_certificate'])
 assert f['principal_entire_sign_certificate']['sign']==f['entire_actual_sign_certificate']['sign']=='NEGATIVE'
 closure={'status':'READ_ONLY_FINAL_GATE_BINDINGS_AND_SCOPE_VERIFIED','bindings':bindings,'complete_beta_prime_list_bounds':bounds,
  'reports_FINAL_sha256':reports,'all_existing_gates_and_replay_copies_read_only':True,
  'producer_or_kernel_called_during_closure':False,'source_or_gate_mutated':False,'real_failed_attempts':0,
  'two_new_candidate_banks_and_one_necessary_read_only_supplement':True,'conservation_before':before,
  'conservation_after':s.conservation.verify(),'noGlobal':True,'noLean':True,'score':0,'victory':False}
 save('role6/closure_receipt.json',closure)
 sample_rows='\n'.join('| '+str(v['profile']['m'])+' | '+str(v['profile']['n'])+' | '+str(v['structure']['s'])+' | '+str(v['structure']['q'])+' | '+str(v['profile']['R'])+' |' for v in i['physical_raccord_sample']['vertices'])
 text='''# Boucle15 — rôle6 numérique FINAL

Les deux contrats numériques nouveaux et leur unique rejeu séparé sont terminés. Le supplément ciblé L4/AP lit le gate d’incidence gelé ; il ne rejoue pas ce producteur et ne recalcule aucun kernel. Conservation exacte651 avant/après, aucun Lean, score0/victoryfalse. Le budget entier D_N n’est pas contrôlé.

## Conservation et exécution

Le registre protège exactement603 fichiers historiques plus48 finaux14. Les47 bindings du controller14, son propre SHA, l’inventaire réel des ajouts/suppressions et les originaux PDF/ZIP sont vérifiés. Les rounds de numéro≥15, caches, .arbor, .git et REPORT.md central sont exclus de l’inventaire historique. Baseline : `d43941b27a4325a841282d389476c9c6fa9af920138b9b0deebe1c484a4ff7f4`. Controller14 : `6795b8ed10872337ac8d0f7caf7ef428b8611b6f35376e575c22661ff68e30bf`. PDF `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24` et ZIP `32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd` intacts.

Écritures limitées au numérique15 ; rapports1/2 et sources anciennes intacts. Les helpers historiques ont leurs SHA vérifiés et sont chargés inertement pour leurs fonctions arithmétiques ; aucun ancien main/producteur/PASS, dépendance, compilation ou rendu n’est exécuté. N=100000000, alpha100,a3163,Q999999,M1000000 et les ceil/floor entiers sont réels. Les signes utilisent des intervalles rationnels de logarithmes symboliques, sans flottants ni UNRESOLVED. Les trois contrôles ont chacun un essai canonique exit0, snapshot source et log réel, puis exactement un rejeu isolé byte/field exact. Zéro véritable essai échoué ; aucune erreur n’est inventée.

## Incidence complète d141 et portée du raccord

Contrat FINAL1 lié : `agent1_weighted_incidence.md`, SHA `'''+ROLE1_SHA+'''`. I=[7093,702127] contient695035 entiers, U278014 unités, beta4201 incidences structurelles sans filtre de primalité de n. rho=4201/278014 diffère de4201/695035 ; le biais de normalisation est conservé exactement. Theta_U a60982 axes réellement premiers ; theta_beta en a912. Projection theta_beta=rho theta_U+Gamma, centrage/covariance et norme²=1150288413/278014 sont exacts. Gamma est strictement NEGATIVE : seul le faux remplacement exact beta→rho chi_U est réfuté, pas BV ou une estimation asymptotique.

La liste de premiers≤10000 suffit complètement, sans tronquer I : 47s>3163 impose s≥68 ;68/69/70 sont composites et71 premier, donc71≤s≤floor3163/3=1054. Puis q≤floor702127/71=9889<10000. Le helper protégé définit PRIMES par le crible entier jusqu’àisqrt(N)=10000 (1229 premiers, dernier9973). Les bases des properpowers et les diviseurs possibles des n≤N sont aussi dans cette liste. Cet audit par bornes lit les artefacts gelés ; il ne rerun pas incidence.

Le raw garde49 properpowers unitaires dans I, dont4 avec beta1 : 2549²,3677²,4523²,5441². La différence raw_beta−theta_beta est exactement la somme de leurs logp. Aucun filtre mu(n)² n’est utilisé. Le contrôle fini M_beta loga≤64B et loga≥8 est positif strict ; la constante est vacuante à ce N et ne minore aucune incidence première.

Le supplément nécessaire sérialise sum theta² et laisse T² factorisé. Il certifie variance>0 et le gap L4 M_beta(1−rho)variance−Gamma²>0 avec intervalles rationnels stricts. Son raccord AP garde n_lo1000093,n_hi98999887,X97999795,phi141=92 ; X=d(#I−1)+1. Remplacer X/phi(d) par d#I/phi(d) oublierait le front(1−d)/phi(d)=−35/23. La liste E_divN est vide car les seuls premiers de N sont2/5 hors intervalle. Le désaccord AP littéral est négatif au banc ; aucun BV/onset n’est certifié ou payé.

Les cinq kernels physiques nouveaux sont sélectionnés par b croissant parmi beta1, n premier, q≥4001 et m absent des anciens JSON numériques protégés. Un chevauchement aurait été retiré seulement de l’échantillon, jamais de beta/Gamma. Pour chaque sample, whole U_a=log3, mu(m)=+1, Lambda(m)=0, C=W−log3 et D/W source réels gardent Q, fronts stricts, unités, U_alpha+annulus et k1 conjoint.

| m | n=N−m premier | s | q | R strict |
|---:|---:|---:|---:|---:|
'''+sample_rows+'''

Leur capacité réelle−B est positive. Les907 autres images premières de beta gardent des erreurs W littérales non évaluées et non payées. Gamma est une covariance de première incidence, pas le résidu entier ni un calcul exhaustif des kernels. kappa=log3+S(N) reste symbolique ; S(cN) n’est pas substitué.

## Fusion complète de petits cœurs et union physique

Contrat FINAL2 lié : `agent2_signed_cofactors.md`, SHA `'''+ROLE2_SHA+'''`. Fenêtre complète déclarée de TOUS q premiers unitaires8000..8200 :21 q. Les six cofacteurs21,33,39,77,91,143 et tous p<3003/c premiers copremiers à cN donnent86 labels et78 cœurs parents distincts AVANT incidence. Avec E3003 et le contrôle e131, il y a1680 axes candidats. Tous leurs n, factorisations, theta/raw et gardes séparées sont conservés. Les416 profils couvrent chaque contrôle et chaque terme theta/raw non nul ; les1264 autres brackets theta/raw sont exactement nuls et leurs W restent littéraux. Il ne s’agit pas d’un échantillonnage des termes non nuls.

Chaque q est l’unique facteur>a, donc récupérable par factorisation ; e=m/q est canonique. E*q est compté une fois et les parents égaux sont fusionnés avant capacité. Le cœur231 a trois labels(21,11),(33,7),(77,3). La multiplicité maximale3 donnerait400 labels premiers au lieu de360 vertices premiers : le crédit par représentation est réfuté.

Les courts sont exactement Div(e). Pour les cœurs composites e≤a, U_a=0, D_a=0 et C=mu(eq)W ; c21/e2751 donne+W, c231/E3003 donne−W. Le contrôle common c1/e131 conserve courts{1,131},U_a=−log131 et C=log131+W. F1 s’applique seulement e≥2 : la branche physique e1/q, C_q=−logq−W, et le cofacteur bilatéral b1 restent hors sélection et dans le complément. F2–F5 portent sur E de rangpair≥4 et parentscomposites de rangimpair≥3. Tous les S(bN) du modèle bilatéral ont l’indice b=m/p réellement supprimé, notamment b=e si q est supprimé et b=cq si p l’est ; les poids logp/logm et les indices restent distincts, sans substitution commune.

Il y a360 parents premiers,7 cibles premières et112 arêtes physiques. Les248 parents premiers dont la cible est composite restent dans la somme entière. Aucune cible orpheline n’existe dans cette fenêtre : NO_COUNTEREXAMPLE_IN_WINDOW seulement. Delta=Σq[I_E logn_E−Σe I_e logn_e] est NEGATIVE strict ; le majorant F4 Delta(q)≤I_E logn_E 1_(Dq=0) a un gap positif sur chaque q. Cette vérification ne postule aucune disponibilité au source et ne paie pas F6.

Pour chaque arête, n_parent−n_target=(3003−e)q>0 et le raccord exact Bpair=−Wtarget(theta_target−theta_parent)+theta_parent(Wparent−Wtarget) est comparé aux vecteurs physiques. Les112 principaux sont négatifs mais les paires réelles ont71 signesNEGATIVE et41POSITIVE : l’identification systématique principal/réel est réfutée. La somme physique ENTIÈRE après union est néanmoins NEGATIVE. Son modèle F5 garde S(N)Delta+Σparents thetaδ−Σtargets thetaδ, sans estimation des erreurs. Le raw est calculé sur les1680 axes ; zéro properpower ici est une absence finie, pas une identité raw=theta globale.

Le test de rang donne3·7·11·13·17·3164=161525364>N : aucune image à six facteurs distincts unitaires avec q>a ne peut être sous N à ce banc. Une fusion inverse reste possible et aucun no-go asymptotique n’en suit. J2 a c≤9 et seuls c unitaires SF1/3/7 : aucun cofacteur composite J2 dans ce N original, sans changer a.

## Statut et obligations restantes

Deux nouveaux contrats arithmétiques ont été vérifiés et trois promotions finies de fusion plus le remplacement exact du masque sont falsifiés dans leur portée précise. Le supplément L4/AP comble une comparaison manquante par lecture seule. Les sources/gates/rejeux sont gelés ; `role6/closure_receipt.json` lie leur audit et la complétude par bornes. `numeric_manifest.json` lie les fichiers numériques, les deux FINAL conceptuels et le registre651. `role6_final_receipt.json` conserve les compteurs et limites.

Le seul ledger reste D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0). P5/K2 porte sur J2bulk ENTIER avant retraits ; U4/variation sont alternatives, sans deuxième NG54. c1/e1/b1,−S(N)N,S(bN),cofacteurs longs,J0/J1/J2 restants,célibataires/faces/nonbulk,fronts,terme couvert et onset BV supplémentaire restent présents. Ni la covariance agrégée ni l’incidence OR/F6 ni la réutilisation globale des parents ne sont estimées. N=10^8 est hors source u≥10^24. Aucun Lean ni nouvel axiome/théorème compilé ; les208 auxiliaires historiques ne sont pas recomptés. D_N≤N/(256u ell) reste ouvert : score0,victoryfalse,recherche active.
'''
 (s.ROOT/'agent6.md').write_text(text,encoding='utf-8')
 save('role6/conservation_after.json',s.conservation.verify())
 fixed=['conservation.py','previous_artifacts_sha256.json','conservation.json','shared.py','run_new.py','replay_new.py','finalize_numeric.py','agent6.md','role6/closure_receipt.json','role6/conservation_after.json']
 for name in BANKS:
  fixed.extend([name+'_checks.py',name+'.json','isolated_'+name+'/'+name+'.json'])
  fixed.extend(['role6/'+name+'_'+suffix for suffix in ['attempt01_source.txt','attempt01.log','canonical_success.json','isolated_replay.log','replay_receipt.json']])
 assert len(fixed)==len(set(fixed))
 assets={relative:hash_file(relative) for relative in sorted(fixed)}
 receipt={'status':'FINAL_NEW_ROUND15_NUMERICAL_ONLY_PARTIAL','scope':'two new concrete banks, one necessary read-only L4/AP supplement, exact conservation651',
  'reports_FINAL_sha256':reports,'bindings':bindings,'own_assets_sha256':assets,'own_asset_count_before_receipt':len(assets),
  'new_canonical_candidate_banks':2,'necessary_read_only_supplements':1,'new_canonical_attempts':3,'real_failed_attempts':0,
  'isolated_replays_total':3,'post_replay_reruns':0,'old_PASS_replays':0,'new_Lean_modules':0,'new_Lean_theorems':0,'new_Lean_definitions':0,
  'old_Lean_recompiles':0,'old_dependency_recompiles':0,'PDF_rerenders':0,'historical_auxiliaries_not_recounted':208,
  'complete_beta_prime_list_bounds':bounds,'unpaid_obligations':['weighted aggregate covariance Gamma','source OR incidence F6','global union parent reuse',
   'unsampled incidence W errors','all complementary ledger terms','effective BV onset and whole D_N target'],
  'conservation_before':before,'conservation_after':s.conservation.verify(),'N':s.N,'source_u_minimum':'10^24',
  'noGlobal':True,'noLean':True,'score':0,'victory':False,'numeric_manifest_relative':'numeric_manifest.json'}
 save('role6_final_receipt.json',receipt);assets['role6_final_receipt.json']=hash_file('role6_final_receipt.json')
 manifest={'status':'FINAL_FROZEN_NEW_ROUND15_NUMERIC_PARTIAL','sha256':assets,'files':len(assets),'reports_FINAL_sha256':reports,
  'probe_sha256':hash_file('PROBE_BLOCK.md'),'previous_protected_registry_sha256':hash_file('previous_artifacts_sha256.json'),'protected_previous_files':651,
  'controller14_sha256':'6795b8ed10872337ac8d0f7caf7ef428b8611b6f35376e575c22661ff68e30bf','new_bank_bindings':bindings,
  'counting':{'new_banks':2,'necessary_read_only_supplements':1,'canonical_attempts':3,'real_failed_attempts':0,'isolated_replays':3,
   'new_Lean_modules':0,'new_Lean_theorems':0,'new_Lean_definitions':0,'old_PASS_replays':0},
  'receipt_sha256':assets['role6_final_receipt.json'],'receipt_and_manifest_do_not_hash_themselves':True,
  'noGlobal':True,'noLean':True,'asymptotic':False,'payments':False,'score':0,'victory':False}
 save('numeric_manifest.json',manifest)
 print(json.dumps({'status':receipt['status'],'protected651':'PRESERVED','numeric_asset_bindings':len(assets),
  'agent6_sha256':hash_file('agent6.md'),'numeric_manifest_sha256':hash_file('numeric_manifest.json'),
  'role6_final_receipt_sha256':hash_file('role6_final_receipt.json'),'victory':False}))

if __name__=='__main__':run()
