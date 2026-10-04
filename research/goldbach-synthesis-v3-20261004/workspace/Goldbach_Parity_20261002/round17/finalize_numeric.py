"""Read-only closure of selected NEW17 gates/copies; no producer/kernel/sign rerun."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
import json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as s
REPORTS={'agent1_calibrated_typeii.md':'446c2d8fe21c86b05fbaf0e2864e7129da1b964287f31ff4287c0a19251103a9',
 'role1/unit_mask_addendum.md':'51735b4ecd379b8b58066d24b952ff779347af5ae8a32ecd4b4ac303b7636cac',
 'agent2_capacity_incidence.md':'2c3b2dfadb507925b0fdc92a69b5174353f8f93ba2fc188175dadf05b38ad8d7'}
BANKS={'rough':('5fe6120ab216dd3320798574e9043db071141802a00c2f300278c3ac5929a698','e4dd2c8e12cbfd34c90208ffb90745472bc8e2c3a3f777681a9d52735fcadfbb',1),
 'typeii':('7ec02d82d4610547456078fec5b099b8b09865aea1d9ded2041b3f90965ed1b2','b3af5c0357201e2a710a2a6c761f34ec1d63d2c87fbbd459a54154f925e6ad5e',2)}
SCOPE_NOTE='Conservation flags describe only READ_ONLY_CONSERVATION_VERIFICATION. numeric_contract_launched_by_this_verification=false does not deny the two selected launches, proven by canonical/replay receipts. mathematical_identity_certified_by_conservation=false is not a claim about the new finite gate identities. Frozen preflight/PASS artifacts were not rewritten.'
def h(relative):return s.sha256((s.ROOT/relative).read_bytes()).hexdigest()
def load(relative):return json.loads((s.ROOT/relative).read_text(encoding='utf-8'))
def save(relative,data):(s.ROOT/relative).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
def interval_positions(value):
 if isinstance(value,dict):
  if {'sign','lower','upper'}<=value.keys():
   lo,hi=Fraction(value['lower']),Fraction(value['upper']);assert lo<=hi
   assert lo>0 if value['sign']=='POSITIVE' else hi<0 if value['sign']=='NEGATIVE' else lo==hi==0 if value['sign']=='ZERO' else False
   return 1
  return sum(interval_positions(v) for v in value.values())
 if isinstance(value,list):return sum(interval_positions(v) for v in value)
 return 0
def run():
 assert not (s.ROOT/'numeric_manifest.json').exists(),'FINAL numeric already frozen'
 before=s.conservation.verify()
 for relative,digest in REPORTS.items():assert h(relative)==digest
 data={};bindings={};positions=0
 for name,(source,gate,attempt) in BANKS.items():
  marker=load('role6/'+name+'_canonical_success.json');replay=load('role6/'+name+'_replay_receipt.json')
  assert marker['attempt']==attempt and marker['exit_code']==replay['exit_code']==0
  assert h(name+'_checks.py')==source==marker['producer_sha256']==replay['source_sha256']
  assert h(name+'.json')==gate==marker['output_sha256']==replay['output_sha256']
  assert h('role6/'+name+f'_attempt{attempt:02d}_source.txt')==source
  assert h('role6/'+name+f'_attempt{attempt:02d}.log')==marker['log_sha256']
  assert h('role6/'+name+'_isolated_replay.log')==replay['log_sha256']
  canonical=(s.ROOT/(name+'.json')).read_bytes();isolated=(s.ROOT/('isolated_'+name)/(name+'.json')).read_bytes()
  assert canonical==isolated and json.loads(canonical)==json.loads(isolated)
  assert replay['bytes_identical'] and replay['all_fields_identical']
  data[name]=json.loads(canonical);positions+=interval_positions(data[name])
  assert not data[name]['victory'] and not data[name]['global_D_N'] and not data[name]['Lean_called']
  bindings[name]={'source_sha256':source,'gate_sha256':gate,'canonical_attempts':attempt,'real_failed_attempts':attempt-1,
   'canonical_receipt_sha256':h('role6/'+name+'_canonical_success.json'),'replay_receipt_sha256':h('role6/'+name+'_replay_receipt.json'),
   'isolated_replays':1,'bytes_and_fields_identical':True}
 failures=list((s.ROOT/'role6').glob('*_failure.json'));assert [p.name for p in failures]==['typeii_attempt01_failure.json']
 failure=load('role6/typeii_attempt01_failure.json');assert failure['attempt']==1 and failure['exit_code']==1
 assert h('role6/typeii_attempt01_source.txt')==failure['producer_sha256']=='a58db7311d56c51bcbe0591d1f3c22f3cb21fc13c39a9ffd4e8eeb6e74ebdc1f'
 assert h('role6/typeii_attempt01.log')==failure['log_sha256']=='da05cdd2526935204ce54d3c3f8b1c4d37d62eaaf170cf0839f5d1cdcca4d649'
 r,t=data['rough'],data['typeii']
 active_counts={cell:sum(len(parts[cell]) for parts in r['partition_active_demands'].values()) for cell in ('A','R','S')}
 saturations=[row['e'] for row in r['finite_selberg_by_core'] if row['status']=='LOCAL_SATURATION_ROUGH_CELL_EMPTY']
 rootcollisions=r['ERROR_FALSIFIER'][1]['counterexamples']
 rational_mode={k:v['z_functional']['exact_rational'] for k,v in t['functionals_exact']['II']['by_mask'].items()}
 gamma_signs={k:v['z_functional']['sign_certificate']['sign'] for k,v in t['functionals_exact']['theta']['by_mask'].items()}
 price_signs={weight:{price:{k:v['sign_certificate']['sign'] for k,v in values.items()} for price,values in t['prices_by_weight'][weight].items() if isinstance(values,dict)} for weight in ('theta','II','II_raw')}
 summary={'rough':{'q_primes':len(r['q_window_complete']['prime_unit_q']),'cores':len(r['core_window_complete']['squarefree_unit_cores']),
  'candidates':r['candidate_count'],'kernels':r['kernel_count'],'active_A_R_S':active_counts,'saturating_e':saturations,
  'first_resource_count_e1':sum(q['I1'] for q in r['q_resources_and_small_factor_cells']),
  'first_resource_count_e3':sum(q['I3'] for q in r['q_resources_and_small_factor_cells']),
  'positive_deficit_sign':r['whole_positive_demand_minus_resources']['sign_certificate']['sign'],
  'entire_signed_sign':r['whole_entire_signed_theta']['sign_certificate']['sign'],
  'falsifier_statuses':[f['status'] for f in r['ERROR_FALSIFIER']]},
  'typeii':{'b_count':t['progression_complete']['integer_count'],'beta':t['beta_structural']['A'],
   'theta_count':t['progression_complete']['theta_candidate_count'],'properpowers':t['raw_Lambda_N']['unit_proper_power_count'],
   'J':{k:v['J'] for k,v in t['unit_conventions'].items()},'TypeII_exact':rational_mode,'Gamma_signs':gamma_signs,
   'price_signs':price_signs,'multiplicity_counts':t['v_complete']['multiplicity_counts']}}
 closure={'status':'READ_ONLY_FROZEN_NEW17_NUMERIC_CLOSURE','bindings':bindings,'reports_FINAL_sha256':REPORTS,'summary':summary,
  'interval_certificate_positions_verified_from_stored_bounds':positions,'real_failed_attempt':failure,
  'producer_or_kernel_or_sign_recomputation_by_closure':False,'frozen_gate_source_mutation':False,
  'conservation_scope_clarification':SCOPE_NOTE,'conservation_before':before,'conservation_after':s.conservation.verify(),
  'post_replay_runs':0,'score':0,'victory':False}
 save('role6/closure_receipt.json',closure)
 report=f'''# Boucle 17 — rôle 6 numérique FINAL

Les deux nouvelles banques sélectionnées et leurs uniques copies isolées sont terminées, avec octets et champs identiques. Exactement 799 artefacts anciens sont préservés. Un véritable échec Type II est conservé avant correction ; aucune banque PASS n’est relancée. Ce reçu porte sur deux contrats finis, sans estimation de whole D_N, sans Lean par ce rôle, score 0 et victoire fausse.

## Conservation et exécutions réelles

Registry SHA `1c21af8d00924e126bf541c03f13277fa699c6f8e9d3a9edbbda337b9cead420` : 701 anciens + 98 finaux 16, dont les 97 bindings du controller16 et ce controller lui-même. Controller16 SHA `10d9f68fc649d965aa5eecac96fecf5fd20f705527d42f52b855662acec02332`. L’inventaire réel détecte ajouts, suppressions et mutations ; exclusions : rounds de numéro ≥17, caches conventionnels, .arbor, .git et REPORT.md central vivant. Les 13 paires de logs/snapshots Lean16, les neuf véritables échecs, copies fraîches du Juge, sources, oleans et manifests sont inclus. Originaux PDF `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24` et ZIP `32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd` intacts.

Les helpers historiques sont vérifiés par SHA et importés inertement ; aucun ancien producteur/main/PASS, Lean, dépendance ou rendu n’est exécuté. Rough scanne seulement les valeurs m des JSON protégés, en dédupliquant les copies, puis vérifie que ses 47 kernels nouveaux ne coïncident avec aucun des 7011 m lus. Aucun ancien W n’est recalculé. Type II ne calcule aucun D/W.

Préflight : un essai exit0. Rough : un essai canonique exit0, puis un seul replay isolé. Type II : essai1 exit1 réel, essai2 exit0, puis un seul replay isolé. L’échec venait du radical de hN envoyé au helper historique qui exige n≤N ; snapshot `a58db731…`, log `da05cdd2…` et failure.json sont conservés. Le source final réunit les facteurs de h,77,N, chacun dans le domaine, sans changer le contrat. Sources, snapshots, logs, gates et reçus sont liés au manifeste. Aucun échec factice, aucun essai Lean par ce rôle.

Les flags `numeric_contract_launched_by_this_verification=false` et `mathematical_identity_certified_by_conservation=false` décrivent uniquement la vérification de conservation. Ils ne décrivent pas l’exécution globale des banques ; les commandes, journaux et reçus canoniques attestent ces launches. Aucun préflight ou PASS figé n’a été réécrit pour changer les flags.

## Quatre formes : partition réelle et carré rationnel

FINAL2 `agent2_capacity_incidence.md` SHA `{REPORTS['agent2_capacity_incidence.md']}`. Tous les 201 entiers q∈[1200100,1200300] sont factorisés/testés ; 9 q premiers unitaires. Tous les e SF/unitaires sous cap82 sont examinés : 28 cœurs, e1 et e3 inclus, 252 candidats physiques distincts. Les rangs≥3 sont vides seulement à ce cap, car le minimum unitaire 231>82. Chaque n=N−eq conserve facteurs, θ première et raw Λ_N distincts, unités/bulk/Q originaux, µ, Λ(e), whole U_a et diviseurs courts complets. Les 47 D/W couvrent tous axes actifs et les 18 contrôles e1/e3 ; les 205 axes exactement nuls gardent W littéral non estimé. Properpowers : zéro dans cette fenêtre seulement.

C_q=−logq−W ; C_eq=Λ(e)−µ(e)W pour e≥2. Les primitifs W exacts sont catalogués une seule fois ; C et les sommes θ/raw ont des recettes exactes par références, avec certificats de signe. U_alpha, annulus, original Q, R=min(Q,(m−1)//a), front ak<m et k1 conjoint sont présents. Les modèles S(bN) conservent les vrais b=m/p et logp/logm ; ils ne sont pas remplacés par S(N). Les principaux θ restent affines sur l’enclosure acquise 847/512≤S_N≤11011/6144, distincts des vrais kernels.

La partition des 29 demandes premières e>3 est A=11, R=0, S=18. A signifie une ressource première e1/e3 présente ; R exige les deux absences ET les deux complémentaires100-rugueux ; S garde les absences avec un petit facteur. Le témoin S est le plus petit facteur de n1 s’il existe≤100, sinon celui de n3, avec priorité et face n1 rugueuse explicites. Pour e≡j modℓ, l’axe θ(n_e) est réellement nul ; son éventuel raw reste séparé. Les ressources premières sont e1={summary['rough']['first_resource_count_e1']}, e3={summary['rough']['first_resource_count_e3']}, comptées une fois par q.

T_A et T_S, définis par max(Bθ,0), sont POSITIVE ; T_R=0. Ressources uniques POSITIVE, déficit de la demande positive après leur consommation unique POSITIVE ; la somme signée entière θ est aussi POSITIVE. Les poids négatifs, les zéros et les ressources ne sont pas reconstruits depuis des labels. A/S restent non payés au source ; R vide fini ne démontre aucune borne source.

Pour chaque e>3, toutes racines des quatre formes F_e(q)=q(N−eq)(N−q)(N−3q) sont comptées modulo chaque premier≤100. Dix cœurs ont saturation modulo3 et R vide : {', '.join(map(str,saturations))}. Aucun G à dénominateur nul n’est formé. Pour les 16 autres, tous h/G/λ SF d≤100 sont rationnels, λ1=1 et |λ|≤1 ; diagonalisation principale exactement1/G. CRT est calculé sur chaque lcm, avec racines locales et compte exact des 201 entiers, reste |r|≤ρ. Les carrés point par point majorent le masque rough, et leur somme vaut exactement201/G+reste signé. Le majorant avec reste absolu et son CRT+1 peuvent être très faibles : leurs valeurs exactes restent publiées, aucune valeur petite n’est postulée.

Trois falsifications nouvelles sont locales : absence des deux incidences n’implique pas roughness (demande réelle en S), ρℓ=4 partout omet les collisions/saturations, et appliquer C6 à toute la demande finie en omettant A/S échoue. Pour cette dernière seule promotion, logN>18 et log18>2 sont encadrés rationnellement, donc N/(8192logNloglogN)<N/294912 ; la demande mesurée dépasse ce majorant. C6/C7 et U4 source ne sont jamais appliqués à N=10^8, et leur onset u≥10^24 n’est pas réfuté.

Source `rough_checks.py` SHA `{BANKS['rough'][0]}` ; gate `rough.json` SHA `{BANKS['rough'][1]}` ; replay SHA `{h('role6/rough_replay_receipt.json')}`. Source et gate PASS restent immuables.

## Mode Type II réel et deux conventions unitaires

FINAL1 SHA `{REPORTS['agent1_calibrated_typeii.md']}`, addendum SHA `{REPORTS['role1/unit_mask_addendum.md']}`. Entière progression b∈[974026,1136363], 162338 entiers ; j∈[12500049,24999998], X=12499950, X−77#I=−76. Les colonnes compactes donnent TOUTES les factorisations b/j, les bits exacts β/θ et des six masques, et leur indexation complète. Bornes propres : s293..451, q≤3878, bases de factorisation j≤25 millions jusqu’à5000 ; aucun ancien qcap9889 n’est transporté.

β reste structurel, sans primalité de j : 181 images canoniques, chacune une fois. Les endpoints physiques q sont max(a,11s,11,ceil(bmin/s)−1)<q≤floor(bmax/s), distincts des endpoints source. Les tableaux AP comptent les vrais q premiers de ces intervalles et les douze classes unitaires modulo13v, avec retraits d’unités, caractères et résidus exacts.

V10 donne v17 et19 après tests exacts ; χ13(v)χ13(w)=χ13(j) et normes≤1 sont vérifiées sur chaque couple entier j=vw. Les recettes complètes de deux progressions en b gardent les w et la multiplicité j divisible323. Cette multiplicité analytique ne devient pas une capacité physique. Les candidats premiers >v n’ont aucun tel facteur ; les 12460 axes θ et 8 properpowers unitaires sont tous examinés. Le raw conserve log(base), exposants, prix propres et aucune µ(j)^2.

J^0_1/3/39=64936/43291/39961 ; J^77_1/3/39=50599/33732/31136, toutes densités A/J exactes. U39 retire b0 mod13, tandis que la primalité candidate exclut b4 ; les deux classes sont distinctes. Les valeurs du mode II h1/3/39 sont respectivement ^0 : −259563/64936, −173345/43291, −93236/39961 ; ^77 : −202939/50599, −11425/2811, −18647/7784. Ce sont des résultats mesurés, aucun signe n’avait été imposé.

Les prix E77_h, L3 et L13 sont séparés pour θ, II et II_raw. U1/U2, les deux télescopages et les normalisations x/A sont exacts. L13θ est NEGATIVE dans les deux conventions ; tous les autres signes et valeurs restent au catalogue. Les références AP θ conservent classes admissibles, vraie longueur X et résidus exacts ; les principales B2/B6 ou U4 Type II conservent hV/h0, les fronts et erreurs AP/unités exacts. BV n’est pas appliqué au banc. L13II n’est pas identifié au prix θ, et aucun nouveau crédit de capacité n’est tiré des calibrations.

Source `typeii_checks.py` SHA `{BANKS['typeii'][0]}` ; gate `typeii.json` SHA `{BANKS['typeii'][1]}` ; replay SHA `{h('role6/typeii_replay_receipt.json')}`. Un mode Type II est mesuré ; tous coefficients Type II, Γ39 et comparaison pondérée entière restent non estimés. D/W de ce raccord restent littéraux hors de ce mode.

## Portée du FINAL

Le seul ledger reste D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0). P5/K2 porte sur J2bulk ENTIER avant retraits ; U4/variation restent alternatives, sans deuxième NG54. α/Q originaux, whole U_a, raw sans µ(n)^2, c1/e1/b1,−S(N)N,S(bN), cofacteurs longs, faces/célibataires/nonbulk et autres couches restent présents. Source u≥10^24 et onset BV supplémentaire inconnu restent distincts du banc fini. Les formaliseurs et le Juge ont leurs compteurs séparés ; ce rôle produit zéro module/théorème Lean et ne recompte aucune dépendance historique.

Clôture en lecture seule : {positions} positions de certificats sont contrôlées à partir de leurs bornes stockées, sans recomputations de signes ni de kernels. Ce compteur n’est pas un nombre de théorèmes. Les deux banques/replays sont gelés ; manifeste et reçu lient les sources/helpers, les trois essais canoniques dont l’échec réel, et toutes leurs sorties. Whole D_N≤N/(256u logu) demeure ouvert. Score0/victoryfalse ; recherche globale active.
'''
 (s.ROOT/'agent6.md').write_text(report,encoding='utf-8');save('role6/conservation_after.json',s.conservation.verify())
 fixed=['conservation.py','previous_artifacts_sha256.json','conservation.json','shared.py','run_new.py','replay_new.py','finalize_numeric.py','agent6.md',
  'role6/conservation_attempt01_source.txt','role6/conservation_attempt01.log','role6/conservation_final_receipt.json','role6/closure_receipt.json','role6/conservation_after.json']
 for name,(_,_,attempt) in BANKS.items():
  fixed.extend([name+'_checks.py',name+'.json','isolated_'+name+'/'+name+'.json'])
  fixed.extend(['role6/'+name+'_'+suffix for suffix in ['canonical_success.json','isolated_replay.log','replay_receipt.json']])
  for number in range(1,attempt+1):fixed.extend([f'role6/{name}_attempt{number:02d}_source.txt',f'role6/{name}_attempt{number:02d}.log'])
 fixed.append('role6/typeii_attempt01_failure.json');assert len(fixed)==len(set(fixed))
 assets={relative:h(relative) for relative in sorted(fixed)}
 receipt={'status':'FINAL_ROUND17_ROLE6_NUMERIC_PARTIAL','own_assets_sha256':assets,'own_assets_before_receipt':len(assets),
  'reports_FINAL_sha256':REPORTS,'new_bank_bindings':bindings,'summary':summary,'protected_previous_artifacts':799,
  'new_banks':2,'canonical_attempts':3,'real_failed_numeric_attempts':1,'isolated_replays':2,'post_replay_runs':0,
  'falsifiers_new_local':3,'interval_certificate_positions':positions,'new_Lean_modules_by_this_role':0,'new_Lean_theorems_by_this_role':0,
  'formal_roles_and_historical_dependencies_counted_separately':True,'old_producer_PASS_Lean_dependency_render_W_runs':0,
  'conservation_scope_clarification':SCOPE_NOTE,'conservation_before':before,'conservation_after':s.conservation.verify(),
  'whole_D_N_uncontrolled':True,'noGlobal':True,'numeric_noLean':True,'payments':False,'asymptotic':False,'score':0,'victory':False}
 save('role6_final_receipt.json',receipt);assets['role6_final_receipt.json']=h('role6_final_receipt.json')
 manifest={'status':'FINAL_FROZEN_NEW_ROUND17_NUMERIC_PARTIAL','sha256':assets,'files':len(assets),'reports_FINAL_sha256':REPORTS,
  'probe_sha256':h('PROBE_BLOCK.md'),'protected_registry_sha256':h('previous_artifacts_sha256.json'),'protected_previous_files':799,
  'controller16_sha256':'10d9f68fc649d965aa5eecac96fecf5fd20f705527d42f52b855662acec02332','new_bank_bindings':bindings,
  'receipt_sha256':assets['role6_final_receipt.json'],'conservation_scope_clarification':SCOPE_NOTE,
  'new_banks':2,'canonical_attempts':3,'real_failed_attempts':1,'isolated_replays':2,'numeric_Lean_called':False,
  'formal_roles_counted_separately':True,'whole_D_N_uncontrolled':True,'noGlobal':True,'payments':False,'asymptotic':False,'score':0,'victory':False}
 save('numeric_manifest.json',manifest)
 print(json.dumps({'status':receipt['status'],'protected799':'PRESERVED','numeric_bindings':len(assets),'certificate_positions':positions,
  'agent6_sha256':h('agent6.md'),'manifest_sha256':h('numeric_manifest.json'),'receipt_sha256':h('role6_final_receipt.json'),
  'finalizer_source_sha256':h('finalize_numeric.py'),'closure_sha256':h('role6/closure_receipt.json'),'summary':summary,'victory':False}))
if __name__=='__main__':run()
