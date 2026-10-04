"""Read-only FINAL C4 annexe; initial FINAL6 and all PASS gates untouched."""
import sys
sys.dont_write_bytecode=True
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
from pathlib import Path
from fractions import Fraction
import json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as c
SOURCE='613a38487ff8016c30e4f93fcdd5c3dd3a4fe54b10924f66ee200e246274617b'
GATE='d78c0cdc941cc2950e43168ed53809108aa55bffe0db31672905c2e5d2f7a5a6'
def load(name):return json.loads((c.ROOT/name).read_text(encoding='utf-8'))
def save(name,data):(c.ROOT/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
def h(name):return c.digest(c.ROOT/name)
def cert_positions(value):
 if isinstance(value,dict):
  if {'sign','lower','upper'}<=value.keys():
   lo,hi=Fraction(value['lower']),Fraction(value['upper']);assert lo<=hi
   assert lo>0 if value['sign']=='POSITIVE' else hi<0 if value['sign']=='NEGATIVE' else lo==hi==0 if value['sign']=='ZERO' else False
   return 1
  return sum(cert_positions(v) for v in value.values())
 if isinstance(value,list):return sum(cert_positions(v) for v in value)
 return 0
def run():
 assert not (c.ROOT/'manifest.json').exists(),'C4 FINAL already frozen'
 before=c.verify();marker=load('canonical_success.json');replay=load('replay_receipt.json');data=load('moment.json')
 assert marker['attempt']==1 and marker['exit_code']==replay['exit_code']==0 and not list(c.ROOT.glob('*_failure.json'))
 assert SOURCE==h('moment_checks.py')==h('attempt01_source.txt')==marker['source_sha256']==replay['source_sha256']
 assert GATE==h('moment.json')==h('isolated/moment.json')==marker['output_sha256']==replay['output_sha256']
 assert (c.ROOT/'moment.json').read_bytes()==(c.ROOT/'isolated/moment.json').read_bytes()
 assert data==load('isolated/moment.json') and replay['bytes_identical'] and replay['all_fields_identical']
 assert h('attempt01.log')==marker['log_sha256'] and h('isolated_replay.log')==replay['log_sha256']
 count=cert_positions(data);assert count==data['new_interval_certificate_positions']==64 and data['initial390_positions_not_recounted']
 assert not data['victory'] and data['no_W_kernel_or_old_bank_recomputed']
 summary={'cores':data['core_count'],'new_positions':count,'initial_positions_separate':390,
  'condition_true':data['true_condition_cores'],'condition_false':data['false_condition_cores'],
  'Markov_signs':{str(row['e']):row['markov_no_division_certificate']['sign'] for row in data['rows']},
  'observed_G_P_half_Z':{str(row['e']):row['observed_G_P_ge_half_Z'] for row in data['rows']},
  'all_queues':[{'e':row['e'],'products':[item['natural_product'] for item in row['all16_subsets'] if item['cell'].startswith('TAIL')],
   'Tail':row['Tail_weight_exact'],'G_P':row['G_P_exact'],'Z':row['Z_sum_and_product_exact']} for row in data['rows']]}
 closure={'status':'READ_ONLY_FINAL_C4_STORED_BOUNDS_AND_COPIES_VERIFIED','summary':summary,
  'source_sha256':SOURCE,'gate_sha256':GATE,'new_positions':count,'initial390_not_recounted':True,
  'producer_kernel_or_sign_recomputed_by_closure':False,'canonical_attempts':1,'real_failed_attempts':0,
  'isolated_replays':1,'post_replay_runs':0,'conservation_before':before,'conservation_after':c.verify(),
  'whole_D_N_uncontrolled':True,'score':0,'victory':False}
 save('closure_receipt.json',closure);save('conservation_after.json',c.verify())
 report=f'''# Boucle 17 — annexe numérique C4 FINAL

Cette annexe nouvelle est distincte du FINAL6 initial et de ses 33 bindings gelés. Elle vérifie le moment et la queue des seize cœurs finis, sans relancer rough/TypeII, leurs replays, aucun W/kernel/Lean/PDF ni aucune estimation source. Les799 archives, le manifeste initial `c6e1efe0ef1e4c2448bb9d53eb6df1635b29eb9a077723620ce62d4f45a6b1e4`, ses33 bindings et les FINAL conceptuels sont vérifiés par hashes et demeurent intacts.

## Domaine et nouvelles identités exactes

Input unique : rough.json gelé SHA `{c.ROUGH_SHA}`, seize cœurs non saturés avec rho/g/h effectifs et G_actual(100). N=10^8, P={{2,3,5,7}}, z=100. Ce choix fini ne prétend pas être le primorial au w=z^(1/32) du source C4. Tous les16 sous-ensembles par cœur sont enumerés exactement : poids W_s=produit h(p), produit naturel, logarithme formel et tête/queue. Fractions et encadrements de logarithmes sont rationnels, aucun flottant.

Les identités Z=Σ_s W_s=Π_p(1+h(p)) et, pour chaque p, coeff_logp(Σ_s W_s log(prod s))=Z*g(p) sont exactes. La queue prod(s)>100 est intégrale : produits105 et210, pour chaque cœur. G_P+Tail=Z et G_P≤G_actual(100) sont vérifiés par inclusion des quatorze produits de tête dans le support carré libre existant et égalité de chaque poids. Aucun noyau harmonique n’intervient dans ce calcul.

## Conditions mesurées et Markov sans division

M=Σ_p g(p)logp. La condition M≤log100/2 est TRUE_FINITE pour {', '.join(map(str,data['true_condition_cores']))}, et FALSE_FINITE pour {', '.join(map(str,data['false_condition_cores']))}. Les dix `CONDITION_FALSE_FINITE` restent des résultats ; la condition n’a jamais été imposée pour obtenir un PASS.

Pour les six premières lignes : Z=105/8, G_P=99/8, Tail=3/4. Pour les dix autres : Z=35/2, G_P=97/6, Tail=4/3. Les seize marges de Markov `(G_P−Z)log100+Z*M` sont strictement POSITIVE, et chaque queue a log(prod s)−log100 strictement positif. La borne générale G_P≥Z*(1−M/log100) est ainsi gardée dans sa forme sans division. La conclusion observée G_P≥Z/2 vaut ici même lorsque la condition suffisante de demi-moment est fausse : cette condition fausse ne réfute donc pas la conclusion observée, et ne permet pas de la déduire gratuitement dans un autre domaine.

L’annexe a64 nouvelles positions de certificats :32 queues,16 conditions et16 Markov. Elles sont comptées séparément des390 positions initiales ; ce ne sont pas64 théorèmes. C4/C6/U4/BV source ne sont pas appliqués au N fini, et le seuil source u≥10^24 ne reçoit aucun verdict à partir de ce tableau.

## Exécutions, gel et hashes

Un essai canonique réel exit0, snapshot pré-exécution et log conservés ; aucun échec réel ou fabriqué. Un seul replay isolé réel exit0, identique en octets et en champs. La clôture lit seulement les preuves stockées, contrôle leurs bornes et hashes, sans producer/sign/kernel rerun. Source et gate PASS sont immuables.

Source `role6_c4/moment_checks.py` SHA `{SOURCE}` ; snapshot identique. Gate `role6_c4/moment.json` et copie `role6_c4/isolated/moment.json` SHA `{GATE}`. Log canonique `{h('attempt01.log')}` ; reçu de copie `{h('replay_receipt.json')}`. Helpers, scripts de capture, logs, outputs et reçu final distinct sont liés dans `role6_c4/manifest.json`.

Portée : nouvelle annexe moment/queue/Markov seulement, aucune nouvelle disponibilité, capacité globale, estimation de Gamma ou whole D_N. Ledger entier et erreurs hors support demeurent non payés. Zéro Lean par ce rôle, aucun recompte des dépendances historiques, score0/victoryfalse. Le FINAL6 initial n’est ni corrigé ni rouvert ; la recherche globale continue.
'''
 reportpath=c.ROUND/'agent6_c4.md';reportpath.write_text(report,encoding='utf-8')
 names=['shared.py','moment_checks.py','run_once.py','replay_once.py','finalize.py','attempt01_source.txt','attempt01.log',
  'canonical_success.json','moment.json','isolated/moment.json','isolated_replay.log','replay_receipt.json','closure_receipt.json','conservation_after.json']
 assets={name:h(name) for name in sorted(names)}
 receipt={'status':'FINAL_ROUND17_ROLE6_C4_DISTINCT_FINITE_ANNEXE','own_assets_sha256':assets,'report_sha256':c.digest(reportpath),
  'input_rough_sha256':c.ROUGH_SHA,'initial_numeric_manifest_sha256':c.MANIFEST_SHA,'summary':summary,
  'canonical_attempts':1,'real_failed_attempts':0,'isolated_replays':1,'post_replay_runs':0,
  'new_positions':count,'initial390_not_recounted':True,'old799_and_initial_FINAL6_unchanged':True,
  'conservation_before':before,'conservation_after':c.verify(),'whole_D_N_uncontrolled':True,
  'Lean_called':False,'source_estimates_applied':False,'payments':False,'asymptotic':False,'score':0,'victory':False}
 save('final_receipt.json',receipt);assets['final_receipt.json']=h('final_receipt.json')
 manifest={'status':'FINAL_FROZEN_C4_NUMERIC_ANNEXE_ONLY','sha256_relative_role6_c4':assets,'files':len(assets),
  'report_relative_round17':'agent6_c4.md','report_sha256':c.digest(reportpath),'receipt_sha256':assets['final_receipt.json'],
  'input_rough_sha256':c.ROUGH_SHA,'initial_numeric_manifest_sha256':c.MANIFEST_SHA,
  'new_positions':count,'initial390_not_recounted':True,'protected_previous':799,
  'initial33_numeric_bindings_and_initial_manifest_unchanged':True,'noGlobal':True,'score':0,'victory':False}
 save('manifest.json',manifest)
 print(json.dumps({'status':receipt['status'],'report_sha256':c.digest(reportpath),'manifest_sha256':h('manifest.json'),
  'receipt_sha256':h('final_receipt.json'),'source_sha256':SOURCE,'gate_and_isolated_sha256':GATE,
  'new_positions':count,'initial390_not_recounted':True,'bindings':len(assets),'victory':False}))
if __name__=='__main__':run()
