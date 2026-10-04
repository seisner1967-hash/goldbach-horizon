"""Read selected stored quantities, without evaluating logarithms or signs."""
import json,hashlib,sys
from pathlib import Path
sys.set_int_max_str_digits(0)
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
p=B/'round19/allrang.json'; raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='29251df2d05db105d6339747fdda6af327279bc95478df7a9154414e156e8e2b'
d=json.loads(raw)
assert d['status']=='PASS_NEW_ALL_RANK_FINITE_IDENTITIES_ONLY' and d['victory'] is False
functions={}
for measure,values in d['global_actual_affine_functionals_theta_raw_PP'].items():
    functions[measure]={name:{k:value[k] for k in ['whole_box_enclosure','whole_box_sign','exact_zero','affine_in_S_no_new_S_evaluation']}
                       for name,value in values.items() if name in {'Gamma0','Gamma_rank','Pi','Pi_principal'}}
modules={R:{'distinct_modules':v['distinct_modules'],
            'max_actual_representation_multiplicity':v['max_actual_representation_multiplicity'],
            'bounded_by40_and64':v['bounded_by40_and64'],
            'all_T0_Ts_TFs_entries_retained':v['all_T0_Ts_TFs_entries_retained']}
         for R,v in d['all_AP_modules_representations_level_and_multiplicity'].items()}
falsifiers={k:{'status':v['status'],'first_example':
              {x:y for x,y in (v.get('first_example') or {}).items() if x in {'d','P_d','P','L','X','d_times_L','R','c','r','k','k_s','t_divisor39','face_multiplier','fixed_f_divisor39P','module'}}}
            for k,v in d['falsifiers'].items()}
summary={'status':'ROOT_READ_STORED_NEW_RANK19_NUMERIC_QUANTITIES_ONLY',
 'result_sha256':hashlib.sha256(raw).hexdigest(),'result_bytes':len(raw),
 'counts':d['counts'],'all_module_representation_metadata':modules,
 'stored_global_functionals':functions,'falsifiers':falsifiers,
 'chi_min':d['chi_min'],'C_star':d['C_star'],
 'raw_PP_catalogue_positions':len(d['all_candidate_properpowers_value_primebase_exponent_including_nonunits']),
 'bitmap_metadata':d['candidate_full_domain_prime_bitmap'],
 'primitive_log_catalogue_metadata':d['strict_primitive_log_catalog'],
 'source_onset_applied':d['source_onset_logN_10power24_applied'],
 'global_Gamma_DN_capacity_bound':d['Gamma_rank_DN_global_capacity_bound_proved'],
 'root_producer_kernel_factorization_primality_log_or_sign_executions':0,
 'official_counts_modified':False,'victory':False}
out=B/'.arbor/sessions/parity/.coordinator/messages/round19_rank_stored_quantities_root.json'
with out.open('x',encoding='utf-8') as f: f.write(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in {'bitmap_metadata','primitive_log_catalogue_metadata'}},ensure_ascii=False,indent=2))
