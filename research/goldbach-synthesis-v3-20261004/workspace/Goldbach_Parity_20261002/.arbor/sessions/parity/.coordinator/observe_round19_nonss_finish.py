"""Root reads and binds stored evidence only; no arithmetic producer or Lean."""
import json, hashlib, re, sys
from pathlib import Path
from datetime import datetime, timezone
sys.set_int_max_str_digits(0)
B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R = B / 'round19'
C = B / '.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def save(p, d):
    with p.open('x', encoding='utf-8') as f:
        f.write(json.dumps(d, ensure_ascii=False, indent=2)+'\n')
receipt_path = R / 'role6_nonss/canonical_attempt01/receipt.json'
final_path = R / 'role6_nonss/final_receipt.json'
receipt, final = read(receipt_path), read(final_path)
assert sha(receipt_path) == '317c9788eefa91ada5af1d8fc32f022530869fbdee7b394d1fb364aefd9b80f5'
assert sha(final_path) == '1090604087418b7b940147f3504b519364d095bff453461969bf7d02b5ddee2b'
bindings = {}
for rel, entry in final['bindings'].items():
    p = R / rel
    assert p.stat().st_size == entry['bytes'] and sha(p) == entry['sha256'], rel
    bindings['round19/'+rel] = entry['sha256']
bindings['round19/role6_nonss/final_receipt.json'] = sha(final_path)
assert len(final['bindings']) == 25
assert receipt['exit_code'] == 0 and receipt['subprocess_launch_error'] is None
assert receipt['new_canonical_invocations'] == 1 and receipt['automatic_replay'] is False
assert receipt['old_producer_kernel_preflight_Lean_PDF_execution'] is False
assert receipt['captured_binding_hashes_unchanged_after_execution'] is True
assert receipt['prepared_original_binding_hashes_unchanged_after_execution'] is True
for key, capture in receipt['PREEXEC_captures'].items():
    assert sha(Path(capture['snapshot'])) == capture['sha256'], key
    assert sha(Path(capture['original'])) == capture['sha256'], key
result = read(R / 'nonss.json')
log = read(Path(receipt['log']))
assert result['status'] == log['status'] == 'PASS_NEW_FINITE_IDENTITIES_ONLY'
assert log['result_sha256'] == receipt['result_sha256'] == sha(R / 'nonss.json')
assert log['counts'] == result['counts']
assert log['kernel_sign_positions_counts'] == result['kernel_sign_positions_counts']
assert result['N'] == 100000000 and result['all_1001_integer_positions'] is True
assert result['H4_exact_support_reindex_verified_theta_and_raw'] is True
assert result['raw_equals_theta_plus_properpower_exact_terms_and_bounds'] is True
assert result['no_floats_no_assumed_signs_no_raw_mu2_no_fake_zero_kernels'] is True
for k in ['victory', 'analytic_H7_H9_or_global_DN_bounds_applied',
          'source_onset_logN_10power24_verified',
          'written_rank3_onset_logN_10power40_verified',
          'all_old_banks_Lean_PDF_preflights_executed']:
    assert result[k] is False, k
assert result['input_manifest_sha256'] == receipt['input_manifest_sha256']
certs = {'stored_positions': 0, 'stored_sign_labels': {}}
def visit(x):
    if isinstance(x, dict):
        if {'lower_scaled','upper_scaled','sign','dyadic_bits'} <= x.keys():
            assert re.fullmatch(r'-?\d+', x['lower_scaled'])
            assert re.fullmatch(r'-?\d+', x['upper_scaled'])
            assert x['dyadic_bits'] == 128
            assert x['sign'] in {'POSITIVE','NEGATIVE','ZERO','UNRESOLVED'}
            certs['stored_positions'] += 1
            label = x['sign']
            certs['stored_sign_labels'][label] = certs['stored_sign_labels'].get(label,0)+1
        for v in x.values(): visit(v)
    elif isinstance(x,list):
        for v in x: visit(v)
visit(result)
# Only inspect certificate encodings and pre-existing labels, never signs/logs.
def compact(x):
    if isinstance(x, (dict,list)):
        return {'type':type(x).__name__, 'length':len(x)}
    if isinstance(x,str) and len(x)>120:
        return {'type':'stored_string','characters':len(x),'sha256_utf8':hashlib.sha256(x.encode()).hexdigest()}
    return x
h8 = {k:compact(v) for k,v in result['finite_H8'].items()}
sources = {
 'TerminalPrimeExtraction.lean':'36307959fc9e0d968be0e39fca9899036351158ad4c048de71cc5f6dcd321966',
 'BalancedResourceSwitch.lean':'2d2153a5f0460e74a744e4625f80eca568b1bc8b6efe18a7f5c3a42a6692aa2f',
 'SignedHyperbolicCRT.lean':'12126717d5fee5f7d3d92617da21b37edd31a9c0861ef40e17151b8b3b359446',
 'NonSSBracketSwitch.lean':'b436ced29ff618df48ccbf0cef49fadb099721f5007b85cdaa4496a121d1e21e',
 'RankTwoHarmonic.lean':'1dec1108ad6c699da9fbc38132150cb7ff3d8b3ffcefb22a15506a88c609bae2'
}
for n, expected in sources.items(): assert sha(R/'role4'/n)==expected, n
assert sha(R/'role4/build.py') == '52f87be8c6dcd09f80051547971a51d2b9ffccefad4b83d7a51a46728e55be62'
deps = read(R/'role4/dependencies_readonly.json')['bindings']
for rel, expected in deps.items(): assert sha(B/rel)==expected, rel
observation = {
 'status':'ROOT_VERIFIED_ACTUAL_UNIQUE_NEW_NONSS19_FINISH_PASS_AUXILIARY_ONLY',
 'observed_utc':datetime.now(timezone.utc).isoformat(), 'round':19,'node':'14.4',
 'actual_start':receipt['started_at_utc'],'actual_finish':receipt['finished_at_utc'],
 'actual_exit_code':0,'canonical_invocations':1,'replays':0,
 'verified_final_bindings':25,'verified_PREEXEC_captures':13,
 'numeric_bindings':bindings, 'stored_counts':result['counts'],
 'stored_certificate_encoding_summary_not_recomputed_signs':certs,
 'stored_H8_metadata':h8,'stored_falsifiers':result['falsifiers'],
 'formal4_full_root_read_current_source_hashes':sources,
 'formal4_readonly_dependency_bindings':deps,
 'formal4_sources_only_not_compiler_counts':{'theorems':100,'definitions':55,'structures':3,'axiom_prints':160},
 'metadata_reader_truncated_outputs':['f4479f dictionary inventory','2c6c7f uncompressed H8'],
 'truncation_resolved_by_compact_stored_metadata_read':True,
 'root_math_producer_Lean_or_sign_recomputations':0,'victory':False,
 'official_Judge_counts_modified':False
}
save(C/'messages/round19_nonss_finish_root_observation.json', observation)
print(json.dumps({k:observation[k] for k in ['status','actual_start','actual_finish','stored_counts','stored_certificate_encoding_summary_not_recomputed_signs','stored_H8_metadata']},ensure_ascii=False,indent=2))
