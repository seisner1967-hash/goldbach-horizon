"""Final-input-only independent round11 judge: exact new banks, fresh new Lean."""
import sys
sys.dont_write_bytecode = True
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
import contextlib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import tempfile
from datetime import datetime, timezone
from fractions import Fraction

JUDGE = Path(__file__).resolve().parent
ROUND = JUDGE.parent
BASE = ROUND.parent
COMPILER = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE = BASE.parent / 'q356-canonical-binding-replay' / '.lake' / 'packages'
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq']
EXPECTED_REGISTRY = 'f86a31f72d624124338afad6932cd859dceae164a6f3422f9b8998164fcf9e05'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

input_path = JUDGE / 'input_sha256.json'
inputs = json.loads(input_path.read_text(encoding='utf-8'))
assert inputs['round'] == 11 and inputs['numerical_sources'] == 3
expected_dependency = BASE / 'round10' / 'lean' / 'ShortDivisorComplement.lean'
assert inputs['dependency_sources'] == [str(expected_dependency)]
assert inputs['external_sha256'][str(expected_dependency)] == '25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447'
assert inputs['role_reports'] == 5 and inputs['final_role_signals']['3']['completed'] is True
assert inputs['final_role_signals']['4']['completed'] is True
for signal in inputs['final_role_signals'].values():
    assert inputs['sha256'][signal['report']] == signal['report_sha256']
    assert inputs['sha256'][signal['module']] == signal['module_sha256']
assert len(inputs['new_lean_sources']) == 2

def verify_inputs():
    for relative, expected in inputs['sha256'].items():
        assert sha(ROUND / relative) == expected, relative
    for absolute, expected in inputs['external_sha256'].items():
        assert sha(Path(absolute)) == expected, absolute

verify_inputs()
registry_path = ROUND / 'previous_artifacts_sha256.json'
assert sha(registry_path) == EXPECTED_REGISTRY
registry = json.loads(registry_path.read_text(encoding='utf-8'))
assert registry['file_count'] == len(registry['sha256']) == 405
spec = importlib.util.spec_from_file_location('goldbach_round11_conservation', ROUND / 'conservation.py')
preservation = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = preservation
spec.loader.exec_module(preservation)
before_preserved = preservation.verify()
assert before_preserved['status'] == 'PRESERVED' and before_preserved['files'] == 405

def snapshot():
    paths = [BASE / relative for relative in registry['sha256']]
    paths += [ROUND / relative for relative in inputs['sha256']]
    paths += [Path(absolute) for absolute in inputs['external_sha256']]
    paths += [input_path]
    return {str(p): sha(p) for p in paths}

before = snapshot()
output = JUDGE / 'numerical'
output.mkdir(exist_ok=True)
for script in ['contract_witnesses.py', 'ap_prefix_checks.py', 'paired_axes_checks.py']:
    source = ROUND / script
    shutil.copyfile(source, output / script)
    argv = sys.argv
    sys.argv = [str(source), '--output-dir', str(output)]
    try:
        with (output / (source.stem + '.log')).open('w', encoding='utf-8') as log:
            with contextlib.redirect_stdout(log):
                runpy.run_path(str(source), run_name='__main__')
    finally:
        sys.argv = argv

numeric = {}
gates = {}
expected_status = {'witnesses.json': 'VERIFIED_NEW_FINITE_WITNESSES_ONLY',
    'ap_prefix.json': 'PASS_NEW_FINITE_CONTRACTS_ONLY',
    'paired_axes.json': 'PASS_NEW_PAIR_IDENTITY_ONLY'}
for name in expected_status:
    original, replay = ROUND / name, output / name
    production = json.loads(original.read_text(encoding='utf-8'))
    reproduced = json.loads(replay.read_text(encoding='utf-8'))
    assert production == reproduced, name
    assert original.read_bytes() == replay.read_bytes(), name
    assert reproduced['N'] == 100000000 and reproduced['status'] == expected_status[name]
    assert not any(reproduced[key] for key in ['global_D_N', 'asymptotic', 'payments', 'Lean_called', 'victory'])
    for key in ['properpowers_removed_from_raw', 'mu_n_squared_added', 'principal_substituted_for_actual_kernels', 'global_no_go']:
        assert reproduced.get(key, False) is False
    for relative, expected in reproduced['imports'].items():
        assert sha(BASE / relative) == expected, relative
    assert reproduced['conservation_before']['files'] == reproduced['conservation_after']['files'] == 405
    numeric[name] = dict(all_fields_equal=True, all_bytes_equal=True,
        production_sha256=sha(original), replay_sha256=sha(replay), status=reproduced['status'])
    gates[name] = reproduced

assert gates['witnesses.json']['script_sha256'] == sha(ROUND / 'contract_witnesses.py')
for name, script in [('ap_prefix.json', 'ap_prefix_checks.py'), ('paired_axes.json', 'paired_axes_checks.py')]:
    gate = gates[name]
    assert gate['script_sha256'] == sha(ROUND / script)
    assert gate['witness_script_sha256'] == sha(ROUND / 'contract_witnesses.py')
    assert gate['exact_helper_sha256'] == sha(ROUND / 'exact11.py')
    assert gate['shared_sha256'] == sha(ROUND / 'shared.py')

ap, paired = gates['ap_prefix.json'], gates['paired_axes.json']
assert ap['finite_coefficients']['status'] == 'PASS_FINITE_LOCAL_IDENTITY_ONLY'
assert ap['finite_coefficients']['B6_guarded_finite_product']['status'] == 'PASS_IDENTITY_ONLY'
assert ap['prefix_expansion']['status'] == 'PASS_IDENTITY_ONLY_WITH_RESTRICTED_E'
assert ap['scope_and_reference']['status'] == 'DISTINCT_LOW_PREFIX_AND_BAND_VERIFIED'
assert len(ap['finite_coefficients']['B6_guarded_finite_product']['all_divisors']) == 16
assert len(ap['prefix_expansion']['records']) == 12
assert len(ap['prefix_expansion']['prime_E']) == 5
assert not ap['finite_coefficients']['infinite_tail_evaluated']
assert ap['scope_and_reference']['false_pointwise_G_nonnegative']['G_over_S_N'] == '-1'
assert ap['properpower_first_axis']['n'] == 9
falsifiers = {}
certificates = {}
def inspect_contract(node, path):
    if isinstance(node, dict):
        if node.get('status') == 'ERROR_FALSIFIER':
            falsifiers[path] = node['status']
        if 'sign' in node and 'lower' in node and 'upper' in node:
            sign = node['sign']
            lo, hi = Fraction(node['lower']), Fraction(node['upper'])
            assert lo <= hi
            assert sign in {'NEGATIVE', 'POSITIVE', 'ZERO'}, (path, sign)
            if sign == 'NEGATIVE': assert hi < 0
            if sign == 'POSITIVE': assert lo > 0
            if sign == 'ZERO': assert lo == hi == 0
            certificates[path] = sign
        for key, value in node.items():
            inspect_contract(value, path + '.' + key)
    elif isinstance(node, list):
        for i, value in enumerate(node): inspect_contract(value, path + '[' + str(i) + ']')
for name, gate in gates.items(): inspect_contract(gate, name)
expected_falsifiers = {
    'ap_prefix.json.finite_coefficients.nonunit_r5',
    'ap_prefix.json.finite_coefficients.nonsquarefree_r9',
    'ap_prefix.json.finite_coefficients.intersection',
    'ap_prefix.json.prefix_expansion.omitted_tail',
    'ap_prefix.json.prefix_expansion.actual_intersection',
    'ap_prefix.json.scope_and_reference.rows.low_prefix',
    'ap_prefix.json.scope_and_reference.rows.low_plus_band',
    'ap_prefix.json.scope_and_reference.rows.negative_reference',
    'ap_prefix.json.scope_and_reference.false_pointwise_G_nonnegative',
    'ap_prefix.json.properpower_first_axis',
    'paired_axes.json.false_pair_favorable',
    'paired_axes.json.incidence_defect',
    'paired_axes.json.missing_face',
}
assert set(falsifiers) == expected_falsifiers, falsifiers
assert paired['pairs']['both_prime']['pair_sign']['sign'] == 'POSITIVE'
assert paired['pairs']['both_prime']['principal_sign']['sign'] == 'NEGATIVE'
assert paired['pairs']['one_prime_axis']['principal_sign']['sign'] == 'POSITIVE'
assert paired['incidence_defect']['incorrect_sign']['sign'] == 'NEGATIVE'
assert paired['missing_face']['tripled_n'] < 0
assert len(paired['full_partitions']) == 2
for partition in paired['full_partitions'].values():
    assert partition['status'] == 'PASS_FULL_FINITE_PARTITION_AND_P2_ONLY'
    assert partition['X_t'] == [1, 3, 7] and partition['D_t'] == [1] and partition['F_t'] == [7]
    assert partition['three_D_t'] == [3] and partition['disjoint_partition'] is True
    assert partition['positive_common_mu_negative_bases'] == []
    assert partition['positive_common_asymptotic_budget_numerically_validated'] is False
    assert partition['S_N_not_evaluated'] is True and partition['actual_kernels_not_replaced'] is True
verify_inputs()
assert snapshot() == before
numeric_receipt = dict(status='PASS_EXACT_REPLAY', jsons=numeric,
    contract_statuses={name: gates[name]['status'] for name in gates},
    falsifiers=falsifiers, falsifier_count=len(falsifiers),
    strict_rational_signs_checked=True, sign_certificate_count=len(certificates),
    sign_certificates=certificates, finite_domain_N=100000000,
    B6_divisor_cases=16, AP_cut_cases=12, restricted_prime_E_count=5,
    three_adic_partitions=2, old_banks_replayed=False,
    analytical_payments_tested=False, global_D_N_estimated=False, victory=False)
write_json(output / 'replay_receipt.json', numeric_receipt)

def executable_lean(text):
    """Remove nested comments and strings while retaining line layout for audit."""
    result, depth, i, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; result.extend('  '); i += 2; continue
            if pair == '-/':
                depth -= 1; result.extend('  '); i += 2; continue
            result.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if string:
            if text[i] == '\\':
                result.extend('  '); i += 2; continue
            if text[i] == '"':
                string = False
            result.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if pair == '/-':
            depth = 1; result.extend('  '); i += 2; continue
        if pair == '--':
            j = text.find('\n', i)
            if j < 0: j = len(text)
            result.extend(' ' * (j-i)); i = j; continue
        if text[i] == '"':
            string = True; result.append(' '); i += 1; continue
        result.append(text[i]); i += 1
    assert depth == 0 and not string
    return ''.join(result)

def declaration_names(code):
    stack, names = [], []
    for line in code.splitlines():
        namespace = re.match(r'^\s*namespace\s+([\w.]+)', line)
        if namespace:
            stack.append(('namespace', namespace.group(1))); continue
        section = re.match(r'^\s*section(?:\s+([\w.]+))?\s*$', line)
        if section:
            stack.append(('section', section.group(1) or '')); continue
        end = re.match(r'^\s*end(?:\s+([\w.]+))?\s*$', line)
        if end and stack:
            if end.group(1): assert end.group(1) == stack[-1][1]
            stack.pop(); continue
        theorem = re.match(r'^\s*(?:(?:private|protected|noncomputable)\s+)*theorem\s+([\w.]+)', line)
        if theorem:
            assert 'private theorem' not in line
            namespaces = [name for kind, name in stack if kind == 'namespace']
            names.append('.'.join(namespaces + [theorem.group(1)]))
    assert names and len(set(names)) == len(names)
    return names

assert COMPILER.is_file()
version = subprocess.run([str(COMPILER), '--version'], capture_output=True, text=True, encoding='utf-8')
assert version.returncode == 0 and 'version 4.15.0' in version.stdout
paths = [CACHE / name / '.lake' / 'build' / 'lib' for name in PACKAGES]
assert all(p.is_dir() for p in paths)
build = Path(tempfile.mkdtemp(prefix='fresh_', dir=JUDGE))
env = dict(os.environ)
env['LEAN_PATH'] = ';'.join([str(build)] + [str(p) for p in paths])
lean_results = []
compiled = set()
source_jobs = [(Path(p), False) for p in inputs['dependency_sources']] + [(ROUND / p, True) for p in inputs['new_lean_sources']]
for original, is_new in source_jobs:
    relative = str(original)
    original_text = original.read_text(encoding='utf-8')
    executable = executable_lean(original_text)
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b', executable)
    assert not forbidden, (relative, forbidden)
    imports = re.findall(r'^\s*import\s+([^\n]+)', executable, flags=re.M)
    for imported in [item for row in imports for item in row.split()]:
        assert imported.startswith('Mathlib.') or imported in compiled, (relative, imported)
    names = declaration_names(executable)
    target = build / original.name
    instrumented = original_text + '\n\n' + '\n'.join('#print axioms ' + name for name in names) + '\n'
    target.write_text(instrumented, encoding='utf-8')
    (build / (original.stem + '_original_source.txt')).write_bytes(original.read_bytes())
    olean = build / (original.stem + '.olean')
    assert not olean.exists()
    argv = [str(COMPILER), '-o', str(olean), str(target)]
    completed = subprocess.run(argv, cwd=build, env=env, capture_output=True, text=True,
        encoding='utf-8', errors='replace')
    raw_output = completed.stdout + completed.stderr
    log = build / (original.stem + '.log')
    log.write_text(raw_output, encoding='utf-8')
    entry = dict(module=original.stem, new_module=is_new, original_source_sha256=sha(original),
        instrumented_source=str(target), instrumented_source_sha256=sha(target),
        source_snapshot=str(build / (original.stem + '_original_source.txt')),
        command_argv=argv, cwd=str(build), exit_code=completed.returncode,
        log=str(log), log_sha256=sha(log), theorem_count=len(names), theorem_names=names,
        forbidden_executable_tokens=forbidden, imports=imports)
    if completed.returncode:
        entry['failure_classification'] = 'ACTUAL_COMPILER_FAILURE_REQUIRES_DIAGNOSTIC'
        write_json(JUDGE / 'compile_failure_receipt.json', entry)
        print(raw_output)
        raise SystemExit(completed.returncode)
    assert not re.search(r'\berror:', raw_output), raw_output
    # An unused source-wrapper premise is a linter diagnostic, not a failed proof.
    entry['warnings'] = [line for line in raw_output.splitlines() if 'warning:' in line]
    axiom_lines = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw_output)
    no_axiom_lines = re.findall(r"'([^']+)' does not depend on any axioms", raw_output)
    axiom_map = {}
    for name, list_text in axiom_lines:
        axioms = [a.strip() for a in list_text.split(',') if a.strip()]
        assert set(axioms) <= STANDARD_AXIOMS, (name, axioms)
        if name in axiom_map: assert axiom_map[name] == axioms
        axiom_map[name] = axioms
    for name in no_axiom_lines:
        axiom_map[name] = []
    assert set(names) <= set(axiom_map), (names, axiom_map, raw_output)
    assert 'sorryAx' not in raw_output
    assert olean.is_file()
    entry.update(status='PASS_FRESH_COMPILE_STANDARD_AXIOMS',
        axioms={name: axiom_map[name] for name in names}, olean=str(olean), olean_sha256=sha(olean))
    entry['additional_printed_definitions_axioms'] = {
        name: axioms for name, axioms in axiom_map.items() if name not in names}
    lean_results.append(entry)
    compiled.add(original.stem)

verify_inputs()
assert snapshot() == before, 'A frozen source or earlier production artifact changed'
after_preserved = preservation.verify()
assert after_preserved['status'] == 'PRESERVED' and after_preserved['files'] == 405
new_results = [row for row in lean_results if row['new_module']]
dependency_results = [row for row in lean_results if not row['new_module']]
new_count = sum(row['theorem_count'] for row in new_results)
new_names = [name for row in new_results for name in row['theorem_names']]
assert len(set(new_names)) == new_count, 'Duplicate new theorem names across modules'
assert len(new_results) == 2 and len(dependency_results) == 1
assert dependency_results[0]['theorem_count'] == 17
receipt = dict(round=11, status='PARTIAL_COMMON_MODEL_COMPENSATION_WITH_RETAINED_SINGLETONS_FACES_AND_ENTROPY',
    victory=False, score=0, recorded_at_utc=datetime.now(timezone.utc).isoformat(),
    input_manifest=str(input_path), input_manifest_sha256=sha(input_path),
    source_sha256=inputs['sha256'], external_source_sha256=inputs['external_sha256'],
    final_role_signals=inputs['final_role_signals'], numerical_replay=numeric_receipt,
    numerical_receipt_sha256=sha(output / 'replay_receipt.json'),
    lean_invoked=True, compiler=str(COMPILER), compiler_sha256=sha(COMPILER),
    compiler_version=version.stdout.strip(), lean_path=env['LEAN_PATH'],
    mathlib_cache_packages={name: str(path) for name, path in zip(PACKAGES, paths)},
    fresh_build_directory=str(build), reused_custom_oleans=False,
    modules=new_results, dependency_rebuilds=dependency_results, new_lean_modules=len(new_results), new_lean_conclusions=new_count,
    previous_auxiliary_modules=11, previous_auxiliary_conclusions=141,
    cumulative_auxiliary_modules=11+len(new_results), cumulative_auxiliary_conclusions=141+new_count,
    preserved_previous_artifacts_before=before_preserved,
    preserved_previous_artifacts_after=after_preserved,
    production_sha256_before=before, production_sha256_after=snapshot(),
    judge_scripts_sha256={name: sha(JUDGE / name) for name in ['audit-judge.ps1', 'verify-frozen.ps1', 'run-judge.py']},
    source54=dict(literal_exponent='-sqrt(u/60)', weaker_valid_majorant='-sqrt(u)/60',
        old_pixels_preserved=True, rerendered=False, adaptive_source_u_min='10^24'),
    semantic_limitations=['Identities do not estimate the unpaid signed moment',
        'P6 retains H2, singletons, faces, entropy, J0/J1 and the true detector; B13 remains unpaid',
        'Written P5 pays the common model alone when 3 is coprime to N; it does not pay the whole pair',
        'Physical-band BV onset remains unevaluated', 'Covered term 2 max(e,0) remains unpaid'],
    old_passed_banks_replayed=False, old_independent_lean_modules_recompiled=False, required_old_dependency_rebuilt=True)
write_json(JUDGE / 'judge_receipt.json', receipt)
print(json.dumps(dict(status=receipt['status'], numerical_status=numeric_receipt['status'],
    lean_exit_codes=[row['exit_code'] for row in lean_results], new_theorems=new_count,
    cumulative_theorems=141+new_count, dependency_theorems=17, preserved_files=405, victory=False, score=0), indent=2))
