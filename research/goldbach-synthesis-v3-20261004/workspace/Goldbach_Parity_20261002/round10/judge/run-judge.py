"""Final-input-only independent round10 judge: exact new banks, fresh new Lean."""
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
EXPECTED_REGISTRY = '39210db5693d97ad22ffe54bfb3e21c238de207b7cb4f73262aae1e0d3a4f9cb'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

input_path = JUDGE / 'input_sha256.json'
inputs = json.loads(input_path.read_text(encoding='utf-8'))
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
assert registry['file_count'] == len(registry['sha256']) == 341
spec = importlib.util.spec_from_file_location('goldbach_round10_conservation', ROUND / 'conservation.py')
preservation = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = preservation
spec.loader.exec_module(preservation)
before_preserved = preservation.verify()
assert before_preserved['status'] == 'PRESERVED' and before_preserved['files'] == 341

def snapshot():
    paths = [BASE / relative for relative in registry['sha256']]
    paths += [ROUND / relative for relative in inputs['sha256']]
    paths += [Path(absolute) for absolute in inputs['external_sha256']]
    paths += [input_path]
    return {str(p): sha(p) for p in paths}

before = snapshot()
output = JUDGE / 'numerical'
output.mkdir(exist_ok=True)
for script in ['witness_search.py', 'paired_cofactor_checks.py']:
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
for name in ['witnesses.json', 'paired_cofactors.json']:
    original, replay = ROUND / name, output / name
    production = json.loads(original.read_text(encoding='utf-8'))
    reproduced = json.loads(replay.read_text(encoding='utf-8'))
    assert production == reproduced, name
    assert original.read_bytes() == replay.read_bytes(), name
    assert reproduced['N'] == 100000000 and reproduced['victory'] is False
    for relative, expected in reproduced['imports'].items():
        assert sha(BASE / relative) == expected, relative
    assert reproduced['conservation_before']['files'] == reproduced['conservation_after']['files'] == 341
    numeric[name] = dict(all_fields_equal=True, all_bytes_equal=True,
        production_sha256=sha(original), replay_sha256=sha(replay), status=reproduced['status'])

gate = json.loads((output / 'paired_cofactors.json').read_text(encoding='utf-8'))
assert gate['status'] == 'PASS_FINITE_IDENTITIES_ONLY'
assert gate['script_sha256'] == sha(ROUND / 'paired_cofactor_checks.py')
assert gate['witness_script_sha256'] == sha(ROUND / 'witness_search.py')
assert all(gate[key]['status'] == 'PASS_IDENTITY_ONLY' for key in ['dual_and_matched', 'small_cofactor', 'singular'])
false_paths = ['false_all_J2_favorable', 'small_cofactor.false_c_large',
    'small_cofactor.false_p_small', 'small_cofactor.false_drop_mu_squared',
    'small_cofactor.false_complete_small_fibre', 'singular.nonunit_extension',
    'singular.properpower_extension', 'singular.multiplicity']
falsifiers = {}
for dotted in false_paths:
    node = gate
    for part in dotted.split('.'):
        node = node[part]
    assert node['status'] == 'ERROR_FALSIFIER', dotted
    falsifiers[dotted] = node['status']
cases = gate['dual_and_matched']['cases']
for name, row in cases.items():
    for field, polynomial in [('W_kernel_sign', 'W_kernel'), ('C_sign', 'C')]:
        certificate = row[field]
        lo, hi = Fraction(certificate['lower']), Fraction(certificate['upper'])
        assert lo <= hi
        if certificate['sign'] == 'NEGATIVE':
            assert hi < 0
        elif certificate['sign'] == 'POSITIVE':
            assert lo > 0
        else:
            assert certificate['sign'] == 'ZERO' and lo == hi == 0 and not row[polynomial]
for name, expected in [('rough_prime_bulk', 'NEGATIVE'), ('rough_semiprime_bulk', 'NEGATIVE'),
        ('small3_two_large_bulk', 'POSITIVE'), ('one_large_small_nonsquarefree', 'ZERO'),
        ('nonsquarefree_bulk', 'ZERO')]:
    certificate = cases[name]['C_sign']
    lo, hi = Fraction(certificate['lower']), Fraction(certificate['upper'])
    assert certificate['sign'] == expected and lo <= hi
    if expected == 'NEGATIVE':
        assert hi < 0
    elif expected == 'POSITIVE':
        assert lo > 0
    else:
        assert lo == hi == 0 and not cases[name]['C']
assert gate['false_all_J2_favorable']['sign_certificate']['sign'] == 'POSITIVE'
assert gate['native_physical_phase']['character_ratio'] == 1
assert not any(gate[key] for key in ['asymptotic_signs_validated', 'analytical_payments_tested',
    'properpowers_removed_from_raw', 'global_D_N_estimated', 'victory', 'Lean_called'])
verify_inputs()
assert snapshot() == before
numeric_receipt = dict(status='PASS_EXACT_REPLAY', jsons=numeric, contract_statuses={
    k: gate[k]['status'] for k in ['dual_and_matched', 'small_cofactor', 'singular']},
    falsifiers=falsifiers, strict_rational_signs_checked=True, observed_signs=gate['observed_signs'],
    finite_domain_N=100000000, matched_cases=len(cases), source_sha256=sha(ROUND / 'paired_cofactor_checks.py'),
    witness_source_sha256=sha(ROUND / 'witness_search.py'), old_banks_replayed=False,
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
            stack.append(namespace.group(1)); continue
        end = re.match(r'^\s*end(?:\s+([\w.]+))?\s*$', line)
        if end and stack:
            if end.group(1): assert end.group(1) == stack[-1]
            stack.pop(); continue
        theorem = re.match(r'^\s*(?:(?:private|protected|noncomputable)\s+)*theorem\s+([\w.]+)', line)
        if theorem:
            assert 'private theorem' not in line
            names.append('.'.join(stack + [theorem.group(1)]))
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
for relative in inputs['new_lean_sources']:
    original = ROUND / relative
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
    entry = dict(module=original.stem, original_source_sha256=sha(original),
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
    lean_results.append(entry)
    compiled.add(original.stem)

verify_inputs()
assert snapshot() == before, 'A frozen source or earlier production artifact changed'
after_preserved = preservation.verify()
assert after_preserved['status'] == 'PRESERVED' and after_preserved['files'] == 341
new_count = sum(row['theorem_count'] for row in lean_results)
receipt = dict(round=10, status='PARTIAL_NATIVE_COFACTOR_IDENTITIES_WITH_OPEN_SIGNED_COMPENSATION',
    victory=False, score=0, recorded_at_utc=datetime.now(timezone.utc).isoformat(),
    input_manifest=str(input_path), input_manifest_sha256=sha(input_path),
    source_sha256=inputs['sha256'], external_source_sha256=inputs['external_sha256'],
    final_role_signals=inputs['final_role_signals'], numerical_replay=numeric_receipt,
    numerical_receipt_sha256=sha(output / 'replay_receipt.json'),
    lean_invoked=True, compiler=str(COMPILER), compiler_sha256=sha(COMPILER),
    compiler_version=version.stdout.strip(), lean_path=env['LEAN_PATH'],
    mathlib_cache_packages={name: str(path) for name, path in zip(PACKAGES, paths)},
    fresh_build_directory=str(build), reused_custom_oleans=False,
    modules=lean_results, new_lean_modules=len(lean_results), new_lean_conclusions=new_count,
    previous_auxiliary_modules=9, previous_auxiliary_conclusions=116,
    cumulative_auxiliary_modules=9+len(lean_results), cumulative_auxiliary_conclusions=116+new_count,
    preserved_previous_artifacts_before=before_preserved,
    preserved_previous_artifacts_after=after_preserved,
    production_sha256_before=before, production_sha256_after=snapshot(),
    judge_scripts_sha256={name: sha(JUDGE / name) for name in ['audit-judge.ps1', 'verify-frozen.ps1', 'run-judge.py']},
    source54=dict(literal_exponent='-sqrt(u/60)', weaker_valid_majorant='-sqrt(u)/60',
        old_pixels_preserved=True, rerendered=False, adaptive_source_u_min='10^24'),
    semantic_limitations=['Identities do not estimate the unpaid signed moment',
        'H2-S(N)M2, J0/J1 and E11/E12 remain unpaid',
        'Written corner and singular-mask payments do not replace parity compensation',
        'Physical-band BV onset remains unevaluated', 'Covered term 2 max(e,0) remains unpaid'],
    old_passed_banks_replayed=False, old_lean_modules_recompiled=False)
write_json(JUDGE / 'judge_receipt.json', receipt)
print(json.dumps(dict(status=receipt['status'], numerical_status=numeric_receipt['status'],
    lean_exit_codes=[row['exit_code'] for row in lean_results], new_theorems=new_count,
    cumulative_theorems=116+new_count, preserved_files=341, victory=False, score=0), indent=2))
