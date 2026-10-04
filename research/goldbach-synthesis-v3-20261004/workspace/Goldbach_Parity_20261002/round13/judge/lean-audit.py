"""Fresh compilation of the two required source dependencies and FINAL round13 modules."""
import json
import os
import re
import subprocess
import tempfile
from hashlib import sha256
from pathlib import Path

COMPILER = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq']
MATHLIB_COMMIT = '9837ca9d65d9de6fad1ef4381750ca688774e608'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def executable_lean(text):
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

def declarations(code):
    stack, proof_names, definitions = [], [], []
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
        declaration = re.match(r'^\s*(?:@\[[^\]]+\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|opaque|structure|inductive)\s+([\w.]+)', line)
        if declaration:
            assert not re.search(r'\bprivate\b', line), 'Private declaration needs explicit name resolution audit'
            namespaces = [name for kind, name in stack if kind == 'namespace']
            name = '.'.join(namespaces + [declaration.group(2)])
            (proof_names if declaration.group(1) in ('theorem', 'lemma') else definitions).append(name)
    assert proof_names and len(set(proof_names + definitions)) == len(proof_names + definitions)
    return proof_names, definitions

def run(inputs, judge, base):
    cache = base.parent / 'q356-canonical-binding-replay' / '.lake' / 'packages'
    assert COMPILER.is_file()
    version = subprocess.run([str(COMPILER), '--version'], capture_output=True, text=True, encoding='utf-8')
    assert version.returncode == 0 and 'version 4.15.0' in version.stdout
    paths = [cache / name / '.lake' / 'build' / 'lib' for name in PACKAGES]
    assert all(p.is_dir() for p in paths)
    assert (cache / 'mathlib' / 'lean-toolchain').read_text(encoding='utf-8').strip() == 'leanprover/lean4:v4.15.0'
    commit = subprocess.run(['git', '-C', str(cache / 'mathlib'), 'rev-parse', 'HEAD'],
                            capture_output=True, text=True, encoding='utf-8')
    assert commit.returncode == 0 and commit.stdout.strip() == MATHLIB_COMMIT
    build = Path(tempfile.mkdtemp(prefix='fresh_', dir=judge))
    env = dict(os.environ)
    env['LEAN_PATH'] = ';'.join([str(build)] + [str(p) for p in paths])
    results, compiled = [], set()
    jobs = [(Path(p), False) for p in inputs['dependency_sources']]
    jobs += [(judge.parent / p, True) for p in inputs['new_lean_sources']]
    for original, is_new in jobs:
        expected = inputs['sha256'][original.relative_to(judge.parent).as_posix()] if is_new else inputs['external_sha256'][str(original)]
        assert sha(original) == expected
        original_text = original.read_text(encoding='utf-8')
        code = executable_lean(original_text)
        forbidden = re.findall(r'\b(?:sorry|admit|axiom|constant|native_decide)\b', code)
        forbidden += re.findall(r'^\s*axioms\b', code, flags=re.M)
        assert not forbidden, (str(original), forbidden)
        imports = re.findall(r'^\s*import\s+([^\n]+)', code, flags=re.M)
        for imported in [item for row in imports for item in row.split()]:
            assert imported == 'Mathlib' or imported.startswith('Mathlib.') or imported in compiled, (original, imported)
        proofs, defs = declarations(code)
        target = build / original.name
        instrumented = original_text + '\n\n' + '\n'.join('#print axioms ' + name for name in proofs + defs) + '\n'
        target.write_text(instrumented, encoding='utf-8')
        snapshot = build / (original.stem + '_original_source.txt')
        snapshot.write_bytes(original.read_bytes())
        olean = build / (original.stem + '.olean')
        assert not olean.exists()
        argv = [str(COMPILER), '-o', str(olean), str(target)]
        completed = subprocess.run(argv, cwd=build, env=env, capture_output=True, text=True,
                                   encoding='utf-8', errors='replace')
        raw = completed.stdout + completed.stderr
        log = build / (original.stem + '.log')
        log.write_text(raw, encoding='utf-8')
        entry = dict(module=original.stem, new_module=is_new, original_source_sha256=sha(original),
            instrumented_source=str(target), instrumented_source_sha256=sha(target), source_snapshot=str(snapshot),
            command_argv=argv, cwd=str(build), exit_code=completed.returncode, log=str(log), log_sha256=sha(log),
            theorem_count=len(proofs), theorem_names=proofs, definition_count=len(defs), definition_names=defs,
            forbidden_executable_tokens=forbidden, imports=imports)
        if completed.returncode:
            entry['failure_classification'] = 'ACTUAL_COMPILER_FAILURE_REQUIRES_DIAGNOSTIC'
            (judge / 'compile_failure_receipt.json').write_text(json.dumps(entry, indent=2) + '\n', encoding='utf-8')
            print(raw)
            raise SystemExit(completed.returncode)
        assert not re.search(r'\berror:', raw) and 'sorryAx' not in raw
        axioms = {}
        for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw):
            used = [x.strip() for x in body.split(',') if x.strip()]
            assert set(used) <= STANDARD_AXIOMS, (name, used)
            if name in axioms: assert axioms[name] == used
            axioms[name] = used
        for name in re.findall(r"'([^']+)' does not depend on any axioms", raw):
            axioms[name] = []
        assert set(proofs + defs) <= set(axioms), (original, set(proofs + defs) - set(axioms))
        assert olean.is_file()
        entry.update(status='PASS_FRESH_COMPILE_STANDARD_AXIOMS', warnings=[l for l in raw.splitlines() if 'warning:' in l],
            theorem_axioms={n: axioms[n] for n in proofs}, definition_axioms={n: axioms[n] for n in defs},
            other_printed_axioms={n: a for n, a in axioms.items() if n not in proofs + defs},
            olean=str(olean), olean_sha256=sha(olean))
        if not is_new:
            assert entry['theorem_count'] == inputs['dependency_expected_conclusions'][original.stem]
        results.append(entry)
        compiled.add(original.stem)
    new = [r for r in results if r['new_module']]
    names = [n for r in new for n in r['theorem_names']]
    assert len(new) == 2 and len(set(names)) == len(names)
    return dict(lean_invoked=True, compiler=str(COMPILER), compiler_sha256=sha(COMPILER),
        compiler_version=version.stdout.strip(), mathlib_commit=MATHLIB_COMMIT,
        mathlib_packages={n: str(p) for n, p in zip(PACKAGES, paths)},
        fresh_build_directory=str(build), lean_path=env['LEAN_PATH'], reused_custom_oleans=False,
        modules=new, dependency_rebuilds=[r for r in results if not r['new_module']],
        new_lean_modules=2, new_lean_conclusions=len(names),
        new_definition_count=sum(r['definition_count'] for r in new),
        cumulative_auxiliary_modules=13+2, cumulative_auxiliary_conclusions=169+len(names))
