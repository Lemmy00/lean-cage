"""Replay source consumers after the reporting collector correction.

The original proof sources and snapshots remain historical inputs. Only generated
temporary, registered result-local and immutable string identifiers are adapted. String mappings preserve
the complete registered global value and alias relationships. Every adapted term
is checked against the current complete-helper AST; a mapping never replaces
the source theorem replay. A matching checked cache needs no rebuild.
"""
# §AR-m4-routes.reporting.chain: Retain the current helper's actual source consumers.
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / '.tools/reporting/rebase'
NAMES = ['main', 'policy', 'arguments', 'digest', 'validation', 'initialization', 'parent']
TEMP = re.compile(r"_t'(\d+)\b")
RESULT = re.compile(r"(?<![\w'])__res__\d+\b")
LITERAL = re.compile(r"(?<![\w'])v?(___stringlit_\d+)\b")
IDENTIFIER = re.compile(r"(?<![\w'])(?:_t'(?P<temporary>\d+)\b|(?P<result>__res__\d+)\b|(?P<variable>v)?(?P<literal>___stringlit_\d+)\b)")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def consumers():
    sys.path[:0] = [str(ROOT / 'm4/main'), str(ROOT / 'm4'), str(ROOT / 'm4/controller')]
    result = {}
    for name in NAMES:
        spec = importlib.util.spec_from_file_location('reporting_source_' + name, ROOT / 'm4' / name / 'check.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        result[name] = module
    return result


def paths():
    result = {str(ROOT / '.tools/m4' / n / 'proofs'): str(WORK / n / 'proofs') for n in NAMES}
    result[str(ROOT / '.tools/m4/main/number')] = str(WORK / 'main/number')
    return result


def flags(module, *, checker=False):
    mapping = paths()
    return [mapping.get(value, value) for value in module.flags(checker=checker)]


def literal_globals(source):
    """Read complete generated globals, rejecting duplicate or aliased registrations."""
    pattern = r'^Definition v(___stringlit_\d+) := \{\|(.*?)^\|\}\.'
    declarations = re.findall(pattern, source, re.S | re.M)
    result = {}
    for name, body in declarations:
        if name in result:
            raise ValueError('duplicate string global: ' + name)
        fields = re.findall(r'\b(gvar_info|gvar_init|gvar_readonly|gvar_volatile)\s*:=', body)
        if sorted(fields) != ['gvar_info', 'gvar_init', 'gvar_readonly', 'gvar_volatile']:
            raise ValueError('unsupported string global fields: ' + name)
        result[name] = body.split()
    definitions = re.search(r'^Definition global_definitions\b.*?(?=^Definition |\Z)', source, re.S | re.M)
    if definitions is None:
        raise ValueError('missing global definitions')
    entries = re.findall(r'\(\s*(___stringlit_\d+)\s*,\s*Gvar\s+v(___stringlit_\d+)\s*\)', definitions[0])
    if len(entries) != len(result) or len({name for name, _ in entries}) != len(entries):
        raise ValueError('duplicate or missing string global registration')
    if set(result) != {name for name, _ in entries} or any(name != value for name, value in entries):
        raise ValueError('aliased string global registration')
    return result


def checked_bijection(pairs, label):
    mapping, reverse = {}, {}
    for left, right in pairs:
        if left in mapping and mapping[left] != right:
            raise ValueError('inconsistent ' + label + ' renaming')
        if right in reverse and reverse[right] != left:
            raise ValueError(label + ' renaming is not injective')
        mapping[left], reverse[right] = right, left
    return mapping


def proof_literals():
    """Include literal identities mentioned outside the selected main prefix."""
    return {literal for name in NAMES for path in (ROOT / 'm4' / name).glob('*.v')
            for literal in LITERAL.findall(path.read_text())}


def proof_results():
    return {slot for name in NAMES for path in (ROOT / 'm4' / name).glob('*.v')
            for slot in RESULT.findall(path.read_text())}


def result_locals(function):
    """Accept only CompCert's registered, nonvolatile result-struct locals."""
    variables = re.search(r'fn_vars\s*:=\s*(.*?);\s*fn_temps\s*:=', function, re.S)
    if variables is None:
        return {}
    names = RESULT.findall(variables[1])
    entries = re.findall(r'\((__res__\d+)\s*,\s*\(\s*(Tstruct\s+_result\s+noattr)\s*\)\s*\)', variables[1])
    if len(entries) != len(names) or len({name for name, _ in entries}) != len(entries):
        raise ValueError('unsupported or duplicate generated result local')
    return {name: tuple(kind.split()) for name, kind in entries}


def renaming(reference, current):
    pattern = r'Definition f_main :=.*?^\|\}\.'
    old_match = re.search(pattern, reference, re.S | re.M)
    new_match = re.search(pattern, current, re.S | re.M)
    if old_match is None or new_match is None:
        raise ValueError('missing main function')
    old_function, new_function = old_match[0], new_match[0]
    old, new = old_function, new_function
    # The collector calls follow every previously accepted input/history frontier.
    old = old[old.index('fn_body :='):old.index('(Evar _capture')]
    new = new[new.index('fn_body :='):new.index('(Evar _capture')]
    canonical = lambda body: RESULT.sub('_RESULT', LITERAL.sub('_STRING', TEMP.sub('_TEMP', body))).split()
    if canonical(old) != canonical(new):
        raise ValueError('main prefix changed beyond generated identifiers')
    temporaries = checked_bijection(zip(TEMP.findall(old), TEMP.findall(new)), 'temporary')
    strings = checked_bijection(zip(LITERAL.findall(old), LITERAL.findall(new)), 'string')
    results = checked_bijection(zip(RESULT.findall(old), RESULT.findall(new)), 'result local')
    used_results = proof_results() | set(results)
    results = checked_bijection([(name, results.get(name, name)) for name in sorted(used_results)], 'result local')
    old_locals, new_locals = result_locals(old_function), result_locals(new_function)
    for left, right in results.items():
        if left not in old_locals or right not in new_locals or old_locals[left] != new_locals[right]:
            raise ValueError('mapped result local registration or type differs: ' + left + ' -> ' + right)
    used = proof_literals() | set(strings)
    strings = checked_bijection([(name, strings.get(name, name)) for name in sorted(used)], 'string')
    old_globals, new_globals = literal_globals(reference), literal_globals(current)
    for left, right in strings.items():
        if left not in old_globals or right not in new_globals:
            raise ValueError('missing mapped string global: ' + left + ' -> ' + right)
        if old_globals[left] != new_globals[right]:
            raise ValueError('mapped string global type, bytes or flags differ: ' + left + ' -> ' + right)
    mapping = {left: right for left, right in (temporaries | strings | results).items() if left != right}
    if adapt(old, mapping).split() != new.split():
        raise ValueError('main prefix is not the checked identifier renaming')
    return mapping


def adapt(source, mapping):
    def replace(match):
        if match['temporary'] is not None:
            return "_t'" + mapping.get(match['temporary'], match['temporary'])
        if match['result'] is not None:
            return mapping.get(match['result'], match['result'])
        return (match['variable'] or '') + mapping.get(match['literal'], match['literal'])
    return IDENTIFIER.sub(replace, source)


def rebuild(expected):
    modules = consumers()
    profile = modules['main'].profile
    (ROOT / '.tools/reporting/current').mkdir(parents=True, exist_ok=True)
    for name, module in modules.items():
        directory = WORK / name / 'proofs'
        directory.mkdir(parents=True, exist_ok=True)
        # Reuse imported Lean computations; they have no dependency on Main.prog.
        for path in (ROOT / '.tools/m4' / name / 'proofs').glob('*.vo'):
            if path.stem not in module.MODULES and path.stem != 'Main':
                shutil.copy2(path, directory / path.name)
    profile.run([str(ROOT / '.tools/m4/CompCert/clightgen'), '-normalize', '-fstruct-passing',
                 '-dprepro', '-I', 'linux', '-o', '.tools/reporting/current/Main.v', 'native/leancage_m3.c'],
                cwd=ROOT, profile=False)
    preprocessed = ROOT / 'leancage_m3.i'
    if preprocessed.exists():
        preprocessed.replace(ROOT / '.tools/reporting/current/leancage_m3.i')
    current = ROOT / '.tools/reporting/current/Main.v'
    mapping = renaming(gzip.decompress((ROOT / 'assurance/reporting-reference-ast.v.gz').read_bytes()).decode(),
                       current.read_text())
    if mapping != expected['temporary_renaming']:
        raise ValueError('reviewed generated-identifier renaming differs')
    shutil.copyfile(current, WORK / 'main/proofs/Main.v')
    number = WORK / 'main/number'
    number.mkdir(parents=True, exist_ok=True)
    for path in (ROOT / '.tools/m4/main/number').glob('*.v'):
        shutil.copyfile(path, number / path.name)

    def compile_file(path, name):
        result = profile.run(['rocq', 'c', '-q', *flags(modules[name]), str(path)], cwd=path.parent)
        path.with_suffix('.check.log').write_text(result.stdout)

    compile_file(WORK / 'main/proofs/Main.v', 'main')
    for name in ['NumberSlice', *modules['main'].controller.MODULES]:
        compile_file(number / (name + '.v'), 'main')
    for name, module in modules.items():
        for item in module.MODULES:
            path = WORK / name / 'proofs' / (item + '.v')
            path.write_text(adapt((ROOT / 'm4' / name / (item + '.v')).read_text(), mapping))
            compile_file(path, name)
    actual = audit(modules, mapping)
    if actual != expected['declarations']:
        raise ValueError('rebuilt statements or foundations differ')
    targets = [expected['namespaces'][n] + '.' + item for n, m in modules.items() for item in m.MODULES]
    result = profile.run(['rocq', 'check', '-silent', *flags(modules['parent'], checker=True), *targets],
                         cwd=WORK, timeout=300)
    (WORK / 'kernel-check.log').write_text(result.stdout)


def audit(modules, mapping):
    result = {}
    for name, module in modules.items():
        old = json.loads(module.MANIFEST.read_text())['rocq_declarations']
        prefix = next(value for i, value in enumerate(flags(module))
                      if i > 1 and flags(module)[i - 2] == '-Q' and
                      flags(module)[i - 1] == str(WORK / name / 'proofs'))
        imports = ['From LeanImport Require Import Lean.']
        if name in {'main', 'parent'}:
            imports += ['From LeanCagePlan Require Import PlanImport.']
        if name == 'initialization':
            imports += ['From LeanCageValidation Require Import ValidationImport.']
        extra = {'policy': ['BoundsImport'], 'arguments': ['ArgumentsImport'],
                 'digest': ['DigestImport'], 'validation': ['ValidationImport']}.get(name, [])
        imports += ['From ' + prefix + ' Require Import ' + ' '.join(extra + module.MODULES) + '.']
        groups = [(name, old, imports)]
        if name == 'main':
            groups = [('number', [r for r in old if r['name'].startswith('LeanCageMainNumber.')],
                       ['From LeanCageMainNumber Require Import ' +
                        ' '.join(module.controller.MODULES) + '.']),
                      (name, [r for r in old if not r['name'].startswith('LeanCageMainNumber.')], imports)]
        rows = []
        for label, targets, imports in groups:
            query = [*imports, 'Set Printing All.', 'Set Printing Depth 1000000.',
                     'Set Printing Width 1000000.']
            for i, row in enumerate(targets):
                query += [f'Redirect "{label}-type-{i}" Check @{row["name"]}.',
                          f'Redirect "{label}-axioms-{i}" Print Assumptions {row["name"]}.']
            path = WORK / name / 'proofs' / ('Reporting' + label.title() + 'Audit.v')
            path.write_text('\n'.join(query) + '\n')
            module.profile.run(['rocq', 'c', '-q', *flags(module), str(path)], cwd=path.parent)
            for i, row in enumerate(targets):
                statement = (path.parent / f'{label}-type-{i}.out').read_text().strip()
                assumptions = (path.parent / f'{label}-axioms-{i}.out').read_text().strip()
                axioms, uip = modules['main'].bridge.foundations(assumptions)
                if (adapt(row['full_type'], mapping).split() != statement.split() or
                        axioms != row['assumption_names'] or uip != row['definitional_uip']):
                    raise ValueError('statement or foundations changed: ' + row['name'])
                rows.append(dict(row, full_type=statement, transitive_assumptions=assumptions))
        result[name] = rows
    return result
