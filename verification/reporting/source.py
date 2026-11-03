"""Replay source consumers after the reporting collector correction.

The original proof sources and snapshots remain historical inputs. Only generated
temporary identifiers are adapted; every adapted term is checked against the
current complete-helper AST. A matching checked cache needs no rebuild.
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


def renaming(reference, current):
    pattern = r'Definition f_main :=.*?^\|\}\.'
    old = re.search(pattern, reference, re.S | re.M)[0]
    new = re.search(pattern, current, re.S | re.M)[0]
    # The collector calls follow every previously accepted input/history frontier.
    old = old[old.index('fn_body :='):old.index('(Evar _capture')]
    new = new[new.index('fn_body :='):new.index('(Evar _capture')]
    if TEMP.sub('_TEMP', old).split() != TEMP.sub('_TEMP', new).split():
        raise ValueError('main prefix changed beyond generated temporary names')
    mapping = {}
    for left, right in zip(TEMP.findall(old), TEMP.findall(new)):
        if left in mapping and mapping[left] != right:
            raise ValueError('inconsistent temporary renaming')
        mapping[left] = right
    if len(set(mapping.values())) != len(mapping):
        raise ValueError('temporary renaming is not injective')
    return {left: right for left, right in mapping.items() if left != right}


def adapt(source, mapping):
    return TEMP.sub(lambda match: "_t'" + mapping.get(match[1], match[1]), source)


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
                 '-dprepro', '-o', '.tools/reporting/current/Main.v', 'native/leancage_m3.c'],
                cwd=ROOT, profile=False)
    preprocessed = ROOT / 'leancage_m3.i'
    if preprocessed.exists():
        preprocessed.replace(ROOT / '.tools/reporting/current/leancage_m3.i')
    current = ROOT / '.tools/reporting/current/Main.v'
    mapping = renaming(gzip.decompress((ROOT / 'assurance/reporting-reference-ast.v.gz').read_bytes()).decode(),
                       current.read_text())
    if mapping != expected['temporary_renaming']:
        raise ValueError('reviewed temporary renaming differs')
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
