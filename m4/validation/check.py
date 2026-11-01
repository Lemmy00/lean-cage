#!/usr/bin/env python3
"""Replay the actual caller string checks and strict live plan connection."""
# §AR-m4-controller.strings: Full propositions, strict checks and immutable prior identities.
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / 'm4/validation'
WORK = ROOT / '.tools/m4/validation'
MANIFEST = ROOT / 'assurance/m4-validation-claims.json'
EVIDENCE = ROOT / 'assurance/m4-validation-evidence.json'
MODULES = ['StringRegion', 'ValidationStructure', 'ValidationMemory', 'ValidationValues', 'ValidationCalls', 'ValidationFinish', 'DigestCaller', 'ExportCaller', 'ExecutableCaller', 'ModeCaller', 'ValidationComposition', 'ValidationAllocation', 'ValidationWitnesses', 'ValidationSamples', 'ValidationInterruptions', 'StringSource', 'StringImported', 'StringConnection']
IMPORT_MODULE = 'ValidationImport'
LEAN_MODULES = ['Validation']
EXPORT_ROOT = 'LeanCageM4.Validation.nativeStringCheck'
ENDPOINT = 'LeanCageValidation.ValidationImport.LeanCageM4_Validation_nativeStringCheck'
PARENT_ARCHIVES = {'assurance/m4-digest-checkpoint-claims.json': 'b98f379940fa8b36b6d1d24bd725a3b15e5a86148e9e1bebb66eec02ed3b803c', 'assurance/m4-digest-checkpoint-evidence.json': '88ae00e472ebdf4611fe080c0d32b6502de13094b8b59b307b9bfd0014de6e4d'}

sys.path.insert(0, str(ROOT / 'm4/digest'))
spec = importlib.util.spec_from_file_location('validation_digest_check', ROOT / 'm4/digest/check.py')
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
bridge, profile, read, digest = parent.bridge, parent.profile, parent.read, parent.digest
proof_names = parent.proof_names


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / p for p in PARENT_ARCHIVES]
    paths += [parent.MANIFEST, parent.EVIDENCE, ROOT / 'docs/reviews/M4-validation.md']
    return dict(sorted((parent.sources() | {str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def inventory():
    if {p.stem for p in DIRECTORY.glob('*.v')} != {IMPORT_MODULE, *MODULES}:
        raise ValueError('caller-string Rocq module inventory differs')
    if {p.stem for p in DIRECTORY.glob('*.lean')} != set(LEAN_MODULES):
        raise ValueError('caller-string Lean module inventory differs')
    return [name for module in MODULES for name in proof_names(
        (DIRECTORY / (module + '.v')).read_text(), 'LeanCageValidation.' + module + '.')]


PARENT_KEYS = ['parent', 'artifact_sha256', 'export_sha256']


def validate_parent(claims, evidence, actual):
    parent.validate_claims(claims, actual)
    for key in PARENT_KEYS:
        if actual[key] != evidence[key]:
            raise ValueError('preserved digest-recognizer identity changed: ' + key)


def parent_identity():
    gate = bridge.connection()
    gate.verify_hashes(PARENT_ARCHIVES)
    main = parent.parent_identity()
    actual, active = read(parent.WORK / 'report.json'), read(parent.EVIDENCE)
    archived = read(ROOT / 'assurance/m4-digest-checkpoint-evidence.json')
    validate_parent(read(parent.MANIFEST), active, actual)
    validate_parent(read(ROOT / 'assurance/m4-digest-checkpoint-claims.json'), archived, actual)
    if actual['parent'] != main or actual['source_sha256'] != parent.sources() or active['source_sha256'] != parent.sources():
        raise ValueError('parent digest-recognizer source replay is stale')
    if active['claims_sha256'] != digest(parent.MANIFEST) or active['full_controller_complete'] is not False or active['full_m4_complete'] is not False:
        raise ValueError('parent digest claim identity or boundary differs')
    gate.verify_hashes(actual['artifact_sha256'], parent.WORK)
    gate.verify_hashes(active['archived_receipts_sha256'])
    if digest(parent.WORK / 'digest.ndjson') != actual['export_sha256']:
        raise ValueError('parent digest imported bytes changed')
    return {key: actual[key] for key in PARENT_KEYS}


def flags(checker=False, proofs=None):
    return parent.flags(checker=checker) + ['-Q', str(proofs or WORK / 'proofs'), 'LeanCageValidation']


def lean_run(command):
    paths = parent.lean_run(['printenv', 'LEAN_PATH']).stdout.strip()
    return parent.lean_run(['env', 'LEAN_PATH=' + str(WORK / 'modules') + ':' + paths, *command])


def lean_inventory():
    query = 'import Validation\n' + (ROOT / 'scripts/m3_axiom_query.lean').read_text()
    query += '\nset_option pp.all true\nset_option pp.proofs true\n#audit_module Validation\n'
    path = WORK / 'modules/ValidationAudit.lean'
    path.write_text(query)
    rows = [json.loads(line.split('LEANCAGE_AUDIT ', 1)[1])
            for line in lean_run(['lean', str(path)]).stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]
    inventories = [row for row in rows if 'module' in row]
    actual = sorted([row for row in rows if 'name' in row], key=lambda x: x['name'])
    expected = sorted(name for row in inventories for name in row['declarations'])
    if [row['module'] for row in inventories] != LEAN_MODULES or expected != [row['name'] for row in actual] or not actual:
        raise ValueError('incomplete Lean caller-string inventory')
    for row in actual:
        if not row['is_theorem'] or set(row['axioms']) - bridge.ALLOWED_LEAN or '...' in row['type'] or '⋯' in row['type']:
            raise ValueError('unreviewed Lean caller-string statement/foundation')
    return actual


def export_inventory(path):
    names, declarations, metadata = {0: ''}, [], None
    for line in path.read_text().splitlines():
        row = json.loads(line)
        if 'meta' in row:
            metadata = row['meta']
        if 'in' in row:
            value = row.get('str') or row.get('num')
            names[row['in']] = (names[value['pre']] + '.' if value['pre'] else '') + str(value.get('str', value.get('i')))
        for kind in ['def', 'thm', 'opaque', 'axiom']:
            if kind in row:
                declarations.append({'name': names[row[kind]['name']], 'kind': kind})
        if 'inductive' in row:
            declarations += [{'name': names[item['name']], 'kind': kind}
                             for kind in ['types', 'ctors', 'recs'] for item in row['inductive'][kind]]
    if not metadata or metadata['lean']['version'] != '4.35.0':
        raise ValueError('unexpected caller-string export version')
    if any(d['kind'] == 'axiom' for d in declarations):
        raise ValueError('computational caller-string closure contains an axiom')
    if {'name': EXPORT_ROOT, 'kind': 'def'} not in declarations:
        raise ValueError('missing caller-string computational root')
    if any(d['name'] in {'Nat.mod', 'Nat.div', 'Iff'} or d['name'].split('.')[0] in {'String', 'Char', 'Array', 'ByteArray', 'UInt8', 'UInt32'} for d in declarations):
        raise ValueError('unreviewed closure in normalized caller-string import')
    return {'metadata': metadata, 'declarations': declarations}


def validate_claims(expected, actual):
    for key in ['rocq_declarations', 'lean_declarations', 'imported_endpoint', 'export_inventory']:
        if not actual[key] or expected[key] != actual[key]:
            raise ValueError('reviewed caller-string statement/foundation/export inventory differs: ' + key)


def negative_structure():
    negative = WORK / 'negative-count'
    negative.mkdir(exist_ok=True)
    source = (DIRECTORY / 'ValidationStructure.v').read_text()
    old = 'Econst_int(Int.repr 17)tint'
    if source.count(old) != 1:
        raise ValueError('ambiguous caller count mutation')
    path = negative / 'ValidationStructure.v'
    path.write_text(source.replace(old, 'Econst_int(Int.repr 16)tint'))
    try:
        profile.run(['rocq', 'c', '-q', *flags(proofs=negative), str(path)], cwd=negative)
    except subprocess.CalledProcessError as error:
        if 'Unable to unify' not in error.stdout:
            raise ValueError('negative count identity failed unexpectedly: ' + error.stdout)
        return error.stdout
    raise ValueError('kernel accepted altered caller count identity')


def negative_literal_memory():
    negative = WORK / 'negative-literal'
    negative.mkdir(exist_ok=True)
    structure = negative / 'ValidationStructure.v'
    memory = negative / 'ValidationMemory.v'
    source = (DIRECTORY / structure.name).read_text()
    memory.write_bytes((DIRECTORY / memory.name).read_bytes())
    old = '112;121;116;104;111;110;51]'
    if source.count(old) != 1:
        raise ValueError('ambiguous Python literal mutation')
    structure.write_text(source)
    for path in [structure, memory]:
        profile.run(['rocq', 'c', '-q', *flags(proofs=negative), str(path)], cwd=negative)
    structure.write_text(source.replace(old, '112;121;116;104;111;110;52]'))
    profile.run(['rocq', 'c', '-q', *flags(proofs=negative), str(structure)], cwd=negative)
    try:
        profile.run(['rocq', 'c', '-q', *flags(proofs=negative), str(memory)], cwd=negative)
    except subprocess.CalledProcessError as error:
        if not all(token in error.stdout for token in ['The term \"LOAD\" has type', 'while it is expected to have type', 'python_bytes', '___stringlit_134']):
            raise ValueError('negative initial-memory literal failed unexpectedly: ' + error.stdout)
        return error.stdout
    raise ValueError('kernel accepted altered bytes for actual initialized Python literal')


def collect():
    started = time.monotonic()
    profile.verify_tools()
    names, before, previous = inventory(), sources(), parent_identity()
    for folder in ['modules', 'proofs']:
        (WORK / folder).mkdir(parents=True, exist_ok=True)
    logs = {}
    for module in LEAN_MODULES:
        path = WORK / 'modules' / (module + '.lean')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = lean_run(['lean', '-R', str(path.parent), '-o', str(path.with_suffix('.olean')), str(path)]).stdout
    lean = lean_inventory()
    export_path = WORK / 'validation.ndjson'
    export_path.write_text(lean_run([str(profile.WORK / 'lean4export/.lake/build/bin/lean4export'), 'Validation', '--', EXPORT_ROOT]).stdout)
    exported_inventory = export_inventory(export_path)
    modules = [IMPORT_MODULE, *MODULES]
    for module in modules:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=path.parent).stdout
    negative = WORK / 'proofs/GuardDisabled.v'
    negative.write_text('From LeanImport Require Import Lean.\nUnset Guard Checking.\n'
                        'Set Lean Error Mode "Fail".\nUnset Lean Skip Missing Quotient.\n'
                        'Lean Import "../validation.ndjson".\n')
    try:
        profile.run(['rocq', 'c', '-q', *flags(), str(negative)], cwd=negative.parent)
    except subprocess.CalledProcessError as error:
        if 'M4 strict bridge requires all kernel typing checks' not in error.stdout:
            raise ValueError('negative caller-string import failed for an unexpected reason: ' + error.stdout)
        logs['guard_rejection'] = error.stdout
    else:
        raise ValueError('strict caller-string importer accepted disabled guardedness')
    logs['structure_rejection'] = negative_structure()
    logs['literal_memory_rejection'] = negative_literal_memory()
    query = ['From LeanImport Require Import Lean.', 'From LeanCageValidation Require Import ' + ' '.join(modules) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    targets = [ENDPOINT, *names]
    for i, name in enumerate(targets):
        query += [f'Redirect "validation-type-{i}" Check @{name}.',
                  f'Redirect "validation-foundations-{i}" Print Assumptions {name}.']
    audit = WORK / 'proofs/ValidationAudit.v'
    audit.write_text('\n'.join(query) + '\n')
    logs['audit'] = profile.run(['rocq', 'c', '-q', *flags(), str(audit)], cwd=audit.parent).stdout
    records = []
    imported = {'StringImported', 'StringConnection'}
    for i, name in enumerate(targets):
        statement = (audit.parent / f'validation-type-{i}.out').read_text().strip()
        assumptions = (audit.parent / f'validation-foundations-{i}.out').read_text().strip()
        axioms, uip = bridge.foundations(assumptions)
        if '...' in statement or (uip and i and name.split('.')[1] not in imported):
            raise ValueError('truncated statement or unreviewed caller-string logical model')
        records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                        'assumption_names': axioms, 'definitional_uip': uip})
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True),
                          *['LeanCageValidation.' + m for m in modules]], cwd=WORK, timeout=300)
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/validation', '-p', 'test_gate.py', '-v'],
                           cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30)
    logs['gate_tests'] = tests.stdout
    if before != sources() or previous != parent_identity():
        raise ValueError('caller-string sources or parent changed during replay')
    artifacts = [WORK / 'proofs' / (m + '.vo') for m in modules]
    artifacts += [WORK / 'modules' / (m + '.olean') for m in LEAN_MODULES]
    report = {'schema_version': 1, 'source_sha256': before, 'parent': previous,
              'rocq_declarations': records[1:], 'imported_endpoint': records[0],
              'lean_declarations': lean, 'export_inventory': exported_inventory, 'export_sha256': digest(export_path),
              'artifact_sha256': {str(p.relative_to(WORK)): digest(p) for p in artifacts},
              'kernel_output': kernel.stdout, 'logs': logs,
              'elapsed_seconds': round(time.monotonic() - started, 3)}
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Caller-string replay passed: {len(names)} Rocq and {len(lean)} Lean full records; strict import, actual AST and kernel checks.', flush=True)
    return report


def check():
    claims, evidence = read(MANIFEST), read(EVIDENCE)
    bridge.connection().verify_hashes(evidence['archived_receipts_sha256'])
    if evidence['claims_sha256'] != digest(MANIFEST) or evidence['full_controller_complete'] is not False or evidence['full_m4_complete'] is not False:
        raise ValueError('caller-string claim identity or boundary differs')
    actual = collect()
    validate_claims(claims, actual)
    for key in ['source_sha256', 'parent', 'artifact_sha256', 'export_sha256']:
        if evidence[key] != actual[key]:
            raise ValueError('reviewed caller-string identity differs: ' + key)
    archived = json.loads(gzip.decompress((ROOT / 'assurance/m4-validation-proof-output.json.gz').read_bytes()))
    validate_claims(archived, actual)
    for key in ['artifact_sha256', 'export_sha256', 'parent', 'kernel_output']:
        if archived[key] != actual[key]:
            raise ValueError('archived caller-string proof identity differs: ' + key)
    print('Reviewed caller-string statements, foundations, artifacts and prior digest-recognizer identities match.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collect', action='store_true', help='write ignored candidate output; never refresh reviewed manifests')
    args = parser.parse_args()
    collect() if args.collect else check()
