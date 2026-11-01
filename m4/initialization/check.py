#!/usr/bin/env python3
"""Replay actual initialization stores and their sequential validation composition."""
# §AR-m4-controller.initialization: Preserve complete claims and every prior checkpoint.
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / 'm4/initialization'
WORK = ROOT / '.tools/m4/initialization'
MANIFEST = ROOT / 'assurance/m4-initialization-claims.json'
EVIDENCE = ROOT / 'assurance/m4-initialization-evidence.json'
MODULES = ['AssemblyRegions', 'FlagStores', 'PointerStores', 'ModeInitialization',
           'StoreFrames', 'ConfigurationMemory', 'ConfigurationSource', 'ExportConfiguration',
           'ArgumentsInitialization', 'DigestArguments', 'InitializationSource',
           'InitializationAllocation', 'InitializationWitnesses', 'InitializationSamples',
           'ModeWitnesses', 'FlagConnection', 'ConfigurationStages', 'InitializationMemory',
           'InterruptionWitnesses']
LEAN_MODULES = ['Initialization']
ENDPOINTS = ['LeanCageValidation.ValidationImport.LeanCageM4_Validation_' + name
             for name in ['bytesEq', 'checkBytes', 'filesBytes']]
PARENT_ARCHIVES = {'assurance/m4-validation-checkpoint-claims.json': 'e6bba0a369b71aec19497e9421813d73fa1f66fad19c21a27737fbb82f323442', 'assurance/m4-validation-checkpoint-evidence.json': '177e355f4ad78bd989785b65d5d41a9bb6349350a1fbeeb66901e6c6dbfc9b76'}

spec = importlib.util.spec_from_file_location('initialization_validation_check', ROOT / 'm4/validation/check.py')
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
bridge, profile, read, digest = parent.bridge, parent.profile, parent.read, parent.digest
proof_names = parent.proof_names
PARENT_KEYS = ['parent', 'artifact_sha256', 'export_sha256']


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / p for p in PARENT_ARCHIVES]
    paths += [parent.MANIFEST, parent.EVIDENCE, ROOT / 'docs/reviews/M4-initialization.md']
    return dict(sorted((parent.sources() | {str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def inventory():
    if {p.stem for p in DIRECTORY.glob('*.v')} != set(MODULES):
        raise ValueError('initialization Rocq module inventory differs')
    if {p.stem for p in DIRECTORY.glob('*.lean')} != set(LEAN_MODULES):
        raise ValueError('initialization Lean module inventory differs')
    return [name for module in MODULES for name in proof_names(
        (DIRECTORY / (module + '.v')).read_text(), 'LeanCageInitialization.' + module + '.')]


def validate_parent(claims, evidence, actual):
    parent.validate_claims(claims, actual)
    for key in PARENT_KEYS:
        if actual[key] != evidence[key]:
            raise ValueError('preserved caller-string identity changed: ' + key)


def parent_identity():
    gate = bridge.connection()
    gate.verify_hashes(PARENT_ARCHIVES)
    previous = parent.parent_identity()
    actual, active = read(parent.WORK / 'report.json'), read(parent.EVIDENCE)
    archived = read(ROOT / 'assurance/m4-validation-checkpoint-evidence.json')
    validate_parent(read(parent.MANIFEST), active, actual)
    validate_parent(read(ROOT / 'assurance/m4-validation-checkpoint-claims.json'), archived, actual)
    if actual['parent'] != previous or actual['source_sha256'] != parent.sources() or active['source_sha256'] != parent.sources():
        raise ValueError('parent caller-string replay is stale')
    if active['claims_sha256'] != digest(parent.MANIFEST) or active['full_controller_complete'] is not False or active['full_m4_complete'] is not False:
        raise ValueError('parent caller-string identity or boundary differs')
    gate.verify_hashes(actual['artifact_sha256'], parent.WORK)
    gate.verify_hashes(active['archived_receipts_sha256'])
    if digest(parent.WORK / 'validation.ndjson') != actual['export_sha256']:
        raise ValueError('strict imported caller-string bytes changed')
    return {key: actual[key] for key in PARENT_KEYS}


def flags(checker=False, proofs=None):
    # The canonical directory supplies unmutated dependencies for each negative control.
    result = parent.flags(checker=checker) + ['-Q', str(WORK / 'proofs'), 'LeanCageInitialization']
    return result + (['-Q', str(proofs), 'LeanCageInitialization'] if proofs else [])


def lean_run(command):
    paths = parent.lean_run(['printenv', 'LEAN_PATH']).stdout.strip()
    return parent.lean_run(['env', 'LEAN_PATH=' + str(WORK / 'modules') + ':' + paths, *command])


def lean_inventory():
    query = 'import Initialization\n' + (ROOT / 'scripts/m3_axiom_query.lean').read_text()
    query += '\nset_option pp.all true\nset_option pp.proofs true\n#audit_module Initialization\n'
    path = WORK / 'modules/InitializationAudit.lean'
    path.write_text(query)
    rows = [json.loads(line.split('LEANCAGE_AUDIT ', 1)[1])
            for line in lean_run(['lean', str(path)]).stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]
    inventories = [row for row in rows if 'module' in row]
    actual = sorted([row for row in rows if 'name' in row], key=lambda x: x['name'])
    expected = sorted(name for row in inventories for name in row['declarations'])
    if [row['module'] for row in inventories] != LEAN_MODULES or expected != [row['name'] for row in actual] or not actual:
        raise ValueError('incomplete Lean initialization inventory')
    for row in actual:
        if not row['is_theorem'] or set(row['axioms']) - bridge.ALLOWED_LEAN or '...' in row['type'] or '⋯' in row['type']:
            raise ValueError('unreviewed Lean initialization statement/foundation')
    return actual


def validate_claims(expected, actual):
    for key in ['rocq_declarations', 'lean_declarations', 'imported_endpoints', 'export_inventory']:
        if not actual[key] or expected[key] != actual[key]:
            raise ValueError('reviewed initialization statement/foundation/export differs: ' + key)


def negative_source(module, old, new, name):
    negative = WORK / name
    negative.mkdir(exist_ok=True)
    source = (DIRECTORY / (module + '.v')).read_text()
    if source.count(old) != 1:
        raise ValueError('ambiguous initialization mutation: ' + name)
    path = negative / (module + '.v')
    path.write_text(source.replace(old, new))
    try:
        profile.run(['rocq', 'c', '-q', *flags(proofs=negative), str(path)], cwd=negative)
    except subprocess.CalledProcessError as error:
        if 'Unable to unify' not in error.stdout:
            raise ValueError('initialization mutation failed unexpectedly: ' + error.stdout)
        return error.stdout
    raise ValueError('kernel accepted altered actual initialization: ' + name)


def negative_rollback():
    negative = WORK / 'negative-rollback'
    negative.mkdir(exist_ok=True)
    source = '''From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import ValidationStructure.
Open Scope Z_scope.
Lemma actual_preflight_write before after :
 Mem.store Mint32 before(symbol_block _preflight)0(Vint Int.one)=Some after->
 Mem.load Mint32 after(symbol_block _preflight)0=Some(Vint Int.one).
Proof. intros STORE;rewrite(Mem.load_store_same _ _ _ _ _ _ STORE);reflexivity. Qed.
'''
    path = negative / 'Rollback.v'
    path.write_text(source)
    profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=negative)
    path.write_text(source.replace('=Some(Vint Int.one).', '=Some(Vint Int.zero).'))
    try:
        profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=negative)
    except subprocess.CalledProcessError as error:
        if 'Unable to unify' not in error.stdout:
            raise ValueError('rollback mutation failed unexpectedly: ' + error.stdout)
        return error.stdout
    raise ValueError('kernel accepted rollback of an actual preflight store')


def compile_proofs():
    names = inventory()
    for folder in ['modules', 'proofs']:
        (WORK / folder).mkdir(parents=True, exist_ok=True)
    logs = {}
    for module in LEAN_MODULES:
        path = WORK / 'modules' / (module + '.lean')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = lean_run(['lean', '-R', str(path.parent), '-o', str(path.with_suffix('.olean')), str(path)]).stdout
    lean = lean_inventory()
    for module in MODULES:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=path.parent).stdout
    logs['flag_rejection'] = negative_source('FlagStores',
        'selection_check 3=flag_statement _t\'294 1 _t\'7 ___stringlit_130 9 preflight_target',
        'selection_check 3=flag_statement _t\'294 1 _t\'7 ___stringlit_131 9 preflight_target', 'negative-flag')
    logs['argument_pointer_rejection'] = negative_source('PointerStores',
        '(Econst_int(Int.repr 16)tint)', '(Econst_int(Int.repr 15)tint)', 'negative-pointer')
    logs['rollback_rejection'] = negative_rollback()
    query = ['From LeanImport Require Import Lean.',
             'From LeanCageValidation Require Import ValidationImport.',
             'From LeanCageInitialization Require Import ' + ' '.join(MODULES) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    targets = [*ENDPOINTS, *names]
    for i, name in enumerate(targets):
        query += [f'Redirect "initialization-type-{i}" Check @{name}.',
                  f'Redirect "initialization-foundations-{i}" Print Assumptions {name}.']
    audit = WORK / 'proofs/InitializationAudit.v'
    audit.write_text('\n'.join(query) + '\n')
    logs['audit'] = profile.run(['rocq', 'c', '-q', *flags(), str(audit)], cwd=audit.parent).stdout
    records = []
    for i, name in enumerate(targets):
        statement = (audit.parent / f'initialization-type-{i}.out').read_text().strip()
        assumptions = (audit.parent / f'initialization-foundations-{i}.out').read_text().strip()
        axioms, uip = bridge.foundations(assumptions)
        if '...' in statement or (uip and i >= len(ENDPOINTS) and name.split('.')[1] != 'FlagConnection'):
            raise ValueError('truncated statement or unreviewed initialization logical model')
        records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                        'assumption_names': axioms, 'definitional_uip': uip})
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True),
                          *['LeanCageInitialization.' + m for m in MODULES]], cwd=WORK, timeout=300)
    artifacts = [WORK / 'proofs' / (m + '.vo') for m in MODULES]
    artifacts += [WORK / 'modules' / (m + '.olean') for m in LEAN_MODULES]
    return {'rocq_declarations': records[len(ENDPOINTS):], 'imported_endpoints': records[:len(ENDPOINTS)],
            'lean_declarations': lean, 'artifact_sha256': {str(p.relative_to(WORK)): digest(p) for p in artifacts},
            'kernel_output': kernel.stdout, 'logs': logs}


def collect():
    started = time.monotonic()
    profile.verify_tools()
    before, previous = sources(), parent_identity()
    report = compile_proofs()
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/initialization', '-p', 'test_gate.py', '-v'],
                           cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30)
    report['logs']['gate_tests'] = tests.stdout
    exported = parent.export_inventory(parent.WORK / 'validation.ndjson')
    if exported != read(parent.MANIFEST)['export_inventory']:
        raise ValueError('reviewed strict caller-string export differs')
    if before != sources() or previous != parent_identity():
        raise ValueError('initialization sources or parent changed during replay')
    report.update(schema_version=1, source_sha256=before, parent=previous,
                  export_inventory=exported, export_sha256=digest(parent.WORK / 'validation.ndjson'),
                  elapsed_seconds=round(time.monotonic() - started, 3))
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Initialization replay passed: {len(report["rocq_declarations"])} Rocq and {len(report["lean_declarations"])} Lean full records; actual stores, strict imported flags and kernel checks.', flush=True)
    return report


def check():
    claims, evidence = read(MANIFEST), read(EVIDENCE)
    bridge.connection().verify_hashes(evidence['archived_receipts_sha256'])
    if evidence['claims_sha256'] != digest(MANIFEST) or evidence['full_controller_complete'] is not False or evidence['full_m4_complete'] is not False:
        raise ValueError('initialization claim identity or boundary differs')
    actual = collect()
    validate_claims(claims, actual)
    for key in ['source_sha256', 'parent', 'artifact_sha256', 'export_sha256']:
        if evidence[key] != actual[key]:
            raise ValueError('reviewed initialization identity differs: ' + key)
    archived = json.loads(gzip.decompress((ROOT / 'assurance/m4-initialization-proof-output.json.gz').read_bytes()))
    validate_claims(archived, actual)
    for key in ['artifact_sha256', 'export_sha256', 'parent', 'kernel_output']:
        if archived[key] != actual[key]:
            raise ValueError('archived initialization identity differs: ' + key)
    print('Reviewed initialization statements, foundations, artifacts and prior caller-string identities match.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collect', action='store_true', help='write ignored candidates; never refresh reviewed manifests')
    args = parser.parse_args()
    collect() if args.collect else check()
