#!/usr/bin/env python3
"""Replay the actual policy-bound block and strict live-policy interface connection."""
# §AR-m4-controller.bounds: Full propositions, strict checks and immutable prior identities.
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
DIRECTORY = ROOT / 'm4/policy'
WORK = ROOT / '.tools/m4/policy'
MANIFEST = ROOT / 'assurance/m4-policy-bounds-claims.json'
EVIDENCE = ROOT / 'assurance/m4-policy-bounds-evidence.json'
MODULES = ['BoundsStructure', 'BoundsWords', 'BoundsMemory', 'BoundsValues', 'BoundsControl',
           'BoundsSequence', 'BoundsSource', 'BoundsWitnesses', 'BoundsSamples', 'BoundsPredicate',
           'BoundsImportedValues', 'BoundsImported', 'BoundsConnection']
IMPORT_MODULE = 'BoundsImport'
LEAN_MODULES = ['Bounds']
EXPORT_ROOT = 'LeanCageM4.Bounds.nativeBounds'
ENDPOINT = 'LeanCageBounds.BoundsImport.LeanCageM4_Bounds_nativeBounds'
MAIN_ARCHIVES = {
    'assurance/m4-main-input-checkpoint-claims.json': '6c99c40d499cfe0d9ea4db7fbdeedfc7c403294fcc3159a69522b8dba2c7a143',
    'assurance/m4-main-input-checkpoint-evidence.json': '65d809873c37977eebc2fc5f9f449b6dee6f57d53cee4b1313df9a16d58caacf',
}

sys.path.insert(0, str(ROOT / 'm4/main'))
spec = importlib.util.spec_from_file_location('bounds_main_check', ROOT / 'm4/main/check.py')
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
bridge, profile, read, digest = parent.bridge, parent.profile, parent.read, parent.digest


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / p for p in MAIN_ARCHIVES]
    paths += [parent.MANIFEST, parent.EVIDENCE, ROOT / 'docs/reviews/M4-policy-bounds.md']
    return dict(sorted((parent.sources() | {str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def inventory():
    if {p.stem for p in DIRECTORY.glob('*.v')} != {IMPORT_MODULE, *MODULES}:
        raise ValueError('policy-bounds Rocq module inventory differs')
    if {p.stem for p in DIRECTORY.glob('*.lean')} != set(LEAN_MODULES):
        raise ValueError('policy-bounds Lean module inventory differs')
    return [name for module in MODULES for name in parent.proof_names(
        (DIRECTORY / (module + '.v')).read_text(), 'LeanCageBounds.' + module + '.')]


PARENT_KEYS = ['parent', 'frontend', 'frontend_command', 'header_inputs_sha256', 'functions',
               'source_sha256_native', 'adapted_sources_sha256', 'artifact_sha256']


def validate_parent(claims, evidence, actual):
    parent.validate_claims(claims, actual)
    for key in PARENT_KEYS:
        if actual[key] != evidence[key]:
            raise ValueError('preserved complete-helper identity changed: ' + key)


def parent_identity():
    gate = bridge.connection()
    gate.verify_hashes(MAIN_ARCHIVES)
    plan = parent.parent_identity()
    actual, active = read(parent.WORK / 'report.json'), read(parent.EVIDENCE)
    parent.validate_claims(read(parent.MANIFEST), actual)
    parent.validate_claims(read(ROOT / 'assurance/m4-main-input-checkpoint-claims.json'), actual)
    archived = read(ROOT / 'assurance/m4-main-input-checkpoint-evidence.json')
    validate_parent(read(parent.MANIFEST), active, actual)
    validate_parent(read(ROOT / 'assurance/m4-main-input-checkpoint-claims.json'), archived, actual)
    if actual['parent'] != plan or actual['source_sha256'] != parent.sources() or active['source_sha256'] != parent.sources():
        raise ValueError('parent main-input source replay is stale')
    if active['claims_sha256'] != digest(parent.MANIFEST) or active['full_controller_complete'] is not False or active['full_m4_complete'] is not False:
        raise ValueError('parent main-input claim identity or boundary differs')
    gate.verify_hashes(actual['artifact_sha256'], parent.WORK)
    gate.verify_hashes(active['archived_receipts_sha256'])
    parent.verify_inputs(actual['header_inputs_sha256'])
    return {key: actual[key] for key in PARENT_KEYS}


def flags(checker=False, proofs=None):
    return parent.flags(checker=checker) + ['-Q', str(proofs or WORK / 'proofs'), 'LeanCageBounds']


def lean_run(command):
    package = ROOT / 'm3'
    paths = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=package, text=True).strip()
    search = ':'.join([str(WORK / 'modules'), str(parent.plan.WORK / 'modules'), paths])
    return subprocess.run(['lake', 'env', 'env', 'LEAN_PATH=' + search, *command], cwd=package,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=180, check=True)


def lean_inventory():
    query = 'import Bounds\n' + (ROOT / 'scripts/m3_axiom_query.lean').read_text()
    query += '\n#audit_module Bounds\n'
    path = WORK / 'modules/BoundsAudit.lean'
    path.write_text(query)
    rows = [json.loads(line.split('LEANCAGE_AUDIT ', 1)[1])
            for line in lean_run(['lean', str(path)]).stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]
    inventories = [row for row in rows if 'module' in row]
    actual = sorted([row for row in rows if 'name' in row], key=lambda x: x['name'])
    expected = sorted(name for row in inventories for name in row['declarations'])
    if [row['module'] for row in inventories] != LEAN_MODULES or expected != [row['name'] for row in actual] or not actual:
        raise ValueError('incomplete Lean policy-bounds inventory')
    for row in actual:
        if not row['is_theorem'] or set(row['axioms']) - bridge.ALLOWED_LEAN or '...' in row['type'] or '⋯' in row['type']:
            raise ValueError('unreviewed Lean policy-bounds statement/foundation')
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
        raise ValueError('unexpected bounds export version')
    if any(d['kind'] == 'axiom' for d in declarations):
        raise ValueError('computational bounds closure contains an axiom')
    if {'name': EXPORT_ROOT, 'kind': 'def'} not in declarations:
        raise ValueError('missing bounds computational root')
    if any(d['name'] in {'Nat.mod', 'Nat.div', 'Iff'} or d['name'].split('.')[0] in {'String', 'Char', 'UInt32'} for d in declarations):
        raise ValueError('unreviewed closure in normalized bounds import')
    return {'metadata': metadata, 'declarations': declarations}


def validate_claims(expected, actual):
    for key in ['rocq_declarations', 'lean_declarations', 'imported_endpoint', 'export_inventory']:
        if not actual[key] or expected[key] != actual[key]:
            raise ValueError('reviewed bounds statement/foundation/export inventory differs: ' + key)


def negative_structure():
    negative = WORK / 'negative'
    negative.mkdir(exist_ok=True)
    source = (DIRECTORY / 'BoundsStructure.v').read_text()
    old = 'Build_policy_guard _memory 0 upper 1073741824'
    if source.count(old) != 1:
        raise ValueError('ambiguous bounds negative mutation')
    path = negative / 'BoundsStructure.v'
    path.write_text(source.replace(old, 'Build_policy_guard _memory 0 upper 1073741825'))
    try:
        profile.run(['rocq', 'c', '-q', *flags(proofs=negative), str(path)], cwd=negative)
    except subprocess.CalledProcessError as error:
        if 'Unable to unify' not in error.stdout:
            raise ValueError('negative bounds identity failed for an unexpected reason: ' + error.stdout)
        return error.stdout
    raise ValueError('kernel accepted changed bounds descriptors')


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
    export_path = WORK / 'bounds.ndjson'
    export_path.write_text(lean_run([str(profile.WORK / 'lean4export/.lake/build/bin/lean4export'), 'Bounds', '--', EXPORT_ROOT]).stdout)
    exported_inventory = export_inventory(export_path)
    modules = [IMPORT_MODULE, *MODULES]
    for module in modules:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=path.parent).stdout
    negative = WORK / 'proofs/GuardDisabled.v'
    negative.write_text('From LeanImport Require Import Lean.\nUnset Guard Checking.\n'
                        'Set Lean Error Mode "Fail".\nUnset Lean Skip Missing Quotient.\n'
                        'Lean Import "../bounds.ndjson".\n')
    try:
        profile.run(['rocq', 'c', '-q', *flags(), str(negative)], cwd=negative.parent)
    except subprocess.CalledProcessError as error:
        if 'M4 strict bridge requires all kernel typing checks' not in error.stdout:
            raise ValueError('negative bounds import failed for an unexpected reason: ' + error.stdout)
        logs['guard_rejection'] = error.stdout
    else:
        raise ValueError('strict bounds importer accepted disabled guardedness')
    logs['structure_rejection'] = negative_structure()
    query = ['From LeanImport Require Import Lean.', 'From LeanCageBounds Require Import ' + ' '.join(modules) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    targets = [ENDPOINT, *names]
    for i, name in enumerate(targets):
        query += [f'Redirect "bounds-type-{i}" Check @{name}.',
                  f'Redirect "bounds-foundations-{i}" Print Assumptions {name}.']
    audit = WORK / 'proofs/BoundsAudit.v'
    audit.write_text('\n'.join(query) + '\n')
    logs['audit'] = profile.run(['rocq', 'c', '-q', *flags(), str(audit)], cwd=audit.parent).stdout
    records = []
    imported = {'BoundsImportedValues', 'BoundsImported', 'BoundsConnection'}
    for i, name in enumerate(targets):
        statement = (audit.parent / f'bounds-type-{i}.out').read_text().strip()
        assumptions = (audit.parent / f'bounds-foundations-{i}.out').read_text().strip()
        axioms, uip = bridge.foundations(assumptions)
        if '...' in statement or (uip and i and name.split('.')[1] not in imported):
            raise ValueError('truncated statement or unreviewed bounds logical model')
        records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                        'assumption_names': axioms, 'definitional_uip': uip})
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True),
                          *['LeanCageBounds.' + m for m in modules]], cwd=WORK, timeout=300)
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/policy', '-p', 'test_gate.py', '-v'],
                           cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30)
    logs['gate_tests'] = tests.stdout
    if before != sources() or previous != parent_identity():
        raise ValueError('bounds sources or parent changed during replay')
    artifacts = [WORK / 'proofs' / (m + '.vo') for m in modules]
    artifacts += [WORK / 'modules' / (m + '.olean') for m in LEAN_MODULES]
    report = {'schema_version': 1, 'source_sha256': before, 'parent': previous,
              'rocq_declarations': records[1:], 'imported_endpoint': records[0],
              'lean_declarations': lean, 'export_inventory': exported_inventory, 'export_sha256': digest(export_path),
              'artifact_sha256': {str(p.relative_to(WORK)): digest(p) for p in artifacts},
              'kernel_output': kernel.stdout, 'logs': logs,
              'elapsed_seconds': round(time.monotonic() - started, 3)}
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Bounds replay passed: {len(names)} Rocq and {len(lean)} Lean full records; strict import, actual AST and kernel checks.', flush=True)
    return report


def check():
    claims, evidence = read(MANIFEST), read(EVIDENCE)
    bridge.connection().verify_hashes(evidence['archived_receipts_sha256'])
    if evidence['claims_sha256'] != digest(MANIFEST) or evidence['full_controller_complete'] is not False or evidence['full_m4_complete'] is not False:
        raise ValueError('bounds claim identity or boundary differs')
    actual = collect()
    validate_claims(claims, actual)
    for key in ['source_sha256', 'parent', 'artifact_sha256', 'export_sha256']:
        if evidence[key] != actual[key]:
            raise ValueError('reviewed bounds identity differs: ' + key)
    archived = json.loads(gzip.decompress((ROOT / 'assurance/m4-policy-bounds-proof-output.json.gz').read_bytes()))
    validate_claims(archived, actual)
    for key in ['artifact_sha256', 'export_sha256', 'parent', 'kernel_output']:
        if archived[key] != actual[key]:
            raise ValueError('archived bounds proof identity differs: ' + key)
    print('Reviewed bounds statements, foundations, artifacts and prior main-input identities match.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collect', action='store_true', help='write ignored candidate output; never refresh reviewed manifests')
    args = parser.parse_args()
    collect() if args.collect else check()
