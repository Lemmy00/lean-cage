#!/usr/bin/env python3
"""Replay the actual digest recognizer and strict live policy digest connection."""
# §AR-m4-controller.digest: Full propositions, strict checks and immutable prior identities.
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
DIRECTORY = ROOT / 'm4/digest'
WORK = ROOT / '.tools/m4/digest'
MANIFEST = ROOT / 'assurance/m4-digest-claims.json'
EVIDENCE = ROOT / 'assurance/m4-digest-evidence.json'
MODULES = ['StringControl', 'DigestWords', 'DigestStructure', 'DigestMemory',
           'DigestValues', 'DigestCharacter', 'DigestControl', 'DigestLoop',
           'DigestEntry', 'DigestSource', 'DigestWitnesses', 'DigestSamples',
           'DigestImported', 'DigestConnection']
IMPORT_MODULE = 'DigestImport'
LEAN_MODULES = ['Digest']
EXPORT_ROOT = 'LeanCageM4.Digest.nativeDigestBytes'
ENDPOINT = 'LeanCageDigest.DigestImport.LeanCageM4_Digest_nativeDigestBytes'
PARENT_ARCHIVES = {'assurance/m4-arguments-checkpoint-claims.json': 'e6bae6942949cd744ed8c2ab344d31b29804d01d690be003ca0a7f2ee837a392', 'assurance/m4-arguments-checkpoint-evidence.json': 'fe461a6144fc2ace990f06e58f484e77f32f8e60234b85724a46398284a522a6'}

sys.path.insert(0, str(ROOT / 'm4/arguments'))
spec = importlib.util.spec_from_file_location('digest_arguments_check', ROOT / 'm4/arguments/check.py')
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
bridge, profile, read, digest = parent.bridge, parent.profile, parent.read, parent.digest
proof_names = parent.parent.parent.proof_names


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / p for p in PARENT_ARCHIVES]
    paths += [parent.MANIFEST, parent.EVIDENCE, ROOT / 'docs/reviews/M4-digest.md']
    return dict(sorted((parent.sources() | {str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def inventory():
    if {p.stem for p in DIRECTORY.glob('*.v')} != {IMPORT_MODULE, *MODULES}:
        raise ValueError('digest-text Rocq module inventory differs')
    if {p.stem for p in DIRECTORY.glob('*.lean')} != set(LEAN_MODULES):
        raise ValueError('digest-text Lean module inventory differs')
    return [name for module in MODULES for name in proof_names(
        (DIRECTORY / (module + '.v')).read_text(), 'LeanCageDigest.' + module + '.')]


PARENT_KEYS = ['parent', 'artifact_sha256', 'export_sha256']


def validate_parent(claims, evidence, actual):
    parent.validate_claims(claims, actual)
    for key in PARENT_KEYS:
        if actual[key] != evidence[key]:
            raise ValueError('preserved argument-loop identity changed: ' + key)


def parent_identity():
    gate = bridge.connection()
    gate.verify_hashes(PARENT_ARCHIVES)
    main = parent.parent_identity()
    actual, active = read(parent.WORK / 'report.json'), read(parent.EVIDENCE)
    archived = read(ROOT / 'assurance/m4-arguments-checkpoint-evidence.json')
    validate_parent(read(parent.MANIFEST), active, actual)
    validate_parent(read(ROOT / 'assurance/m4-arguments-checkpoint-claims.json'), archived, actual)
    if actual['parent'] != main or actual['source_sha256'] != parent.sources() or active['source_sha256'] != parent.sources():
        raise ValueError('parent argument-loop source replay is stale')
    if active['claims_sha256'] != digest(parent.MANIFEST) or active['full_controller_complete'] is not False or active['full_m4_complete'] is not False:
        raise ValueError('parent argument claim identity or boundary differs')
    gate.verify_hashes(actual['artifact_sha256'], parent.WORK)
    gate.verify_hashes(active['archived_receipts_sha256'])
    if digest(parent.WORK / 'arguments.ndjson') != actual['export_sha256']:
        raise ValueError('parent argument imported bytes changed')
    return {key: actual[key] for key in PARENT_KEYS}


def flags(checker=False, proofs=None):
    return parent.flags(checker=checker) + ['-Q', str(proofs or WORK / 'proofs'), 'LeanCageDigest']


def lean_run(command):
    package = ROOT / 'm3'
    paths = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=package, text=True).strip()
    search = ':'.join([str(WORK / 'modules'), str(parent.WORK / 'modules'), str(parent.parent.WORK / 'modules'), str(parent.parent.parent.plan.WORK / 'modules'), paths])
    return subprocess.run(['lake', 'env', 'env', 'LEAN_PATH=' + search, *command], cwd=package,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=180, check=True)


def lean_inventory():
    query = 'import Digest\n' + (ROOT / 'scripts/m3_axiom_query.lean').read_text()
    query += '\nset_option pp.all true\nset_option pp.proofs true\n#audit_module Digest\n'
    path = WORK / 'modules/DigestAudit.lean'
    path.write_text(query)
    rows = [json.loads(line.split('LEANCAGE_AUDIT ', 1)[1])
            for line in lean_run(['lean', str(path)]).stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]
    inventories = [row for row in rows if 'module' in row]
    actual = sorted([row for row in rows if 'name' in row], key=lambda x: x['name'])
    expected = sorted(name for row in inventories for name in row['declarations'])
    if [row['module'] for row in inventories] != LEAN_MODULES or expected != [row['name'] for row in actual] or not actual:
        raise ValueError('incomplete Lean digest-text inventory')
    for row in actual:
        if not row['is_theorem'] or set(row['axioms']) - bridge.ALLOWED_LEAN or '...' in row['type'] or '⋯' in row['type']:
            raise ValueError('unreviewed Lean digest-text statement/foundation')
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
        raise ValueError('unexpected digest-text export version')
    if any(d['kind'] == 'axiom' for d in declarations):
        raise ValueError('computational digest-text closure contains an axiom')
    if {'name': EXPORT_ROOT, 'kind': 'def'} not in declarations:
        raise ValueError('missing digest-text computational root')
    if any(d['name'] in {'Nat.mod', 'Nat.div', 'Iff'} or d['name'].split('.')[0] in {'String', 'Char', 'Array', 'ByteArray', 'UInt8', 'UInt32'} for d in declarations):
        raise ValueError('unreviewed closure in normalized digest-text import')
    return {'metadata': metadata, 'declarations': declarations}


def validate_claims(expected, actual):
    for key in ['rocq_declarations', 'lean_declarations', 'imported_endpoint', 'export_inventory']:
        if not actual[key] or expected[key] != actual[key]:
            raise ValueError('reviewed digest-text statement/foundation/export inventory differs: ' + key)


def negative_structure():
    negative = WORK / 'negative'
    negative.mkdir(exist_ok=True)
    source = (DIRECTORY / 'DigestStructure.v').read_text()
    old = 'Econst_int(Int.repr 64)tint'
    if source.count(old) != 1:
        raise ValueError('ambiguous digest-text negative mutation')
    path = negative / 'DigestStructure.v'
    path.write_text(source.replace(old, 'Econst_int(Int.repr 63)tint'))
    try:
        profile.run(['rocq', 'c', '-q', *flags(proofs=negative), str(path)], cwd=negative)
    except subprocess.CalledProcessError as error:
        if 'Unable to unify' not in error.stdout:
            raise ValueError('negative digest-text identity failed for an unexpected reason: ' + error.stdout)
        return error.stdout
    raise ValueError('kernel accepted changed digest-text descriptors')


def negative_lean_identity():
    negative = WORK / 'negative'
    negative.mkdir(exist_ok=True)
    source = (DIRECTORY / 'Digest.lean').read_text()
    old = 'rest.length != 64'
    if source.count(old) != 1:
        raise ValueError('ambiguous live digest-field identity mutation')
    prefix, equation = source.split('theorem live_digest_equation', 1)
    equation = equation.split('theorem parsed_digest_valid', 1)[0]
    if equation.count(' = (do') != 1 or equation.count(') := rfl') != 1:
        raise ValueError('live digest identity syntax changed')
    body = 'do' + equation.split(' = (do', 1)[1].split(') := rfl', 1)[0]
    fixture = prefix + 'def comparedDigestField (j : Lean.Json) (name : String) : Except String (Option String) := ' + body
    fixture += """
set_option maxRecDepth 4000 in
example : comparedDigestField
    (Lean.Json.mkObj [("digest", .str ("sha256:" ++ String.ofList (List.replicate 64 'a')))]) "digest" =
    liveDigestField
    (Lean.Json.mkObj [("digest", .str ("sha256:" ++ String.ofList (List.replicate 64 'a')))]) "digest" := by cbv
end LeanCageM4.Digest
"""
    positive = negative / 'DigestIdentityControl.lean'
    positive.write_text(fixture)
    lean_run(['lean', str(positive)])
    path = negative / 'DigestNegative.lean'
    path.write_text(fixture.replace(old, 'rest.length != 63'))
    try:
        lean_run(['lean', str(path)])
    except subprocess.CalledProcessError as error:
        counterexample = '⊢ Except.error \"invalid artifact digest\" = Except.ok (some \"sha256:' + 'a' * 64 + '\")'
        if 'unsolved goals' not in error.stdout or counterexample not in ' '.join(error.stdout.split()) or 'timeout' in error.stdout:
            raise ValueError('negative live digest identity failed unexpectedly: ' + error.stdout)
        return error.stdout
    raise ValueError('Lean accepted a changed live digest-field equation')


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
    export_path = WORK / 'digest.ndjson'
    export_path.write_text(lean_run([str(profile.WORK / 'lean4export/.lake/build/bin/lean4export'), 'Digest', '--', EXPORT_ROOT]).stdout)
    exported_inventory = export_inventory(export_path)
    modules = [IMPORT_MODULE, *MODULES]
    for module in modules:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=path.parent).stdout
    negative = WORK / 'proofs/GuardDisabled.v'
    negative.write_text('From LeanImport Require Import Lean.\nUnset Guard Checking.\n'
                        'Set Lean Error Mode "Fail".\nUnset Lean Skip Missing Quotient.\n'
                        'Lean Import "../digest.ndjson".\n')
    try:
        profile.run(['rocq', 'c', '-q', *flags(), str(negative)], cwd=negative.parent)
    except subprocess.CalledProcessError as error:
        if 'M4 strict bridge requires all kernel typing checks' not in error.stdout:
            raise ValueError('negative digest-text import failed for an unexpected reason: ' + error.stdout)
        logs['guard_rejection'] = error.stdout
    else:
        raise ValueError('strict digest-text importer accepted disabled guardedness')
    logs['structure_rejection'] = negative_structure()
    logs['lean_identity_rejection'] = negative_lean_identity()
    query = ['From LeanImport Require Import Lean.', 'From LeanCageDigest Require Import ' + ' '.join(modules) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    targets = [ENDPOINT, *names]
    for i, name in enumerate(targets):
        query += [f'Redirect "digest-type-{i}" Check @{name}.',
                  f'Redirect "digest-foundations-{i}" Print Assumptions {name}.']
    audit = WORK / 'proofs/DigestAudit.v'
    audit.write_text('\n'.join(query) + '\n')
    logs['audit'] = profile.run(['rocq', 'c', '-q', *flags(), str(audit)], cwd=audit.parent).stdout
    records = []
    imported = {'DigestImported', 'DigestConnection'}
    for i, name in enumerate(targets):
        statement = (audit.parent / f'digest-type-{i}.out').read_text().strip()
        assumptions = (audit.parent / f'digest-foundations-{i}.out').read_text().strip()
        axioms, uip = bridge.foundations(assumptions)
        if '...' in statement or (uip and i and name.split('.')[1] not in imported):
            raise ValueError('truncated statement or unreviewed digest-text logical model')
        records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                        'assumption_names': axioms, 'definitional_uip': uip})
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True),
                          *['LeanCageDigest.' + m for m in modules]], cwd=WORK, timeout=300)
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/digest', '-p', 'test_gate.py', '-v'],
                           cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30)
    logs['gate_tests'] = tests.stdout
    if before != sources() or previous != parent_identity():
        raise ValueError('digest-text sources or parent changed during replay')
    artifacts = [WORK / 'proofs' / (m + '.vo') for m in modules]
    artifacts += [WORK / 'modules' / (m + '.olean') for m in LEAN_MODULES]
    report = {'schema_version': 1, 'source_sha256': before, 'parent': previous,
              'rocq_declarations': records[1:], 'imported_endpoint': records[0],
              'lean_declarations': lean, 'export_inventory': exported_inventory, 'export_sha256': digest(export_path),
              'artifact_sha256': {str(p.relative_to(WORK)): digest(p) for p in artifacts},
              'kernel_output': kernel.stdout, 'logs': logs,
              'elapsed_seconds': round(time.monotonic() - started, 3)}
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Digest-text replay passed: {len(names)} Rocq and {len(lean)} Lean full records; strict import, actual AST and kernel checks.', flush=True)
    return report


def check():
    claims, evidence = read(MANIFEST), read(EVIDENCE)
    bridge.connection().verify_hashes(evidence['archived_receipts_sha256'])
    if evidence['claims_sha256'] != digest(MANIFEST) or evidence['full_controller_complete'] is not False or evidence['full_m4_complete'] is not False:
        raise ValueError('digest-text claim identity or boundary differs')
    actual = collect()
    validate_claims(claims, actual)
    for key in ['source_sha256', 'parent', 'artifact_sha256', 'export_sha256']:
        if evidence[key] != actual[key]:
            raise ValueError('reviewed digest-text identity differs: ' + key)
    archived = json.loads(gzip.decompress((ROOT / 'assurance/m4-digest-proof-output.json.gz').read_bytes()))
    validate_claims(archived, actual)
    for key in ['artifact_sha256', 'export_sha256', 'parent', 'kernel_output']:
        if archived[key] != actual[key]:
            raise ValueError('archived digest-text proof identity differs: ' + key)
    print('Reviewed digest-text statements, foundations, artifacts and prior argument-loop identities match.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collect', action='store_true', help='write ignored candidate output; never refresh reviewed manifests')
    args = parser.parse_args()
    collect() if args.collect else check()
