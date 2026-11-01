#!/usr/bin/env python3
"""Rebuild a frozen review candidate without promoting its security claims."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-controller.composition: Preserve the baseline while checking candidate terms.
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import shutil
import time

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / 'm4/parent-checkpoint'
WORK = ROOT / '.tools/m4/parent-checkpoint'
SNAPSHOT = ROOT / 'assurance/m4-parent-checkpoint-proof-output.json.gz'
HANDOFF = ROOT / 'docs/reviews/M4-checkpoint-handoff.md'
BASELINE_COMMIT = '2db87b46d861ffd1c10e295a985818197b8c6170'
MODULES = [
    'NumericFrame', 'NumericMemory', 'ParentAllocation', 'ParentMachine',
    'ParentMemory', 'ParentStructure', 'ParentWords', 'NumericSource',
    'ParentGuards', 'ParentParse', 'ParentRegion', 'ValidationLocals', 'ParentLift',
    'ValidationAllocation', 'ParentComparison', 'ParentPaths', 'ValidationInputs',
    'ParentFinish', 'ParentControl', 'ParentObserve', 'ParentAfterParse',
    'ParentDecision', 'ParentFrontier', 'ParentPlan', 'ParentSource',
    'ParentInitialization', 'ParentRuns', 'NumericComposition', 'ParentLoss',
    'ParentMatching', 'ParentWitnesses', 'NumericMatching', 'NumericWitnesses',
    'ParentSamples', 'ValidationMatching',
]
ENDPOINT = 'LeanCagePlan.PlanImport.LeanCageM4_Plan_parseDecimal'
COMPARE_KEYS = ['baseline_commit', 'review_candidate', 'integrated',
                'full_controller_complete', 'full_m4_complete', 'source_sha256',
                'baseline', 'exports', 'rocq_declarations', 'lean_declarations',
                'imported_endpoint', 'artifact_sha256', 'kernel_output']


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


parent = load(ROOT / 'm4/initialization/check.py', 'parent_candidate_initialization')
plan = load(ROOT / 'm4/plan/check.py', 'parent_candidate_plan')
bridge, profile, read, digest = parent.bridge, parent.profile, parent.read, parent.digest


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [parent.MANIFEST, parent.EVIDENCE, HANDOFF]
    return dict(sorted((parent.sources() | {
        str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def baseline_identity():
    previous = parent.parent_identity()
    actual, evidence = read(parent.WORK / 'report.json'), read(parent.EVIDENCE)
    parent.validate_claims(read(parent.MANIFEST), actual)
    gate = bridge.connection()
    gate.verify_hashes(evidence['archived_receipts_sha256'])
    gate.verify_hashes(actual['artifact_sha256'], parent.WORK)
    if (evidence['claims_sha256'] != digest(parent.MANIFEST)
            or evidence['full_controller_complete'] is not False
            or evidence['full_m4_complete'] is not False):
        raise ValueError('initialization identity or claim boundary differs')
    if actual['parent'] != previous:
        raise ValueError('initialization dependency identity differs')
    if actual['source_sha256'] != parent.sources():
        raise ValueError('initialization replay is stale; replay the existing gates')
    for key in ['source_sha256', 'parent', 'artifact_sha256', 'export_sha256']:
        if actual[key] != evidence[key]:
            raise ValueError('initialization evidence differs: ' + key)
    archived = json.loads(gzip.decompress(
        (ROOT / 'assurance/m4-initialization-proof-output.json.gz').read_bytes()))
    parent.validate_claims(archived, actual)
    for key in ['artifact_sha256', 'export_sha256', 'parent', 'kernel_output']:
        if actual[key] != archived[key]:
            raise ValueError('initialization archive differs: ' + key)
    exports = {}
    for name, checker, filename in [
            ('caller_strings', parent.parent, 'validation.ndjson'),
            ('numeric_plan', plan, 'plan-decimal.ndjson')]:
        report, claims = read(checker.WORK / 'report.json'), read(checker.MANIFEST)
        inventory = checker.export_inventory(checker.WORK / filename)
        if inventory != claims['export_inventory'] or inventory != report['export_inventory']:
            raise ValueError('strict export inventory differs: ' + name)
        sha = digest(checker.WORK / filename)
        if sha != report['export_sha256']:
            raise ValueError('strict export bytes differ: ' + name)
        exports[name] = {'inventory': inventory, 'sha256': sha}
    return ({key: actual[key] for key in ['parent', 'artifact_sha256', 'export_sha256']}, exports)


def flags(checker=False):
    return parent.flags(checker=checker) + ['-Q', str(WORK / 'proofs'), 'LeanCageParent']


def lean_run(command):
    paths = parent.lean_run(['printenv', 'LEAN_PATH']).stdout.strip()
    return parent.lean_run(['env', 'LEAN_PATH=' + str(WORK / 'modules') + ':' + paths, *command])


def lean_inventory():
    query = 'import Parent\n' + (ROOT / 'scripts/m3_axiom_query.lean').read_text()
    query += '\nset_option pp.all true\nset_option pp.proofs true\n#audit_module Parent\n'
    path = WORK / 'modules/ParentAudit.lean'
    path.write_text(query)
    rows = [json.loads(line.split('LEANCAGE_AUDIT ', 1)[1])
            for line in lean_run(['lean', str(path)]).stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]
    inventories = [row for row in rows if 'module' in row]
    actual = sorted([row for row in rows if 'name' in row], key=lambda x: x['name'])
    expected = sorted(name for row in inventories for name in row['declarations'])
    if ([row['module'] for row in inventories] != ['Parent']
            or expected != [row['name'] for row in actual] or not actual):
        raise ValueError('incomplete candidate Lean inventory')
    for row in actual:
        if (not row['is_theorem'] or set(row['axioms']) - bridge.ALLOWED_LEAN
                or '...' in row['type'] or '⋯' in row['type']):
            raise ValueError('unchecked candidate Lean statement or foundation')
    return actual


def collect():
    started = time.monotonic()
    profile.verify_tools()
    before, identity = sources(), baseline_identity()
    if {p.stem for p in DIRECTORY.glob('*.v')} != set(MODULES):
        raise ValueError('candidate Rocq module inventory differs')
    if {p.stem for p in DIRECTORY.glob('*.lean')} != {'Parent'}:
        raise ValueError('candidate Lean module inventory differs')
    names = [name for module in MODULES for name in parent.proof_names(
        (DIRECTORY / (module + '.v')).read_text(), 'LeanCageParent.' + module + '.')]
    for folder in ['modules', 'proofs']:
        (WORK / folder).mkdir(parents=True, exist_ok=True)
    logs = {}
    path = WORK / 'modules/Parent.lean'
    shutil.copyfile(DIRECTORY / path.name, path)
    logs[path.name] = lean_run([
        'lean', '-R', str(path.parent), '-o', str(path.with_suffix('.olean')), str(path)]).stdout
    lean = lean_inventory()
    for module in MODULES:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=path.parent).stdout
        print('Compiled ' + module, flush=True)
    query = ['From LeanImport Require Import Lean.',
             'From LeanCagePlan Require Import PlanImport.',
             'From LeanCageParent Require Import ' + ' '.join(MODULES) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    targets = [ENDPOINT, *names]
    for i, name in enumerate(targets):
        query += [f'Redirect "parent-type-{i}" Check @{name}.',
                  f'Redirect "parent-foundations-{i}" Print Assumptions {name}.']
    audit = WORK / 'proofs/ParentAudit.v'
    audit.write_text('\n'.join(query) + '\n')
    logs['audit'] = profile.run(['rocq', 'c', '-q', *flags(), str(audit)], cwd=audit.parent).stdout
    records = []
    for i, name in enumerate(targets):
        statement = (audit.parent / f'parent-type-{i}.out').read_text().strip()
        assumptions = (audit.parent / f'parent-foundations-{i}.out').read_text().strip()
        axioms, uip = bridge.foundations(assumptions)
        if '...' in statement or (uip and i > 0 and name.split('.')[1] != 'ParentPlan'):
            raise ValueError('truncated candidate statement or unexpected logical model')
        records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                        'assumption_names': axioms, 'definitional_uip': uip})
    # The imported computation must be precisely the existing reviewed endpoint.
    if records[0] != read(plan.MANIFEST)['imported_endpoint']:
        raise ValueError('imported numeric parser endpoint differs from the baseline')
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True),
                          *['LeanCageParent.' + m for m in MODULES]], cwd=WORK, timeout=300)
    artifacts = [WORK / 'proofs' / (m + '.vo') for m in MODULES]
    artifacts += [WORK / 'modules/Parent.olean']
    if before != sources() or identity != baseline_identity():
        raise ValueError('candidate sources or baseline changed during checking')
    report = dict(schema_version=1, baseline_commit=BASELINE_COMMIT, review_candidate=True,
                  integrated=False, full_controller_complete=False, full_m4_complete=False,
                  source_sha256=before, baseline=identity[0], exports=identity[1],
                  rocq_declarations=records[1:], lean_declarations=lean,
                  imported_endpoint=records[0],
                  artifact_sha256={str(p.relative_to(WORK)): digest(p) for p in artifacts},
                  kernel_output=kernel.stdout, logs=logs,
                  elapsed_seconds=round(time.monotonic() - started, 3))
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Candidate checked: {len(records)-1} Rocq and {len(lean)} Lean records; '
          f'{len(artifacts)} compiled artifacts. Integration review remains open.', flush=True)
    return report


def check():
    expected = json.loads(gzip.decompress(SNAPSHOT.read_bytes()))
    actual = collect()
    for key in COMPARE_KEYS:
        if expected[key] != actual[key]:
            raise ValueError('frozen review candidate differs: ' + key)
    print('Full candidate statements, foundations, source and artifact identities match the snapshot.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collect', action='store_true', help='write only an ignored review report')
    args = parser.parse_args()
    collect() if args.collect else check()
