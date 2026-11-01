#!/usr/bin/env python3
"""Replay live plan layout, exact decimal bytes and imported native source composition."""
# §AR-m4-controller.plan: Preserve full checked statements and the preceding native checkpoint.
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / 'm4/plan'
WORK = ROOT / '.tools/m4/plan'
MANIFEST = ROOT / 'assurance/m4-plan-claims.json'
EVIDENCE = ROOT / 'assurance/m4-plan-evidence.json'
MODULES = ['PlanValues', 'PlanCodec', 'PlanSource', 'PlanSamples']
LEAN_MODULES = ['Decimal', 'Plan']
ENDPOINT = 'LeanCagePlan.PlanImport.LeanCageM4_Plan_parseDecimal'
EXPORT_ROOT = 'LeanCageM4.Plan.parseDecimal'
NUMBER_ARCHIVES = {
    'assurance/m4-number-checkpoint-claims.json': '0d3fa5e0d645987f1a5495def441ed2c35bc43be542da827160aeea8c50fdf58',
    'assurance/m4-number-checkpoint-evidence.json': 'b5bdd8dbec624efcdf3a45a45a8ceff72748cbfcaa4ae1d5fc4ba3f7ddd76951',
}


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


sys.path.insert(0, str(ROOT / 'm4/controller'))
controller = load(ROOT / 'm4/controller/check.py', 'plan_controller_check')
bridge = controller.bridge
profile = controller.profile
digest = profile.digest
read = controller.read


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / p for p in NUMBER_ARCHIVES]
    paths += [ROOT / p for p in ['assurance/m4-controller-number-claims.json',
              'assurance/m4-controller-number-evidence.json', 'docs/reviews/M4-plan.md']]
    return dict(sorted((controller.sources() | {str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def inventory():
    if {p.stem for p in DIRECTORY.glob('*.v')} != {'PlanImport', *MODULES}:
        raise ValueError('plan Rocq module inventory differs')
    if {p.stem for p in DIRECTORY.glob('*.lean')} != set(LEAN_MODULES):
        raise ValueError('plan Lean module inventory differs')
    result = []
    for module in MODULES:
        source = re.sub(r'\(\*.*?\*\)', '', (DIRECTORY / (module + '.v')).read_text(), flags=re.S)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|vm_cast_no_check|native_cast_no_check)\b', source):
            raise ValueError('unfinished or unchecked plan proof')
        if re.search(r'Unset\s+(?:Guard|Positivity|Universe|Elimination)\s+Checking', source):
            raise ValueError('disabled plan kernel check')
        names = re.findall(r'^\s*(?:Theorem|Lemma|Example|Corollary|Fact|Remark|Proposition)\s+(\w+)', source, re.M)
        if not names:
            raise ValueError('empty plan theorem inventory')
        result += ['LeanCagePlan.' + module + '.' + name for name in names]
    return result


def validate_parent(claims, evidence, actual):
    controller.validate_claims(claims, actual)
    for key in ['source_connection', 'frontend_command', 'frontend', 'parent', 'artifact_sha256']:
        if evidence[key] != actual[key]:
            raise ValueError('native decimal checkpoint changed: ' + key)


def parent_identity():
    gate = bridge.connection()
    gate.verify_hashes(NUMBER_ARCHIVES)
    current_frames = controller.parent_identity()
    actual = read(controller.WORK / 'report.json')
    active = read(controller.EVIDENCE)
    validate_parent(read(ROOT / 'assurance/m4-number-checkpoint-claims.json'),
                    read(ROOT / 'assurance/m4-number-checkpoint-evidence.json'), actual)
    controller.validate_claims(read(controller.MANIFEST), actual)
    if actual['source_sha256'] != controller.sources() or actual['source_sha256'] != active['source_sha256']:
        raise ValueError('parent controller source replay is stale')
    for key in ['source_connection', 'frontend_command', 'frontend', 'parent', 'artifact_sha256']:
        if actual[key] != active[key]:
            raise ValueError('active controller identity differs: ' + key)
    if actual['parent'] != current_frames or actual['frontend'] != controller.frontend_identity():
        raise ValueError('controller frame or frontend dependency differs')
    if active['claims_sha256'] != digest(controller.MANIFEST) or active['full_controller_complete'] is not False or active['full_m4_complete'] is not False:
        raise ValueError('controller claim identity or boundary differs')
    gate.verify_hashes(actual['artifact_sha256'], controller.WORK)
    gate.verify_hashes(active['archived_receipts_sha256'])
    return {key: actual[key] for key in ['source_connection', 'frontend_command', 'frontend', 'parent', 'artifact_sha256']}


def flags(checker=False):
    return profile.flags(checker=checker) + ['-Q', str(controller.WORK / 'proofs'), 'LeanCageController',
                                           '-Q', str(WORK / 'proofs'), 'LeanCagePlan']


def compile_file(path):
    return profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=WORK / 'proofs')


def lean_run(command):
    package = ROOT / 'm3'
    paths = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=package, text=True).strip()
    return subprocess.run(['lake', 'env', 'env', 'LEAN_PATH=' + str(WORK / 'modules') + ':' + paths, *command],
                          cwd=package, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=180, check=True)


def lean_inventory():
    query = 'import Plan\n' + (ROOT / 'scripts/m3_axiom_query.lean').read_text()
    query += '\n' + '\n'.join('#audit_module ' + name for name in LEAN_MODULES) + '\n'
    path = WORK / 'modules/PlanAudit.lean'
    path.write_text(query)
    rows = [json.loads(line.split('LEANCAGE_AUDIT ', 1)[1])
            for line in lean_run(['lean', str(path)]).stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]
    inventories = [row for row in rows if 'module' in row]
    actual = sorted([row for row in rows if 'name' in row], key=lambda x: x['name'])
    expected = sorted(name for row in inventories for name in row['declarations'])
    if sorted(row['module'] for row in inventories) != sorted(LEAN_MODULES) or expected != [r['name'] for r in actual] or not actual:
        raise ValueError('incomplete actual Lean plan theorem inventory')
    for record in actual:
        if not record['is_theorem'] or set(record['axioms']) - bridge.ALLOWED_LEAN:
            raise ValueError('unreviewed Lean plan theorem/foundation')
        if '...' in record['type'] or '⋯' in record['type']:
            raise ValueError('truncated Lean plan statement')
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
        raise ValueError('unexpected plan export version')
    if any(d['kind'] == 'axiom' for d in declarations):
        raise ValueError('computational plan closure contains an axiom')
    if {'name': EXPORT_ROOT, 'kind': 'def'} not in declarations:
        raise ValueError('missing actual exported numeric root')
    if any(d['name'].split('.')[0] in {'String', 'Char', 'UInt32'} for d in declarations):
        raise ValueError('unreviewed string/character closure in numeric plan import')
    return {'metadata': metadata, 'declarations': declarations}


def validate_claims(expected, actual):
    for key in ['rocq_declarations', 'lean_declarations', 'imported_endpoint', 'export_inventory']:
        if not actual[key] or expected[key] != actual[key]:
            raise ValueError('reviewed plan statement/foundation/export inventory differs: ' + key)


def collect():
    started = time.monotonic()
    profile.verify_tools()
    names, before, parent = inventory(), sources(), parent_identity()
    for name in ['modules', 'proofs']:
        (WORK / name).mkdir(parents=True, exist_ok=True)
    logs = {}
    for module in LEAN_MODULES:
        path = WORK / 'modules' / (module + '.lean')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = lean_run(['lean', '-R', str(WORK / 'modules'), '-o', str(path.with_suffix('.olean')), str(path)]).stdout
    lean = lean_inventory()
    exported = lean_run([str(profile.WORK / 'lean4export/.lake/build/bin/lean4export'),
                         'Plan', '--', EXPORT_ROOT]).stdout
    export_path = WORK / 'plan-decimal.ndjson'
    export_path.write_text(exported)
    exported_inventory = export_inventory(export_path)
    for module in ['PlanImport', *MODULES]:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[path.name] = compile_file(path).stdout
    negative = WORK / 'proofs/GuardDisabled.v'
    negative.write_text('From LeanImport Require Import Lean.\nUnset Guard Checking.\n'
                        'Set Lean Error Mode "Fail".\nUnset Lean Skip Missing Quotient.\n'
                        'Lean Import "../plan-decimal.ndjson".\n')
    try:
        compile_file(negative)
    except subprocess.CalledProcessError as error:
        if 'M4 strict bridge requires all kernel typing checks' not in error.stdout:
            raise ValueError('negative plan import failed for an unexpected reason: ' + error.stdout)
        logs['GuardDisabled.v'] = error.stdout
    else:
        raise ValueError('strict plan importer accepted disabled guardedness')
    query = ['From LeanImport Require Import Lean.',
             'From LeanCagePlan Require Import PlanImport ' + ' '.join(MODULES) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    targets = [ENDPOINT, *names]
    for i, name in enumerate(targets):
        query += [f'Redirect "plan-type-{i}" Check @{name}.',
                  f'Redirect "plan-foundations-{i}" Print Assumptions {name}.']
    path = WORK / 'proofs/PlanAudit.v'
    path.write_text('\n'.join(query) + '\n')
    logs[path.name] = compile_file(path).stdout
    records = []
    for i, name in enumerate(targets):
        statement = (WORK / f'proofs/plan-type-{i}.out').read_text().strip()
        assumptions = (WORK / f'proofs/plan-foundations-{i}.out').read_text().strip()
        axioms, uip = bridge.foundations(assumptions)
        if '...' in statement:
            raise ValueError('truncated plan theorem statement')
        records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                        'assumption_names': axioms, 'definitional_uip': uip})
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True),
                          *['LeanCagePlan.' + name for name in ['PlanImport', *MODULES]]],
                         cwd=WORK / 'proofs', timeout=300)
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/plan',
                            '-p', 'test_gate.py', '-v'], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30)
    logs['gate_tests'] = tests.stdout
    if before != sources() or parent != parent_identity():
        raise ValueError('plan or parent inputs changed during replay')
    artifacts = [WORK / 'proofs' / (name + '.vo') for name in ['PlanImport', *MODULES]]
    artifacts += [WORK / 'modules' / (name + '.olean') for name in LEAN_MODULES]
    report = {'schema_version': 1, 'source_sha256': before, 'parent': parent,
              'rocq_declarations': records[1:], 'imported_endpoint': records[0],
              'lean_declarations': lean, 'export_inventory': exported_inventory,
              'export_sha256': digest(export_path),
              'artifact_sha256': {str(path.relative_to(WORK)): digest(path) for path in artifacts},
              'kernel_output': kernel.stdout, 'logs': logs,
              'elapsed_seconds': round(time.monotonic() - started, 3)}
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Plan replay passed: {len(records)-1} Rocq and {len(lean)} Lean full theorem records; strict import and independent kernel check.', flush=True)
    return report


def check():
    claims, evidence = read(MANIFEST), read(EVIDENCE)
    report = collect()
    validate_claims(claims, report)
    for key in ['source_sha256', 'parent', 'artifact_sha256', 'export_sha256']:
        if report[key] != evidence[key]:
            raise ValueError('reviewed plan identity differs: ' + key)
    if evidence['claims_sha256'] != digest(MANIFEST) or evidence['full_controller_complete'] is not False or evidence['full_m4_complete'] is not False:
        raise ValueError('plan claim identity or boundary differs')
    bridge.connection().verify_hashes(evidence['archived_receipts_sha256'])
    exported = gzip.decompress((ROOT / 'assurance/m4-plan-export.ndjson.gz').read_bytes())
    if hashlib.sha256(exported).hexdigest() != report['export_sha256']:
        raise ValueError('archived plan terms differ from actual export')
    print('Live plan bytes and imported native parsing checked; translation, argv provenance, main ordering and Linux/executable composition remain OPEN.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--collect', action='store_true', help='write an ignored candidate report; never refresh expectations')
    args = parser.parse_args()
    try:
        collect() if args.collect else check()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print('Plan replay failed: ' + str(error), file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stdout, file=sys.stderr)
        sys.exit(1)
