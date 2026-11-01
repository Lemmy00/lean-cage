#!/usr/bin/env python3
"""Replay the complete-helper numeric block without refreshing reviewed expectations."""
# §AR-m4-controller.main-inputs: Full propositions, source identity and preserved artifacts.
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

from frontend import ROOT, SOURCE_SHA256, adapt_proof, digest, function, header_inputs, mutated_number, number_adapter, verify_inputs

DIRECTORY = ROOT / 'm4/main'
WORK = ROOT / '.tools/m4/main'
MANIFEST = ROOT / 'assurance/m4-main-input-claims.json'
EVIDENCE = ROOT / 'assurance/m4-main-input-evidence.json'
MODULES = ['MainStructure', 'MainMemory', 'MainValues', 'MainControl', 'MainLoop', 'MainPrefix',
           'MainFields', 'MainEntry', 'MainSource', 'MainGlobals', 'MainPacked', 'MainArgv',
           'MainAllocation', 'MainOutcomes', 'MainPlan', 'MainWitnesses', 'MainSamples']
PLAN_ARCHIVES = {
    'assurance/m4-plan-checkpoint-claims.json': '5b67d4ffd3834f6cebcc916734283e88525de439b49d523fa74282f92417e747',
    'assurance/m4-plan-checkpoint-evidence.json': '26cc2bb9b37dc24b3adb20cb6b8cdf935640e035eff0118720f68fc900510132',
}


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


sys.path.insert(0, str(ROOT / 'm4/controller'))
plan = load(ROOT / 'm4/plan/check.py', 'main_plan_check')
controller, bridge, profile = plan.controller, plan.bridge, plan.profile
read = controller.read


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / p for p in PLAN_ARCHIVES]
    paths += [plan.MANIFEST, plan.EVIDENCE, ROOT / 'docs/reviews/M4-main-input.md']
    return dict(sorted((plan.sources() | {str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def proof_names(source, prefix):
    source = re.sub(r'\(\*.*?\*\)', '', source, flags=re.S)
    if re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|vm_cast_no_check|native_cast_no_check)\b', source):
        raise ValueError('unfinished or unchecked main-input proof')
    if re.search(r'Unset\s+(?:Guard|Positivity|Universe|Elimination)\s+Checking', source):
        raise ValueError('disabled main-input kernel check')
    names = re.findall(r'^\s*(?:Theorem|Lemma|Example|Corollary|Fact|Remark|Proposition)\s+(\w+)', source, re.M)
    if not names or len(names) != len(set(names)):
        raise ValueError('empty or duplicate main-input theorem inventory')
    return [prefix + name for name in names]


def inventory():
    if {p.stem for p in DIRECTORY.glob('*.v')} != set(MODULES):
        raise ValueError('main-input module inventory differs')
    return [name for module in MODULES for name in proof_names(
        (DIRECTORY / (module + '.v')).read_text(), 'LeanCageMain.' + module + '.')]


def parent_identity():
    gate = bridge.connection()
    gate.verify_hashes(PLAN_ARCHIVES)
    parent = plan.parent_identity()
    actual, active = read(plan.WORK / 'report.json'), read(plan.EVIDENCE)
    plan.validate_claims(read(plan.MANIFEST), actual)
    plan.validate_claims(read(ROOT / 'assurance/m4-plan-checkpoint-claims.json'), actual)
    archived = read(ROOT / 'assurance/m4-plan-checkpoint-evidence.json')
    for key in ['parent', 'artifact_sha256', 'export_sha256']:
        if actual[key] != active[key] or actual[key] != archived[key]:
            raise ValueError('preserved plan identity changed: ' + key)
    if actual['parent'] != parent or actual['source_sha256'] != plan.sources() or active['source_sha256'] != plan.sources():
        raise ValueError('parent plan source replay is stale')
    if active['claims_sha256'] != digest(plan.MANIFEST) or active['full_controller_complete'] is not False or active['full_m4_complete'] is not False:
        raise ValueError('parent plan claim identity or boundary differs')
    gate.verify_hashes(actual['artifact_sha256'], plan.WORK)
    gate.verify_hashes(active['archived_receipts_sha256'])
    if digest(plan.WORK / 'plan-decimal.ndjson') != actual['export_sha256']:
        raise ValueError('parent imported plan bytes changed')
    return {key: actual[key] for key in ['parent', 'artifact_sha256', 'export_sha256']}


def flags(checker=False, proofs=None, number=None):
    return plan.flags(checker=checker) + ['-Q', str(proofs or WORK / 'proofs'), 'LeanCageMain',
                                         '-Q', str(number or WORK / 'number'), 'LeanCageMainNumber']


def validate_claims(expected, actual):
    for key in ['rocq_declarations', 'replayed_number_declarations', 'function_identity']:
        if not actual[key] or expected[key] != actual[key]:
            raise ValueError('main-input full statement/foundation inventory differs: ' + key)


def validate_number_records(records, originals):
    expected = json.loads(json.dumps(originals).replace('LeanCageController', 'LeanCageMainNumber'))
    if records != expected:
        raise ValueError('replayed decimal propositions or foundations changed beyond namespace')


def negative_identity(ast, adapter):
    negative = WORK / 'negative'
    (negative / 'proofs').mkdir(parents=True, exist_ok=True)
    (negative / 'number').mkdir(parents=True, exist_ok=True)
    main = negative / 'proofs/Main.v'
    main.write_text(mutated_number(ast))
    number = negative / 'number/NumberSlice.v'
    number.write_text(adapter)
    options = flags(proofs=main.parent, number=number.parent)
    front = profile.run(['rocq', 'c', '-q', *options, str(main)], cwd=negative).stdout
    try:
        profile.run(['rocq', 'c', '-q', *options, str(number)], cwd=negative)
    except subprocess.CalledProcessError as error:
        if 'Unable to unify' not in error.stdout or 'full_number_ast' in error.stdout.split('Error:')[0]:
            raise ValueError('negative function identity failed for an unexpected reason: ' + error.stdout)
        return {'frontend_compile': front, 'identity_rejection': error.stdout}
    raise ValueError('kernel accepted a changed full-helper parser')


def collect():
    started = time.monotonic()
    profile.verify_tools()
    names, before, parent = inventory(), sources(), parent_identity()
    frontend = controller.frontend_identity()
    if digest(ROOT / 'native/leancage_m3.c') != SOURCE_SHA256:
        raise ValueError('unreviewed complete native helper source')
    for folder in ['input', 'proofs', 'number']:
        (WORK / folder).mkdir(parents=True, exist_ok=True)
    command = [str(ROOT / '.tools/m4/CompCert/clightgen'), '-normalize', '-fstruct-passing',
               '-dprepro', '-o', str(WORK / 'input/Main.v'), str(ROOT / 'native/leancage_m3.c')]
    front = subprocess.run(command, cwd=WORK / 'input', env=controller.bootstrap.environment(),
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=60)
    ast = (WORK / 'input/Main.v').read_text()
    functions = re.findall(r'^Definition f_(\w+) :=', ast, re.M)
    if len(functions) != 55 or len(set(functions)) != 55 or 'Definition version := "3.17".' not in ast:
        raise ValueError('complete-helper frontend inventory differs')
    function(ast, 'main')
    headers = header_inputs((WORK / 'input/leancage_m3.i').read_text())
    verify_inputs(headers)
    adapter = number_adapter((controller.WORK / 'input/NumberSlice.v').read_text())
    shutil.copyfile(WORK / 'input/Main.v', WORK / 'proofs/Main.v')
    (WORK / 'number/NumberSlice.v').write_text(adapter)
    logs = {'frontend': front.stdout}
    compile_files = [WORK / 'proofs/Main.v', WORK / 'number/NumberSlice.v']
    adapted = {}
    for module in controller.MODULES:
        path = WORK / 'number' / (module + '.v')
        path.write_text(adapt_proof((controller.DIRECTORY / (module + '.v')).read_text()))
        compile_files.append(path)
        adapted[str(path.relative_to(WORK))] = digest(path)
    for module in MODULES:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        compile_files.append(path)
    for path in compile_files:
        logs[str(path.relative_to(WORK))] = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=path.parent).stdout
    original_records = read(controller.MANIFEST)['rocq_declarations']
    number_names = [row['name'].replace('LeanCageController', 'LeanCageMainNumber') for row in original_records]
    identity_name = 'LeanCageMainNumber.NumberSlice.full_number_ast'
    def audit_records(targets, imports, prefix):
        query = [*imports, 'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
        for i, name in enumerate(targets):
            query += [f'Redirect "{prefix}-type-{i}" Check @{name}.',
                      f'Redirect "{prefix}-foundations-{i}" Print Assumptions {name}.']
        audit = WORK / 'proofs' / (prefix + 'Audit.v')
        audit.write_text('\n'.join(query) + '\n')
        logs[prefix + '_audit'] = profile.run(['rocq', 'c', '-q', *flags(), str(audit)], cwd=audit.parent).stdout
        records = []
        for i, name in enumerate(targets):
            statement = (audit.parent / f'{prefix}-type-{i}.out').read_text().strip()
            assumptions = (audit.parent / f'{prefix}-foundations-{i}.out').read_text().strip()
            axioms, uip = bridge.foundations(assumptions)
            if '...' in statement or (uip and not name.startswith('LeanCageMain.MainPlan.')):
                raise ValueError('truncated statement or unreviewed main-input logical model')
            records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                            'assumption_names': axioms, 'definitional_uip': uip})
        return records
    # Preserve the original number audit's import context as well as its proof sources.
    records = audit_records([identity_name, *number_names],
                            ['From LeanCageMainNumber Require Import ' + ' '.join(controller.MODULES) + '.'], 'MainNumber')
    records += audit_records(names, ['From LeanImport Require Import Lean.',
                            'From LeanCagePlan Require Import PlanImport.',
                            'From LeanCageMain Require Import ' + ' '.join(MODULES) + '.'], 'Main')
    copied = records[1:1 + len(number_names)]
    validate_number_records(copied, original_records)
    targets = ['LeanCageMain.Main', *['LeanCageMainNumber.' + m for m in ['NumberSlice', *controller.MODULES]],
               *['LeanCageMain.' + m for m in MODULES]]
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True), *targets], cwd=WORK, timeout=300)
    logs['negative_identity'] = negative_identity(ast, adapter)
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/main',
                            '-p', 'test_gate.py', '-v'], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30)
    logs['gate_tests'] = tests.stdout
    verify_inputs(headers)
    if before != sources() or parent != parent_identity() or frontend != controller.frontend_identity():
        raise ValueError('main-input source or parent changed during replay')
    artifacts = [path.with_suffix('.vo') for path in compile_files]
    artifacts += [WORK / 'input/Main.v', WORK / 'input/leancage_m3.i', WORK / 'number/NumberSlice.v']
    report = {'schema_version': 1, 'source_sha256': before, 'parent': parent,
              'rocq_declarations': records[1 + len(number_names):], 'replayed_number_declarations': copied,
              'function_identity': records[0], 'frontend': frontend, 'frontend_command': command,
              'header_inputs_sha256': headers, 'functions': functions, 'source_sha256_native': SOURCE_SHA256,
              'adapted_sources_sha256': adapted,
              'artifact_sha256': {str(p.relative_to(WORK)): digest(p) for p in artifacts},
              'kernel_output': kernel.stdout, 'logs': logs,
              'elapsed_seconds': round(time.monotonic() - started, 3)}
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Main input replay passed: {len(names)} new and {len(copied)} replayed records; exact full-helper identity and independent kernel check.', flush=True)
    return report


def check():
    claims, evidence = read(MANIFEST), read(EVIDENCE)
    report = collect()
    validate_claims(claims, report)
    for key in ['source_sha256', 'parent', 'frontend', 'frontend_command', 'header_inputs_sha256',
                'functions', 'source_sha256_native', 'adapted_sources_sha256', 'artifact_sha256']:
        if evidence[key] != report[key]:
            raise ValueError('reviewed main-input identity differs: ' + key)
    if evidence['claims_sha256'] != digest(MANIFEST) or evidence['full_controller_complete'] is not False or evidence['full_m4_complete'] is not False:
        raise ValueError('main-input claim identity or boundary differs')
    bridge.connection().verify_hashes(evidence['archived_receipts_sha256'])
    archived = json.loads(gzip.decompress((ROOT / 'assurance/m4-main-input-proof-output.json.gz').read_bytes()))
    validate_claims(claims, archived)
    for key in ['artifact_sha256', 'header_inputs_sha256', 'frontend', 'source_sha256_native', 'kernel_output']:
        if archived[key] != report[key]:
            raise ValueError('archived main-input proof identity differs: ' + key)
    print('Selected main numeric block checked; entry reachability, later validation, Linux and executable correspondence remain OPEN.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--collect', action='store_true', help='collect an ignored candidate; never refresh expectations')
    args = parser.parse_args()
    try:
        collect() if args.collect else check()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print('Main input replay failed: ' + str(error), file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stdout, file=sys.stderr)
        sys.exit(1)
