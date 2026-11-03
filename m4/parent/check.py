#!/usr/bin/env python3
"""Check the maintained parent composition without refreshing reviewed expectations."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-parent.audit: Full propositions, foundations, input/trace contracts and compiled controls.
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
DIRECTORY = ROOT / 'm4/parent'
WORK = ROOT / '.tools/m4/parent'
MANIFEST = ROOT / 'assurance/m4-parent-claims.json'
EVIDENCE = ROOT / 'assurance/m4-parent-evidence.json'
SNAPSHOT = ROOT / 'assurance/m4-parent-proof-output.json.gz'
MODULES = [
    'NumericFrame', 'NumericMemory', 'ParentAllocation', 'ParentMachine',
    'ParentMemory', 'ParentStructure', 'ParentWords', 'NumericSource',
    'ParentGuards', 'ParentParse', 'ParentRegion', 'ValidationLocals', 'ParentLift',
    'ValidationAllocation', 'ParentComparison', 'ParentPaths', 'ValidationInputs',
    'ParentFinish', 'ParentControl', 'ParentObserve', 'ParentAfterParse',
    'ParentDecision', 'ParentFrontier', 'ParentPlan', 'ParentSource',
    'ParentInitialization', 'ParentRuns', 'NumericComposition', 'ParentLoss',
    'TraceRegion', 'TraceExecution', 'TraceCut', 'TraceChoices', 'ParentCost', 'ParentMatching', 'ParentWitnesses', 'NumericMatching',
    'ParentSamples', 'ParentTrace',
    'TraceInitialization', 'FrontierShapes', 'NumericTrace', 'InputRepresentation',
    'NumericWitnesses', 'ValidationMatching', 'CompositionDecision', 'CompositionExecution', 'CompositionSamples', 'CompositionLoss', 'CompositionWitnesses',
]


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


candidate = load(ROOT / 'm4/parent-checkpoint/verify.py', 'maintained_parent_candidate')
parent, plan = candidate.parent, candidate.plan
bridge, profile, read, digest = candidate.bridge, candidate.profile, candidate.read, candidate.digest
inventory_module = load(DIRECTORY / 'inventory.py', 'maintained_parent_inventory')
amendment = load(DIRECTORY / 'amendment.py', 'maintained_parent_amendment')
ENDPOINT = candidate.ENDPOINT
STATUS = 'independently reviewed bounded parent source contract; full M4 remains open'
PRIMARY_CONTRACTS = [
    'LeanCageParent.NumericTrace.numeric_trace_source',
    'LeanCageParent.TraceExecution.trace_execution_split',
    'LeanCageParent.TraceCut.trace_post_bounds_cut',
    'LeanCageParent.TraceCut.trace_acceptance_prefix',
    'LeanCageParent.FrontierShapes.residual_acceptance_history',
    'LeanCageParent.NumericWitnesses.allocated_numeric_validation',
    'LeanCageParent.ValidationMatching.allocated_validation_matching',
]
RECEIPTS = {
    'assurance/m4-parent-baseline-validation.json',
    'assurance/m4-parent-baseline-check.log.gz',
    'assurance/m4-parent-navigation.json',
    'assurance/m4-parent-navigation-before.json.gz',
    'assurance/m4-parent-checkpoint-validation.json',
}
CHECKPOINT_RECEIPT = 'f1bfcf2eca69767c63ff75b5357531f8eb682a55e87215ab2f08142cdfe68442'
REVIEW_CHECKPOINT = {
    'assurance/m4-parent-reviewed-candidate-claims.json':
        '357a423c31d314a7efe8a04dc2361676cafbe0289209b1a490ca13e3b03152f3',
    'assurance/m4-parent-reviewed-candidate-evidence.json':
        'e746fa2f7524ff251d5ee64e746fc1f1d6c8f99152f36b017eaca7878cb614cb',
    'assurance/m4-parent-reviewed-candidate-proof-output.json.gz':
        '7a6cc4e4b296eba0f0a1471fea00f88a114aca284f294a40e458a0bfb95251ee',
    'assurance/m4-parent-reviewed-candidate-validation.json':
        'b4c5be501b3e820c73905fac70bd18d86f5d6bf1da111c896fd64dec4aaa7a1b',
}
REVISED_CANDIDATE = {
    'LeanCageParent.ParentLift.parent_getppid': 'Remove unused duplicate observation constructor.',
    'LeanCageParent.ParentRuns.parent_observation_execution': 'Export independently constructed suffix bound.',
    'LeanCageParent.NumericComposition.numeric_validation_source': 'Remove unused export contract parameter.',
    'LeanCageParent.ParentMatching.parent_initialization_matching': 'Export the actual singleton observation history.',
    'LeanCageParent.ParentWitnesses.allocated_parent_observations': 'Export the source-derived suffix bound.',
    'LeanCageParent.NumericMatching.numeric_validation_matching': 'Preserve the actual observation through numeric composition.',
    'LeanCageParent.NumericWitnesses.allocated_numeric_validation': 'Export initial input representation and universal trace contract.',
    'LeanCageParent.ValidationMatching.allocated_validation_matching': 'Export initial input representation and actual matching history.',
}


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / 'docs/architecture/AR-m4-parent.md',
              ROOT / 'docs/decisions/architectural/DA-m4-parent.md',
              ROOT / 'docs/reviews/M4-parent-repair.md',
              ROOT / 'docs/reviews/M4-parent-independent-review.md',
              amendment.RECORD, amendment.BEFORE, ROOT / 'assurance/m4-parent-baseline-validation.json',
              ROOT / 'assurance/m4-parent-baseline-check.log.gz']
    paths += [ROOT / 'assurance/m4-parent-build-roots.json',
              ROOT / 'assurance/m4-parent-initial-build-output.json.gz',
              ROOT / 'assurance/m4-compiler-initial-build-output.json.gz']
    paths += [ROOT / ('assurance/m4-parent-reviewed-candidate-' + suffix)
              for suffix in ['claims.json', 'evidence.json', 'proof-output.json.gz', 'validation.json']]
    paths += [ROOT / 'assurance/m4-parent-review-correction.json']
    paths += [ROOT / ('assurance/m4-parent-corrected-review-' + suffix)
              for suffix in ['claims.json', 'evidence.json', 'proof-output.json.gz', 'validation.json']]
    paths += [ROOT / 'assurance/m4-parent-navigation-stage1.json',
              ROOT / 'assurance/m4-parent-promotion.json', ROOT / 'assurance/m4-parent-independent-check.log.gz']
    paths += [p for p in (ROOT / 'm4/feasibility').iterdir() if p.is_file()]
    paths += [ROOT / 'assurance/m4-compiler-feasibility.json',
              ROOT / 'assurance/m4-compiler-feasibility-output.json.gz']
    return dict(sorted((candidate.sources() | {
        str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def flags(checker=False, proofs=None):
    result = parent.flags(checker=checker) + ['-Q', str(WORK / 'proofs'), 'LeanCageParent']
    return result + (['-Q', str(proofs), 'LeanCageParent'] if proofs else [])


def lean_run(command):
    paths = parent.lean_run(['printenv', 'LEAN_PATH']).stdout.strip()
    return parent.lean_run(['env', 'LEAN_PATH=' + str(WORK / 'modules') + ':' + paths, *command])


def inventory():
    if {p.stem for p in DIRECTORY.glob('*.v')} != set(MODULES):
        raise ValueError('maintained parent Rocq module inventory differs')
    if {p.stem for p in DIRECTORY.glob('*.lean')} != {'Parent'}:
        raise ValueError('maintained parent Lean module inventory differs')
    return [name for module in MODULES for name in inventory_module.declarations(
        (DIRECTORY / (module + '.v')).read_text(), 'LeanCageParent.' + module + '.')]


def compile_proofs(modules=None):
    for folder in ['modules', 'proofs']:
        (WORK / folder).mkdir(parents=True, exist_ok=True)
    logs = {}
    for module in modules or MODULES:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        result = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=path.parent)
        logs[path.name] = result.stdout
        print('Compiled ' + module, flush=True)
    return logs


def checked_inventory(source_names):
    """Read actual compiled signatures; the source scanner is not an inventory oracle."""
    directory = WORK / 'proofs'
    query = ['From LeanCageParent Require Import ' + ' '.join(MODULES) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    for index, module in enumerate(MODULES):
        query.append(f'Redirect "parent-environment-{index}" Print Module LeanCageParent.{module}.')
    path = directory / 'ParentEnvironment.v'
    path.write_text('\n'.join(query) + '\n')
    compilation = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=directory)
    names, signatures = [], {}
    for index, module in enumerate(MODULES):
        signature = (directory / f'parent-environment-{index}.out').read_text().strip()
        signatures[module] = signature
        names += inventory_module.checked_declarations(signature, 'LeanCageParent.' + module)
    if not set(source_names).issubset(names) or len(names) != len(set(names)):
        raise ValueError('source declarations missing from checked environment or duplicate names')
    return names, dict(compilation_output=compilation.stdout, signatures=signatures)


def native_controls():
    """Compile actual C edits, then ask the kernel to check whole-main identity."""
    controls = {}
    original = (ROOT / 'native/leancage_m3.c').read_text()
    guard = 'parent>INT_MAX||getppid()!=(pid_t)parent'
    if original.count(guard) != 1:
        raise ValueError('ambiguous native parent guard')
    for label, replacement in [
            ('positive', guard),
            ('guard', 'parent>=INT_MAX||getppid()!=(pid_t)parent'),
            ('narrowing', 'parent>INT_MAX||getppid()!=(uint64_t)parent'),
            ('comparison', 'parent>INT_MAX||getppid()==(pid_t)parent')]:
        directory = WORK / ('control-' + label)
        directory.mkdir(exist_ok=True)
        source = directory / 'leancage_m3.c'
        source.write_text(original.replace(guard, replacement))
        ast = directory / 'ControlMain.v'
        front = subprocess.run([
            str(ROOT / '.tools/m4/CompCert/clightgen'), '-normalize', '-fstruct-passing',
            '-I', str(ROOT / 'native'), '-o', str(ast), str(source)], cwd=directory,
            env=plan.controller.bootstrap.environment(),
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=60)
        options = flags() + ['-Q', str(directory), 'LeanCageParentControl']
        profile.run(['rocq', 'c', '-q', *options, str(ast)], cwd=directory)
        query = directory / 'ControlIdentity.v'
        query.write_text('From LeanCageMain Require Import Main.\n'
                         'From LeanCageParentControl Require Import ControlMain.\n'
                         'Lemma actual_main_unchanged : Main.f_main=ControlMain.f_main.\n'
                         'Proof. reflexivity. Qed.\n')
        try:
            proof = profile.run(['rocq', 'c', '-q', *options, str(query)], cwd=directory)
        except subprocess.CalledProcessError as error:
            if label == 'positive' or 'Unable to unify' not in error.stdout:
                raise ValueError('unexpected compiled parent control failure: ' + label + '\n' + error.stdout) from error
            proof_output = error.stdout
        else:
            if label != 'positive':
                raise ValueError('kernel accepted altered actual native main: ' + label)
            proof_output = proof.stdout
        controls[label] = dict(source_sha256=digest(source), ast_sha256=digest(ast),
                               frontend_output=front.stdout, proof_output=proof_output,
                               expected_acceptance=label == 'positive')
    return controls


def validate_claims(expected, actual):
    names = [row['name'] for row in actual['rocq_declarations']]
    required = {
        'LeanCageParent.ParentTrace.traced_parent_frontier',
        'LeanCageParent.ParentTrace.matching_history',
        'LeanCageParent.TraceInitialization.traced_initialization_frontier',
        'LeanCageParent.NumericTrace.numeric_trace_contract',
        'LeanCageParent.InputRepresentation.validation_input_representation',
        'LeanCageParent.CompositionExecution.allocated_composition_execution',
        'LeanCageParent.CompositionWitnesses.composition_samples_source',
        'LeanCageParent.CompositionLoss.composed_prefix_loss',
        *actual['primary_contracts'],
    }
    if (len(names) != len(set(names)) or not required.issubset(names)
            or names != actual['checked_environment_names']
            or actual['primary_contracts'] != PRIMARY_CONTRACTS):
        raise ValueError('missing or duplicate maintained parent contracts')
    validate_candidate_preservation(actual['rocq_declarations'])
    validate_review_preservation(actual['rocq_declarations'])
    for key in ['rocq_declarations', 'checked_environment_names', 'lean_declarations',
                'imported_endpoint', 'primary_contracts', 'candidate_preservation']:
        if not actual[key] or actual[key] != expected[key]:
            raise ValueError('maintained parent statement/foundation inventory differs: ' + key)


def validate_review_preservation(records):
    original = read(ROOT / 'assurance/m4-parent-reviewed-candidate-claims.json')
    current = {row['name']: row for row in records}
    for row in original['rocq_declarations']:
        if current.get(row['name']) != row:
            raise ValueError('unamended reviewed-candidate type/foundation changed: ' + row['name'])


def validate_candidate_preservation(records):
    original = json.loads(gzip.decompress(candidate.SNAPSHOT.read_bytes()))
    current = {row['name']: row for row in records}
    unchanged, revised = [], []
    for row in original['rocq_declarations']:
        name, actual = row['name'], current.get(row['name'])
        if name in REVISED_CANDIDATE:
            if name.endswith('.parent_getppid'):
                if actual is not None:
                    raise ValueError('unused parent_getppid must remain removed')
            else:
                if actual is None or actual == row:
                    raise ValueError('candidate interface amendment missing: ' + name)
                for key in ['transitive_assumptions', 'assumption_names', 'definitional_uip']:
                    if row[key] != actual[key]:
                        raise ValueError('revised candidate foundations changed: ' + name)
            revised.append(name)
        elif actual != row:
            raise ValueError('unamended candidate statement/foundation changed: ' + name)
        else:
            unchanged.append(name)
    if set(revised) != set(REVISED_CANDIDATE):
        raise ValueError('candidate amendment inventory differs')
    return dict(unchanged_declarations=unchanged, revised_declarations=REVISED_CANDIDATE,
                frozen_snapshot_sha256=digest(candidate.SNAPSHOT),
                original_candidate_promoted=False)


def validate_evidence(evidence, archived, actual, claims_sha256):
    reviewed = read(ROOT / 'assurance/m4-parent-corrected-review-evidence.json')
    if actual['artifact_sha256'] != reviewed['artifact_sha256']:
        raise ValueError('promotion changed a reviewed compiled artifact')
    for key in ['source_sha256', 'baseline', 'exports', 'artifact_sha256', 'kernel_output']:
        if actual[key] != evidence[key] or actual[key] != archived[key]:
            raise ValueError('parent evidence differs: ' + key)
    if evidence['claims_sha256'] != claims_sha256:
        raise ValueError('parent claim receipt identity differs')
    receipts = evidence['archived_receipts_sha256']
    if set(receipts) != RECEIPTS:
        raise ValueError('parent receipt inventory differs')
    for path in RECEIPTS:
        required = CHECKPOINT_RECEIPT if path.endswith('m4-parent-checkpoint-validation.json') else actual['source_sha256'].get(path)
        if receipts[path] != required:
            raise ValueError('parent receipt identity differs: ' + path)
    if (evidence['status'] != STATUS or evidence['fresh_vm_workloads_run'] is not False
            or type(evidence['original_obligations_closed']) is not int
            or evidence['original_obligations_closed'] != 0):
        raise ValueError('parent status or evidence scope differs')
    for record in [evidence, archived, actual]:
        if record['full_controller_complete'] is not False or record['full_m4_complete'] is not False:
            raise ValueError('parent completion boundary differs')


def collect_proofs():
    profile.verify_tools()
    source_names = inventory()
    logs = compile_proofs()
    names, logs['checked_environment'] = checked_inventory(source_names)
    path = WORK / 'modules/Parent.lean'
    shutil.copyfile(DIRECTORY / path.name, path)
    logs[path.name] = lean_run(['lean', '-R', str(path.parent), '-o', str(path.with_suffix('.olean')), str(path)]).stdout
    old_work = candidate.WORK
    try:
        candidate.WORK = WORK
        lean = candidate.lean_inventory()
    finally:
        candidate.WORK = old_work
    query = ['From LeanImport Require Import Lean.', 'From LeanCagePlan Require Import PlanImport.',
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
            raise ValueError('truncated parent statement or unexpected logical model')
        records.append(dict(name=name, full_type=statement, transitive_assumptions=assumptions,
                            assumption_names=axioms, definitional_uip=uip))
    if records[0] != read(plan.MANIFEST)['imported_endpoint']:
        raise ValueError('imported numeric parser endpoint differs')
    preservation = validate_candidate_preservation(records[1:])
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True),
                          *['LeanCageParent.' + m for m in MODULES]], cwd=WORK, timeout=300)
    logs['native_controls'] = native_controls()
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/parent',
                            '-p', 'test_*.py', '-v'], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=60)
    logs['gate_tests'] = tests.stdout
    artifacts = [WORK / 'proofs' / (m + '.vo') for m in MODULES] + [path.with_suffix('.olean')]
    return dict(schema_version=1, full_controller_complete=False, full_m4_complete=False,
                  rocq_declarations=records[1:], checked_environment_names=names,
                  lean_declarations=lean, imported_endpoint=records[0],
                  candidate_preservation=preservation,
                  primary_contracts=PRIMARY_CONTRACTS,
                  artifact_sha256={str(p.relative_to(WORK)): digest(p) for p in artifacts},
                  kernel_output=kernel.stdout, logs=logs)


def collect():
    started = time.monotonic()
    amendment.check()
    if read(ROOT / 'assurance/m4-parent-review-correction.json')['preserved_sha256'] != REVIEW_CHECKPOINT:
        raise ValueError('rejected review checkpoint inventory differs')
    bridge.connection().verify_hashes(REVIEW_CHECKPOINT)
    promotion = read(ROOT / 'assurance/m4-parent-promotion.json')
    bridge.connection().verify_hashes(promotion['reviewed_files_sha256'])
    log = ROOT / promotion['independent_focused_check']['log_path']
    if (digest(log) != promotion['independent_focused_check']['compressed_log_sha256']
            or amendment.sha(gzip.decompress(log.read_bytes())) !=
            promotion['independent_focused_check']['uncompressed_log_sha256']):
        raise ValueError('independent promotion receipt differs')
    before, identity = sources(), candidate.baseline_identity()
    report = collect_proofs()
    reviewed = read(ROOT / 'assurance/m4-parent-corrected-review-claims.json')
    validate_claims(reviewed, report)
    # The early compiler interface is a separate experiment, not a discharged M4 edge.
    load(ROOT / 'm4/feasibility/check.py', 'parent_compiler_feasibility').check()
    if before != sources() or identity != candidate.baseline_identity():
        raise ValueError('parent source or dependency changed during checking')
    report.update(source_sha256=before, baseline=identity[0], exports=identity[1],
                  elapsed_seconds=round(time.monotonic() - started, 3))
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Parent checked: {len(report["rocq_declarations"])} Rocq declarations and '
          f'{len(report["lean_declarations"])} Lean theorems; '
          f'{len(report["artifact_sha256"])} compiled artifacts; complete M4 remains open.', flush=True)
    return report


def check():
    actual, expected, evidence = collect(), read(MANIFEST), read(EVIDENCE)
    validate_claims(expected, actual)
    archived = json.loads(gzip.decompress(SNAPSHOT.read_bytes()))
    if digest(SNAPSHOT) != evidence['proof_output_sha256']:
        raise ValueError('parent raw proof archive receipt differs')
    validate_claims(archived, actual)
    validate_evidence(evidence, archived, actual, digest(MANIFEST))
    bridge.connection().verify_hashes(evidence['archived_receipts_sha256'])
    print('Maintained parent statements, foundations, inputs, histories and artifacts match.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collect', action='store_true', help='write only an ignored report for statement review')
    args = parser.parse_args()
    try:
        collect() if args.collect else check()
    except subprocess.CalledProcessError as error:
        print(error.stdout, file=sys.stderr)
        raise
