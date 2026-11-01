#!/usr/bin/env python3
"""Replay the bounded controller source connection without refreshing claims."""
# §AR-m4-controller.extraction: Actual source, full propositions, foundations and parent identities.
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

from extract_number import ROOT, extract, identity

DIRECTORY = ROOT / 'm4/controller'
WORK = ROOT / '.tools/m4/controller'
MANIFEST = ROOT / 'assurance/m4-controller-number-claims.json'
EVIDENCE = ROOT / 'assurance/m4-controller-number-evidence.json'
MODULES = ['NumberMath', 'NumberStructure', 'NumberMemory', 'NumberWords',
           'NumberValues', 'NumberEntry', 'NumberControl', 'NumberStorage',
           'NumberIterations', 'NumberLoop', 'NumberInitial', 'NumberSource',
           'NumberSafety', 'NumberAllocation', 'NumberWitnesses', 'NumberSamples']
FRAME_ARCHIVES = {
    'assurance/m4-frames-claims.json': '80b44430a559b0c965dccad7dab08e0c78c6f3d6b3eb0a19e053830d89dd49e0',
    'assurance/m4-frames-evidence.json': 'b15a4fa57aadeb4b6dbdee97ce5648d34a5e5661a4494faa88963294258727fd',
}


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


sys.path.insert(0, str(ROOT / 'm4/bridge'))
bridge = load(ROOT / 'm4/bridge/check.py', 'controller_bridge_check')
profile = load(ROOT / 'm4/bridge/profile.py', 'controller_bridge_profile')
bootstrap = load(ROOT / 'm4/bootstrap.py', 'controller_native_bootstrap')
digest = profile.digest


def read(path):
    return json.loads(Path(path).read_text())


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / p for p in FRAME_ARCHIVES]
    paths += [ROOT / p for p in [
        'docs/architecture/AR-m4-controller.md',
        'docs/decisions/architectural/DA-m4-controller.md',
        'docs/reviews/M4-controller-number.md',
        'assurance/m4-bridge-claims.json', 'assurance/m4-bridge-evidence.json',
        'm4/extract.py', 'm4/bootstrap.py', 'm4/bridge/check.py',
    ]]
    return dict(sorted((bridge.sources() | {str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def inventory():
    if {p.stem for p in DIRECTORY.glob('*.v')} != set(MODULES):
        raise ValueError('controller module inventory differs')
    result = []
    for module in MODULES:
        source = re.sub(r'\(\*.*?\*\)', '', (DIRECTORY / (module + '.v')).read_text(), flags=re.S)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|vm_cast_no_check|native_cast_no_check)\b', source):
            raise ValueError('unfinished or unchecked controller proof')
        if re.search(r'Unset\s+(?:Guard|Positivity|Universe|Elimination)\s+Checking', source):
            raise ValueError('disabled controller kernel check')
        names = re.findall(r'^\s*(?:Theorem|Lemma|Example|Corollary|Fact|Remark|Proposition)\s+(\w+)', source, re.M)
        if not names:
            raise ValueError('empty controller theorem inventory')
        result += ['LeanCageController.' + module + '.' + name for name in names]
    return result


def validate_parent(claims, evidence, actual):
    bridge.validate_claims(claims, actual)
    for key in ['artifact_sha256', 'tool_artifact_sha256', 'replayed_sources_sha256', 'export_sha256']:
        if evidence[key] != actual[key]:
            raise ValueError('complete frame checkpoint changed: ' + key)


def parent_identity():
    gate = bridge.connection()
    gate.verify_hashes(FRAME_ARCHIVES)
    archived_claims = read(ROOT / 'assurance/m4-frames-claims.json')
    archived_evidence = read(ROOT / 'assurance/m4-frames-evidence.json')
    actual = read(profile.WORK / 'report.json')
    active = read(bridge.EVIDENCE)
    validate_parent(archived_claims, archived_evidence, actual)
    bridge.validate_claims(read(bridge.MANIFEST), actual)
    if actual['source_sha256'] != bridge.sources() or actual['source_sha256'] != active['source_sha256']:
        raise ValueError('parent bridge source replay is stale')
    for key in ['artifact_sha256', 'tool_artifact_sha256', 'replayed_sources_sha256', 'export_sha256']:
        if actual[key] != active[key]:
            raise ValueError('active parent bridge identity differs: ' + key)
    if active['claims_sha256'] != digest(bridge.MANIFEST) or active['full_bridge_complete'] is not False:
        raise ValueError('parent claim identity or boundary differs')
    gate.verify_hashes(actual['artifact_sha256'], profile.WORK)
    gate.verify_hashes(actual['tool_artifact_sha256'], profile.WORK)
    gate.verify_hashes(active['archived_receipts_sha256'])
    if digest(profile.WORK / 'normalized-decoder.ndjson') != actual['export_sha256']:
        raise ValueError('parent exported decoder changed')
    gate.validate_obligations(read(ROOT / 'assurance/m4-obligations.json'))
    return {key: actual[key] for key in [
        'artifact_sha256', 'tool_artifact_sha256', 'replayed_sources_sha256', 'export_sha256']}


def frontend_identity():
    evidence = read(ROOT / 'assurance/m4-evidence.json')
    executable = ROOT / '.tools/m4/CompCert/clightgen'
    if digest(executable) != evidence['frontend_sha256']:
        raise ValueError('pinned native frontend differs')
    for path, expected in evidence['runtime_inputs_sha256'].items():
        resolved = Path(path) if Path(path).is_absolute() else ROOT / path
        if digest(resolved) != expected:
            raise ValueError('native frontend runtime input differs: ' + path)
    return {'frontend_sha256': digest(executable), 'runtime_inputs_sha256': evidence['runtime_inputs_sha256']}


def flags(checker=False):
    return profile.flags(checker=checker) + ['-Q', str(WORK / 'proofs'), 'LeanCageController']


def validate_claims(expected, actual):
    if not actual['rocq_declarations'] or expected['rocq_declarations'] != actual['rocq_declarations']:
        raise ValueError('controller full statement or foundation inventory differs')


def collect():
    started = time.monotonic()
    profile.verify_tools()
    names = inventory()
    before = sources()
    parent = parent_identity()
    frontend = frontend_identity()
    for directory in ['input', 'proofs']:
        (WORK / directory).mkdir(parents=True, exist_ok=True)
    source = (ROOT / 'native/leancage_m3.c').read_text()
    generated = extract(source)
    (WORK / 'input/number.c').write_text(generated)
    provenance = identity(source, generated)
    command = [str(ROOT / '.tools/m4/CompCert/clightgen'), '-normalize', '-fstruct-passing',
               '-dprepro', '-o', 'NumberSlice.v', 'number.c']
    front = subprocess.run(command, cwd=WORK / 'input', env=bootstrap.environment(), text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=60)
    ast = (WORK / 'input/NumberSlice.v').read_text()
    if 'Definition version := "3.17".' not in ast or 'Definition f_number :=' not in ast:
        raise ValueError('unexpected controller frontend output')
    if re.findall(r'^Definition f_(\w+) :=', ast, re.M) != ['number']:
        raise ValueError('unexpected controller function inventory')
    logs = {'frontend': front.stdout}
    for module in ['NumberSlice', *MODULES]:
        original = WORK / 'input/NumberSlice.v' if module == 'NumberSlice' else DIRECTORY / (module + '.v')
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(original, path)
        logs[module] = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=WORK / 'proofs').stdout
    query = ['From LeanCageController Require Import ' + ' '.join(MODULES) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    for i, name in enumerate(names):
        query += [f'Redirect "controller-type-{i}" Check @{name}.',
                  f'Redirect "controller-foundations-{i}" Print Assumptions {name}.']
    path = WORK / 'proofs/ControllerAudit.v'
    path.write_text('\n'.join(query) + '\n')
    logs['audit'] = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=path.parent).stdout
    records = []
    for i, name in enumerate(names):
        statement = (WORK / f'proofs/controller-type-{i}.out').read_text().strip()
        assumptions = (WORK / f'proofs/controller-foundations-{i}.out').read_text().strip()
        axioms, uip = bridge.foundations(assumptions)
        if '...' in statement or uip:
            raise ValueError('truncated statement or unreviewed controller logical model')
        records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                        'assumption_names': axioms, 'definitional_uip': uip})
    kernel = profile.run(['rocq', 'check', '-silent', *flags(checker=True),
                          *['LeanCageController.' + name for name in ['NumberSlice', *MODULES]]],
                         cwd=WORK / 'proofs', timeout=300)
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/controller',
                            '-p', 'test_gate.py', '-v'], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30)
    logs['gate_tests'] = tests.stdout
    if before != sources() or parent != parent_identity() or frontend != frontend_identity():
        raise ValueError('controller or parent inputs changed during replay')
    report = {'schema_version': 1, 'source_sha256': before, 'rocq_declarations': records,
              'source_connection': provenance, 'frontend_command': command, 'frontend': frontend,
              'parent': parent, 'artifact_sha256': {
                  str(p.relative_to(WORK)): digest(p) for p in [WORK / 'input/number.c',
                      WORK / 'input/number.i', WORK / 'input/NumberSlice.v',
                      *[WORK / 'proofs' / (name + '.vo') for name in ['NumberSlice', *MODULES]]]},
              'kernel_output': kernel.stdout, 'logs': logs,
              'elapsed_seconds': round(time.monotonic() - started, 3)}
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Controller replay passed: {len(records)} full theorem records, source extraction and independent kernel check.', flush=True)
    return report


def check():
    claims, evidence = read(MANIFEST), read(EVIDENCE)
    report = collect()
    validate_claims(claims, report)
    for key in ['source_sha256', 'source_connection', 'frontend_command', 'frontend', 'parent', 'artifact_sha256']:
        if report[key] != evidence[key]:
            raise ValueError('reviewed controller identity differs: ' + key)
    if evidence['claims_sha256'] != digest(MANIFEST) or evidence['full_m4_complete'] is not False:
        raise ValueError('controller claim identity or boundary differs')
    bridge.connection().verify_hashes(evidence['archived_receipts_sha256'])
    raw = gzip.decompress((ROOT / 'assurance/m4-number-slice.v.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != report['artifact_sha256']['input/NumberSlice.v']:
        raise ValueError('archived controller AST differs')
    print('Exact decimal source parsing checked; plan encoding, controller ordering and Linux/executable composition remain OPEN.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--collect', action='store_true', help='write an ignored candidate report; never refresh expectations')
    args = parser.parse_args()
    try:
        collect() if args.collect else check()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print('Controller replay failed: ' + str(error), file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stdout, file=sys.stderr)
        sys.exit(1)
