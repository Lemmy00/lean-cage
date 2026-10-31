#!/usr/bin/env python3
"""Replay the bounded experiment; never refresh reviewed expectations."""
# §AR-m4-native.evidence: Reject source, proof, frontend and assumption drift.
import hashlib
import gzip
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile

from bootstrap import ROOT, WORK, digest, environment
from extract import extract, identities, NAMES
from prover import compile_file, flags

PROOFS = ['Codec.v', 'Effects.v', 'Attempt.v']
MANIFEST = ROOT / 'assurance/m4-claims.json'
EVIDENCE = ROOT / 'assurance/m4-evidence.json'
COQ_ALLOWED = {
    'ClassicalDedekindReals.sig_not_dec', 'ClassicalDedekindReals.sig_forall_dec',
    'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic',
    'Events.external_functions_sem', 'Events.inline_assembly_sem',
}
LEAN_TARGETS = [
    'LeanCageM3.decodeResult', 'LeanCageM3.resultValid', 'LeanCageM3.decodeResult_valid',
    'LeanCageM3.observe', 'LeanCageM3.private_report_knowledge',
    'LeanCageM3.report_loss_preserves_entry', 'LeanCageM3.cancel_not_completion',
    'LeanCageM3.release_requires_extinction', 'LeanCageM3.entry_requires_receipts',
    'LeanCageM3.reachable_entry_ordered', 'LeanCageM2.lost_report_unknown',
    'LeanCageM2.entry_requires_plan',
]


def run(command, **kwargs):
    result = subprocess.run([str(x) for x in command], cwd=WORK / 'input',
                            env=environment(), capture_output=True, text=True,
                            timeout=180, **kwargs)
    if result.returncode:
        raise ValueError(f'command failed: {command}\n{result.stdout}{result.stderr}')
    return result.stdout + result.stderr


def verify_tools():
    pins = json.loads((ROOT / 'm4/toolchain-lock.json').read_text())
    archive = WORK / 'compcert.tar.gz'
    if digest(archive) != pins['compcert']['sha256']:
        raise ValueError('CompCert archive identity differs')
    # Check all archived source files, not just the handful referenced by proofs.
    count = 0
    with tarfile.open(archive) as tar:
        for member in tar:
            if not member.isfile():
                continue
            relative = Path(*Path(member.name).parts[1:])
            path = WORK / 'CompCert' / relative
            if path.read_bytes() != tar.extractfile(member).read():
                raise ValueError(f'CompCert source drift: {relative}')
            count += 1
    for package in pins['packages']:
        path = WORK / 'packages' / package['url'].rsplit('/', 1)[1]
        if digest(path) != package['sha256']:
            raise ValueError(f'package identity differs: {path}')
        # Verify the actual prover/compiler/library files against their pinned packages.
        with subprocess.Popen(['dpkg-deb', '--fsys-tarfile', str(path)], stdout=subprocess.PIPE) as process:
            with tarfile.open(fileobj=process.stdout, mode='r|') as tar:
                for member in tar:
                    target = WORK / 'root' / member.name.removeprefix('./')
                    if member.isfile():
                        if target.read_bytes() != tar.extractfile(member).read():
                            raise ValueError(f'extracted tool drift: {target}')
                    elif member.issym() and (not target.is_symlink() or os.readlink(target) != member.linkname):
                        raise ValueError(f'extracted tool link drift: {target}')
            if process.wait():
                raise ValueError('could not inspect pinned package payload')
    notices = {str(p.relative_to(WORK)): digest(p)
               for p in sorted((WORK / 'root/usr/share/doc').glob('*/copyright'))}
    if len(notices) < len(pins['packages']):
        raise ValueError('missing extracted package notices')
    return {'archive_files_checked': count, 'notices': notices,
            'compcert_license_sha256': digest(WORK / 'CompCert/LICENSE')}


def declarations():
    result = []
    for filename in PROOFS:
        source = (ROOT / 'm4' / filename).read_text()
        source = re.sub(r'\(\*.*?\*\)', '', source, flags=re.S)
        if re.search(r'\b(?:Admitted|admit|Axiom|Parameter)\b', source):
            raise ValueError(f'forbidden authored admission/axiom: {filename}')
        for name in re.findall(r'^(?:Theorem|Lemma|Example)\s+([A-Za-z0-9_]+)', source, re.M):
            result.append(filename[:-2] + '.' + name)
    return result


def coq_inventory():
    names = declarations()
    commands = ['From Coq Require Import List.', 'Require Import Codec Effects Attempt.',
                'Set Printing All.', 'Set Printing Width 1000000.']
    for i, name in enumerate(names):
        commands += [f'Redirect "type-{i}" Check @{name}.',
                     f'Redirect "axioms-{i}" Print Assumptions {name}.']
    (WORK / 'input/Audit.v').write_text('\n'.join(commands) + '\n')
    result = compile_file('Audit.v')
    if result.returncode:
        raise ValueError(result.stdout + result.stderr)
    records = []
    for i, name in enumerate(names):
        full_type = (WORK / f'input/type-{i}.out').read_text().strip()
        assumptions = (WORK / f'input/axioms-{i}.out').read_text().strip()
        axioms = re.findall(r'^([A-Za-z0-9_.]+)(?:\s*:|\s*$)', assumptions, re.M)
        axioms = sorted(set(axioms) - {'Axioms'})
        if set(axioms) - COQ_ALLOWED:
            raise ValueError(f'unknown transitive Coq assumptions: {name}: {axioms}')
        records.append({'name': name, 'full_type': full_type,
                        'transitive_assumptions': assumptions, 'assumption_names': axioms})
    return records


def lean_inventory():
    path = ROOT / 'scripts/audit_m3.py'
    spec = importlib.util.spec_from_file_location('m4_m3_audit', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    records = module.query_environment(declarations=[n for n in LEAN_TARGETS if n.startswith('LeanCageM3.')])
    records += module.M2.query_environment(declarations=[n for n in LEAN_TARGETS if n.startswith('LeanCageM2.')])
    if {r['name'] for r in records} != set(LEAN_TARGETS):
        raise ValueError('Lean target inventory differs')
    for record in records:
        if set(record['axioms']) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError(f'unknown Lean target assumptions: {record}')
    return records


def sources():
    paths = [*sorted((ROOT / 'm4').glob('*')),
             ROOT / 'scripts/check_m4.sh', ROOT / 'docs/architecture/AR-m4-native.md',
             ROOT / 'docs/architecture/README.md', ROOT / 'docs/roadmap.md']
    return {str(p.relative_to(ROOT)): digest(p) for p in paths if p.is_file()}


def validate_input_artifacts(expected, directory):
    for name, key in [('slice.c', 'slice_sha256'), ('slice.i', 'preprocessed_sha256'),
                      ('Slice.v', 'clight_ast_sha256')]:
        if digest(directory / name) != expected[key]:
            raise ValueError(f'stale or tampered semantics input: {name}')


def runtime_profile():
    candidates = [WORK / 'CompCert/clightgen', WORK / 'CompCert/compcert.ini',
                  WORK / 'root/usr/bin/coqc', WORK / 'root/usr/bin/coqchk',
                  WORK / 'root/usr/bin/ocamlopt.opt', WORK / 'root/usr/bin/menhir']
    for name in ['gcc', 'cc', 'make', 'as', 'ld']:
        candidates.append(Path(shutil.which(name, path=environment()['PATH'])).resolve())
    candidates.append(Path(run(['gcc', '-print-prog-name=cc1']).strip()).resolve())
    libraries = set()
    for path in candidates:
        if path.suffix == '.ini':
            continue
        result = subprocess.run(['ldd', str(path)], capture_output=True, text=True, timeout=10)
        for name in re.findall(r'(/[^\s()]+)', result.stdout):
            if Path(name).is_file():
                libraries.add(Path(name).resolve())
    paths = sorted(set(candidates) | libraries)
    return {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p): digest(p) for p in paths}


def collect():
    (WORK / 'input').mkdir(parents=True, exist_ok=True)
    tool_report = verify_tools()
    source = (ROOT / 'native/leancage_m3.c').read_text()
    (WORK / 'input/slice.c').write_text(extract(source))
    for filename in ['abi.h', 'witness.c', 'abi_check.c']:
        shutil.copyfile(ROOT / 'm4' / filename, WORK / 'input' / filename)
    frontend_command = [WORK / 'CompCert/clightgen', '-normalize', '-fstruct-passing',
                        '-dprepro', '-o', 'Slice.v', 'slice.c']
    run(frontend_command)
    ast = (WORK / 'input/Slice.v').read_text()
    for name in [*NAMES, 'm4_collect_failure']:
        if f'Definition f_{name} :=' not in ast:
            raise ValueError(f'frontend discarded a slice function: {name}')
    if 'Definition version := "3.17".' not in ast:
        raise ValueError('assigned CompCert commit version differs')
    logs = {}
    for filename in ['Slice.v', *PROOFS]:
        result = compile_file(filename)
        if result.returncode:
            raise ValueError(result.stdout + result.stderr)
        logs[filename] = result.stdout + result.stderr
    # The attempt must expose its unresolved return-bound goal, with no theorem exported.
    if 'Int64.signed n = -1' not in logs['Attempt.v'] or 'CALL : external_functions_sem' not in logs['Attempt.v']:
        raise ValueError('missing reproducible effect proof obstruction')
    records = coq_inventory()
    kernel_log = run([WORK / 'root/usr/bin/coqchk', '-silent', *flags(), 'Codec', 'Effects', 'Attempt'])
    run(['cc', '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror', '-fPIC', '-shared',
         'witness.c', '-o', 'witness.so'])
    run(['cc', '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror', 'abi_check.c', '-o', 'abi_check'])
    run([WORK / 'input/abi_check'])
    header_output = run(['cc', '-std=c11', '-M', 'abi_check.c'])
    headers = sorted({Path(x).resolve() for x in header_output.replace('\\\n', ' ').split()[1:]
                      if x != '\\' and Path(x).is_absolute()})
    # Dependencies are emitted as absolute host header paths, plus local experiment inputs.
    host_headers = {str(p): digest(p) for p in headers if p.is_file() and not p.is_relative_to(ROOT)}
    witness_log = run(['python3', ROOT / 'm4/test_witness.py'])
    lean = lean_inventory()
    identities_record = {
        'native_helper_sha256': digest(ROOT / 'native/leancage_m3.c'),
        'functions': identities(source),
        'slice_sha256': digest(WORK / 'input/slice.c'),
        'preprocessed_sha256': digest(WORK / 'input/slice.i'),
        'clight_ast_sha256': digest(WORK / 'input/Slice.v'),
        'slice_c_lines': len((WORK / 'input/slice.c').read_text().splitlines()),
        'abi_c_lines': len((ROOT / 'm4/abi.h').read_text().splitlines()),
        'readable_c_lines': len((WORK / 'input/slice.c').read_text().splitlines()) + len((ROOT / 'm4/abi.h').read_text().splitlines()),
    }
    report = {
        'source_sha256': sources(), 'source_connection': identities_record,
        'rocq_declarations': records, 'lean_targets': lean,
        'tools': tool_report, 'host_header_sha256': host_headers,
        'runtime_inputs_sha256': runtime_profile(),
        'versions': {name: run(command).strip() for name, command in {
            'coq': [WORK / 'root/usr/bin/coqc', '--version'],
            'compcert': [WORK / 'CompCert/clightgen', '-version'],
            'ocaml': [WORK / 'root/usr/bin/ocamlc', '-version'],
            'menhir': [WORK / 'root/usr/bin/menhir', '--version'],
            'gcc': ['cc', '--version'],
        }.items()},
        'artifact_sha256': {name: digest(WORK / 'input' / name) for name in
                            ['Slice.vo', 'Codec.vo', 'Effects.vo', 'Attempt.vo', 'witness.so', 'abi_check']},
        'frontend_sha256': digest(WORK / 'CompCert/clightgen'),
        'prover_sha256': digest(WORK / 'root/usr/bin/coqc'),
        'logs': logs, 'witness_log': witness_log, 'coqchk_log': kernel_log,
    }
    (WORK / 'check-report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def check():
    expected = json.loads(MANIFEST.read_text())
    evidence = json.loads(EVIDENCE.read_text())
    # Reject tracked source drift before invoking the tools.
    if sources() != expected['source_sha256']:
        raise ValueError('M4 authored source identities differ from the reviewed manifest')
    for name, expected_hash in evidence['preserved_baseline_sha256'].items():
        if digest(ROOT / name) != expected_hash:
            raise ValueError(f'preserved baseline changed: {name}')
    for name, expected_hash in evidence['runtime_inputs_sha256'].items():
        path = Path(name) if Path(name).is_absolute() else ROOT / name
        if digest(path) != expected_hash:
            raise ValueError(f'proof/frontend runtime input changed before execution: {name}')
    for name, expected_hash in evidence['archived_input_sha256'].items():
        if digest(ROOT / name) != expected_hash:
            raise ValueError(f'archived semantics input differs: {name}')
    for name, expected_hash in evidence['uncompressed_sha256'].items():
        if hashlib.sha256(gzip.decompress((ROOT / name).read_bytes())).hexdigest() != expected_hash:
            raise ValueError(f'compressed raw evidence differs: {name}')
    actual = collect()
    for key in ['rocq_declarations', 'lean_targets']:
        if actual[key] != expected[key]:
            raise ValueError(f'reviewed full types/assumptions differ: {key}')
    validate_input_artifacts(evidence['source_connection'], WORK / 'input')
    if actual['source_connection'] != evidence['source_connection']:
        raise ValueError('maintained helper/preprocessed/Clight input identity differs')
    if actual['frontend_sha256'] != evidence['frontend_sha256']:
        raise ValueError('frontend executable differs from the reviewed local build')
    if actual['tools'] != evidence['tools']:
        raise ValueError('tool source/license identities differ')
    if actual['runtime_inputs_sha256'] != evidence['runtime_inputs_sha256']:
        raise ValueError('proof/frontend runtime library selection differs')
    if actual['versions'] != evidence['versions'] or actual['host_header_sha256'] != evidence['host_header_sha256']:
        raise ValueError('tool/host ABI profile differs; review a new profile explicitly')
    print(f'M4 checked: {len(actual["rocq_declarations"])} Rocq declarations, '
          f'{len(actual["lean_targets"])} Lean target types/axioms; '
          f'{actual["source_connection"]["readable_c_lines"]} C lines; 11 witness tests; coqchk passed')
    print('Outcome: pure codec feasibility checked; count-only effect route rejected; '
          'full native simulation, whole-slice memory safety and Lean bridge UNPROVED')


if __name__ == '__main__':
    check()
