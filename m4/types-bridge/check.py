#!/usr/bin/env python3
"""Check the recursive representation bridge and its actual CompCert type codecs."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-routes.reporting.types: Complete statements and both representation round trips.
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

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path(__file__).resolve().parent
WORK = ROOT / '.tools/m4/types-bridge'
PROOFS = WORK / 'proofs'
RECORD = ROOT / 'assurance/m4-type-bridge.json'


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


profile = load(ROOT / 'm4/bridge/profile.py', 'type_bridge_profile')
inventory = load(ROOT / 'm4/parent/inventory.py', 'type_bridge_inventory')
saved_profile = sys.modules.get('profile')
try:
    sys.modules['profile'] = profile
    foundation = load(ROOT / 'm4/bridge/check.py', 'type_bridge_foundations')
finally:
    if saved_profile is None:
        del sys.modules['profile']
    else:
        sys.modules['profile'] = saved_profile


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def verify_dependency_amendment():
    record = read(ROOT / 'assurance/m4-type-bridge-dependency-amendment.json')
    archive = ROOT / 'assurance/m4-type-bridge-dependency-before.json.gz'
    if digest(archive) != record['before_archive_sha256']:
        raise ValueError('dependency preimage archive differs')
    before = json.loads(gzip.decompress(archive.read_bytes()))
    route_path = 'assurance/m4-route-feasibility.json'
    docs = ['docs/architecture/AR-m4-routes.md',
            'docs/decisions/architectural/DA-m4-routes.md']
    if set(before) != {route_path, *docs} or set(record['files']) != set(before):
        raise ValueError('dependency amendment scope differs')
    for path, row in record['files'].items():
        if (hashlib.sha256(before[path].encode()).hexdigest() != row['before_sha256']
                or digest(ROOT / path) != row['after_sha256']):
            raise ValueError('dependency amendment bytes differ: ' + path)
    old_route = hashlib.sha256(before[route_path].encode()).hexdigest()
    if (old_route != record['before_route_sha256']
            or old_route != read(ROOT / 'assurance/m4-parent-validation.json')['route_evidence_sha256']
            or digest(ROOT / 'assurance/m4-obligations.json') != record['original_obligations_sha256']):
        raise ValueError('original route or obligation evidence differs')
    expected = json.loads(before[route_path])
    for path in docs:
        if expected['source_sha256'][path] != record['files'][path]['before_sha256']:
            raise ValueError('original route documentation binding differs')
        expected['source_sha256'][path] = record['files'][path]['after_sha256']
    if read(ROOT / route_path) != expected:
        raise ValueError('dependency amendment changes a route proof/result field')


def flags(checker=False):
    old = str(profile.WORK / 'rocq-lean-import/src')
    return [str(WORK / 'importer/src') if x == old else x
            for x in profile.flags(checker=checker)]


def run(command, *, cwd=PROOFS, timeout=180):
    return profile.run(command, cwd=cwd, timeout=timeout).stdout


def compile_file(path):
    return run(['rocq', 'c', '-q', *flags(), str(path)])


def verify_sources(derivation):
    if digest(DIRECTORY / 'importer.patch') != derivation['patch_sha256']:
        raise ValueError('derived importer patch differs')
    base = profile.WORK / 'rocq-lean-import'
    private = WORK / 'importer'
    changed = derivation['base_source_sha256']
    for name, data, _ in profile.archive_files(profile.WORK / 'importer-source.tar.gz'):
        rel = str(name)
        base_hash = digest(base / name)
        if rel in changed:
            if base_hash != changed[rel]['before']:
                raise ValueError('accepted importer input differs: ' + rel)
            expected = changed[rel]['after']
        else:
            expected = base_hash
        if digest(private / name) != expected:
            raise ValueError('private importer source differs: ' + rel)
    closure = ROOT / '.tools/m4/routes/ported-step.ndjson'
    route = read(ROOT / 'assurance/m4-route-feasibility.json')
    if (digest(closure) != derivation['ported_closure_sha256']
            or derivation['ported_closure_sha256'] != route['closure_sha256']
            or (ROOT / 'm3/lean-toolchain').read_text().strip() != route['lean_toolchain']):
        raise ValueError('actual exported CC.Step closure differs')


def prepare(derivation):
    profile.verify_tools()
    verify_dependency_amendment()
    WORK.mkdir(parents=True, exist_ok=True)
    private = WORK / 'importer'
    if not private.exists():
        shutil.copytree(profile.WORK / 'rocq-lean-import', private)
        run(['patch', '-p1', '--forward', '-i', str(DIRECTORY / 'importer.patch')], cwd=private)
    verify_sources(derivation)
    return run(['make', '-B', '-j2'], cwd=private)


def source_hashes():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / 'docs/architecture/AR-m4-routes.md',
              ROOT / 'docs/decisions/architectural/DA-m4-routes.md',
              ROOT / 'scripts/check_m4_types.sh',
              ROOT / 'assurance/m4-type-bridge-dependency-amendment.json',
              ROOT / 'assurance/m4-type-bridge-dependency-before.json.gz',
              ROOT / 'm3/lean-toolchain', ROOT / 'm4/bridge/toolchain-lock.json']
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}


def compiled_names(signature, module):
    """Extend the maintained compiled-signature reader for the actual mutual pair."""
    try:
        return inventory.checked_declarations(signature, module)
    except ValueError:
        short = module.rsplit('.', 1)[-1]
        match = re.fullmatch(r'Module\s+' + re.escape(short) + r'\s*:=\s*Struct\s+(.*)\s+End',
                             signature.strip(), re.S)
        if not match or '...' in signature:
            raise ValueError('unsupported or truncated checked module signature')
        result = []
        for field in inventory.commands(match[1]):
            normal = re.sub(r'\s+', ' ', field).strip()
            normal = re.sub(r'^Variant\b', 'Inductive', normal)
            if normal.startswith('Record '):
                normal = re.sub(r'\s+as\s+' + inventory.IDENT + r'$', '', normal)
            empty = re.fullmatch(r'Inductive\s+(' + inventory.IDENT + r')\b(.+)\s*:=\s*', normal)
            if empty:
                inventory.outer_split(empty[2], '\0')
                result.append(module + '.' + empty[1])
                continue
            if normal.startswith('Inductive ') and len(inventory.outer_split(normal, ' with ')) > 1:
                packets = inventory.outer_split(normal[len('Inductive '):], ' with ')
                for packet in packets:
                    result += inventory.checked_declarations(
                        f'Module {short} := Struct Inductive {packet}. End', module)
            else:
                result += inventory.checked_declarations(f'Module {short} := Struct {normal}. End', module)
        if not result or len(set(result)) != len(result):
            raise ValueError('empty or duplicate compiled declaration inventory')
        return result


def negative(name, body, expected):
    path = PROOFS / (name + '.v')
    path.write_text(body)
    try:
        compile_file(path)
    except subprocess.CalledProcessError as error:
        if error.returncode != 1 or expected not in error.stdout:
            raise ValueError('negative control failed differently: ' + name + '\n' + error.stdout)
        return error.stdout
    raise ValueError('negative control unexpectedly accepted: ' + name)


def collect():
    derivation = read(DIRECTORY / 'derivation.json')
    logs = {'build': prepare(derivation)}
    before = source_hashes()
    PROOFS.mkdir(exist_ok=True)
    modules = derivation['modules']
    for module in modules:
        path = PROOFS / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[module] = compile_file(path)
        print('Checked ' + module, flush=True)
    prelude = ('From LeanImport Require Import Lean.\n'
               'Require Import TypePrefix TypeRecursors.\n'
               'Set Lean Error Mode "Fail".\nUnset Lean Skip Missing Quotient.\n')
    command = 'Lean Check Recursors "CC.Ty" "cc_ty_type" "cc_ty_sprop" "cc_ty_list_type" "cc_ty_list_sprop".\n'
    logs['pending'] = negative('Pending', prelude + 'Lean Assert Complete.\n', 'unchecked deferred recursor')
    logs['guard'] = negative('Guard', prelude + 'Unset Guard Checking.\n' + command,
                             'requires all kernel typing checks')
    logs['universe_arity'] = negative('UniverseArity', prelude + command.replace('"cc_ty_type"', '"cc_ty_sprop"'),
                                     'helper universe arity differs')
    wrong = ('Set Universe Polymorphism.\n'
             'Polymorphic Definition wrong_root@{u} (T : Type@{u}) : Type@{u} := T.\n')
    logs['signature'] = negative('Signature', prelude + wrong + command.replace('"cc_ty_type"', '"wrong_root"'),
                                 'has type')
    opaque = ('Set Universe Polymorphism.\n'
              'Polymorphic Definition opaque_root@{u} :\n'
              ' ltac:(let T := type of (@cc_ty_type@{u}) in exact T).\n'
              'Proof. exact (@cc_ty_type@{u}). Qed.\n')
    logs['reduction'] = negative('Reduction', prelude + opaque + command.replace('"cc_ty_type"', '"opaque_root"'),
                                 'Checking reduction CC.Ty.rec_1 constructor List.cons instance 0')
    # §AR-m4-routes.reporting.types: Inverse laws must not hide a tag permutation.
    theory = (DIRECTORY / 'TyRelation.v').read_text()
    start, stop = theory.index('Definition signedness_out'), theory.index('Definition floatsize_out')
    permuted = theory[start:stop].replace('Ctypes.Signed', 'SWAPPED_SIGNED')
    permuted = permuted.replace('Ctypes.Unsigned', 'Ctypes.Signed').replace('SWAPPED_SIGNED', 'Ctypes.Unsigned')
    logs['tags'] = negative('PermutedTags', theory[:start] + permuted + theory[stop:], 'Unable to unify')
    query = ['Require Import ' + ' '.join(modules) + '.', 'Set Printing All.',
             'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    for index, module in enumerate(modules):
        query.append(f'Redirect "signature-{index}" Print Module {module}.')
    path = PROOFS / 'Environment.v'
    path.write_text('\n'.join(query) + '\n')
    logs['environment'] = compile_file(path)
    names = []
    signatures = {}
    for index, module in enumerate(modules):
        signature = (PROOFS / f'signature-{index}.out').read_text()
        signatures[module] = signature
        names += compiled_names(signature, module)
    if len(names) != len(set(names)):
        raise ValueError('duplicate checked declarations')
    query = ['Require Import ' + ' '.join(modules) + '.', 'Set Printing All.',
             'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    for index, name in enumerate(names):
        query += [f'Redirect "type-{index}" Check @{name}.',
                  f'Redirect "axioms-{index}" Print Assumptions {name}.']
    path = PROOFS / 'Audit.v'
    path.write_text('\n'.join(query) + '\n')
    logs['audit'] = compile_file(path)
    records = []
    for index, name in enumerate(names):
        statement = (PROOFS / f'type-{index}.out').read_text().strip()
        assumptions = (PROOFS / f'axioms-{index}.out').read_text().strip()
        # The imported modules qualify existing SProp model names when they clash
        # with Stdlib names. Preserve the raw report and validate only these aliases.
        validation = re.sub(
            r'(?m)^(?:(?:LeanImport\.)?Lean|TypePrefix|StmtPrefix)\.(eq|eq_inst1|True|HEq|HEq_inst1)(?= relies on definitional UIP\.)',
            r'\1', assumptions)
        axioms, uip = foundation.foundations(validation)
        if axioms or '...' in statement:
            raise ValueError('unexpected axiom or truncated type: ' + name)
        records.append(dict(name=name, full_type=statement,
                            transitive_assumptions=assumptions, definitional_uip=uip))
    logs['kernel'] = run(['rocq', 'check', '-silent', *flags(checker=True), *modules], timeout=300)
    verify_sources(derivation)
    if source_hashes() != before:
        raise ValueError('authored inputs changed during replay')
    report = dict(schema_version=1, full_m4_complete=False, ordinary_lean_security_claim=False,
                  original_obligations_closed=[],
                  claim='Checked recursive representations and CompCert type bijection; full semantics correspondence open',
                  source_sha256=before, declarations=records,
                  artifacts={m + '.vo': digest(PROOFS / (m + '.vo')) for m in modules})
    raw = dict(logs=logs, checked_module_signatures=signatures)
    (WORK / 'collected.json').write_text(json.dumps(report, indent=2) + '\n')
    with gzip.GzipFile(filename=str(WORK / 'collected-output.json.gz'), mode='wb', mtime=0) as stream:
        stream.write((json.dumps(raw, indent=2) + '\n').encode())
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--collect', action='store_true', help='write an ignored candidate record without accepting it')
    args = parser.parse_args()
    report = collect()
    if not args.collect and report != read(RECORD):
        raise SystemExit('type-bridge statements, foundations, sources or artifacts differ')
    print('Type bridge checked; no original M4 obligation is closed by this result.')
