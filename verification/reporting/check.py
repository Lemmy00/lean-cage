#!/usr/bin/env python3
"""Check current source consumers while preserving the original reporting receipts."""
# §AR-tooling.checks: Rebuild only missing or explicitly invalidated source consumers.
import argparse
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

import source

ROOT = source.ROOT
WORK = ROOT / '.tools/reporting/entry-rebase'
RECORD = ROOT / 'assurance/workspace-source.json.gz'
source.WORK = WORK


def evidence():
    spec = importlib.util.spec_from_file_location('workspace_source_predecessor', ROOT / 'scripts/workspace_evidence.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def preserved_lean_cache(name, expected):
    """Keep accepted decoder-input identities historical, without rebinding caches."""
    if name not in {'m3/.lake/build/lib/lean/LeanCageM3/API.olean', 'm3/.lake/build/lib/lean/Main.olean'}:
        return False
    spec = importlib.util.spec_from_file_location('workspace_compiled_predecessor', ROOT / 'scripts/rebind_product_evidence.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    files, _ = module.preserved_caches()
    return name in files and hashlib.sha256(files[name]).hexdigest() == expected


def verify_files(files, root=ROOT, *, historical_dependencies=False):
    for name, expected in files.items():
        if Path(name).is_absolute() or '..' in Path(name).parts:
            raise ValueError('noncanonical reporting dependency path')
        path = root / name
        if not path.is_file() or source.sha(path) != expected:
            if historical_dependencies and root == ROOT and preserved_lean_cache(name, expected):
                continue
            raise ValueError('reporting source/dependency identity differs: ' + name)


def source_inputs():
    paths = [ROOT / name for name in (
        'native/leancage_m3.c', 'native/m3_artifacts.h', 'native/m3_filter.h', 'native/m3_sha256.h',
        'verification/reporting/source.py', 'verification/reporting/check.py',
        'verification/reporting/test_identifiers.py', 'scripts/workspace_evidence.py',
        'assurance/workspace-baseline.json.gz', 'assurance/product-cache-baseline.json.gz',
        'scripts/rebind_product_evidence.py', 'assurance/reporting-reference-ast.v.gz',
        'lean-toolchain', 'm3/lean-toolchain', 'm3/lakefile.lean', 'm3/lake-manifest.json')]
    paths += sorted((ROOT / 'linux').glob('*.h')) + sorted((ROOT / 'linux').glob('*.c'))
    paths += [p for p in (ROOT / 'm4').rglob('*') if p.is_file() and p.suffix in {'.v', '.lean', '.py', '.json'}
              and '__pycache__' not in p.parts and 'compat' not in p.parts]
    for directory in ('LeanCage', 'lifecycle', 'workspace'):
        paths += [p for p in (ROOT / directory).rglob('*.lean') if '.lake' not in p.parts]
    paths += [module.MANIFEST for module in source.consumers().values()]
    return {str(p.relative_to(ROOT)): source.sha(p) for p in sorted(set(paths))}


def reporting_slice():
    spec = importlib.util.spec_from_file_location('workspace_source_extract', ROOT / 'm4/extract.py')
    extract = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(extract)
    previous = evidence().read_baseline()['native/leancage_m3.c'].decode()
    current = (ROOT / 'native/leancage_m3.c').read_text()
    before, after = extract.identities(previous), extract.identities(current)
    return dict(sha256=__import__('hashlib').sha256(extract.extract(current).encode()).hexdigest(),
                preserved_functions={name: digest for name, digest in before.items() if after[name] == digest},
                changed_components={name: dict(before=digest, after=after[name])
                                    for name, digest in before.items() if after[name] != digest})


def original_record():
    return json.loads(gzip.decompress(evidence().read_baseline()['assurance/reporting-source.json.gz']))


def check_scope(record):
    fields = {'schema_version', 'baseline_revision', 'predecessor', 'full_m4_complete',
              'ordinary_lean_security_claim', 'original_obligations_closed', 'delivery', 'source_boundary',
              'inputs_sha256', 'dependency_sha256', 'host_inputs_sha256', 'cache_sha256', 'namespaces',
              'temporary_renaming', 'declarations', 'reporting_slice', 'kernel_check', 'remaining_connections'}
    if set(record) != fields or record['baseline_revision'] != evidence().REVISION:
        raise ValueError('current source-consumer record schema differs')
    previous = original_record()
    if record['namespaces'] != previous['namespaces'] or record['kernel_check']['roots'] != previous['kernel_check']['roots'] or record['kernel_check']['exit_code'] != 0:
        raise ValueError('current source-consumer kernel namespace/root inventory differs')
    if (record['schema_version'] != 2 or record['full_m4_complete'] is not False or
            record['ordinary_lean_security_claim'] is not False or record['original_obligations_closed'] != []):
        raise ValueError('current source-consumer scope differs')
    if record['predecessor'] != evidence().binding():
        raise ValueError('current source-consumer predecessor differs')
    if record['inputs_sha256'] != source_inputs():
        raise ValueError('current source-consumer input inventory differs')


def check(rebuild=False):
    record = json.loads(gzip.decompress(RECORD.read_bytes()))
    check_scope(record)
    verify_files(record['dependency_sha256'], historical_dependencies=True)
    for name, expected in record['host_inputs_sha256'].items():
        if not Path(name).is_absolute() or source.sha(name) != expected:
            raise ValueError('reporting frontend/runtime input differs: ' + name)
    missing = any(not (WORK / name).is_file() for name in record['cache_sha256'])
    if rebuild or missing:
        source.rebuild(record)
    verify_files(record['cache_sha256'], WORK)
    reference = gzip.decompress((ROOT / 'assurance/reporting-reference-ast.v.gz').read_bytes()).decode()
    current = (WORK / 'main/proofs/Main.v').read_text()
    if source.renaming(reference, current) != record['temporary_renaming']:
        raise ValueError('current source prefix or identifier mapping differs')
    for name, module in source.consumers().items():
        original = json.loads(module.MANIFEST.read_text())['rocq_declarations']
        rows = record['declarations'][name]
        if [row['name'] for row in original] != [row['name'] for row in rows]:
            raise ValueError('source-consumer declaration inventory differs: ' + name)
        for old, new in zip(original, rows):
            if (source.adapt(old['full_type'], record['temporary_renaming']).split() != new['full_type'].split() or
                    old['assumption_names'] != new['assumption_names'] or
                    old['definitional_uip'] != new['definitional_uip']):
                raise ValueError('source-consumer statement or foundations differ: ' + old['name'])
        for item in module.MODULES:
            expected = source.adapt((ROOT / 'm4' / name / (item + '.v')).read_text(), record['temporary_renaming'])
            if (WORK / name / 'proofs' / (item + '.v')).read_text() != expected:
                raise ValueError('adapted proof source differs: ' + item)
    if reporting_slice() != record['reporting_slice']:
        raise ValueError('current reporting slice/component identity differs')
    print('Current workspace helper source consumers checked; preserved input/history theorem artifacts reused.')


def cache_inputs():
    paths = [WORK / 'main/proofs/Main.v', WORK / 'main/proofs/Main.vo']
    modules = source.consumers()
    for name, module in modules.items():
        paths += [WORK / name / 'proofs' / (item + suffix) for item in module.MODULES for suffix in ('.v', '.vo')]
    for item in ['NumberSlice', *modules['main'].controller.MODULES]:
        paths += [WORK / 'main/number' / (item + suffix) for suffix in ('.v', '.vo')]
    return {str(path.relative_to(WORK)): source.sha(path) for path in paths}


def collect():
    WORK.mkdir(parents=True, exist_ok=True)
    before = source_inputs()
    old = original_record()
    modules = source.consumers()
    profile = modules['main'].profile
    profile.verify_tools()
    profile.run([str(ROOT / '.tools/m4/CompCert/clightgen'), '-normalize', '-fstruct-passing', '-I', 'linux',
                 '-o', str(WORK / 'Main-preview.v'), 'native/leancage_m3.c'], cwd=ROOT, profile=False)
    reference = gzip.decompress((ROOT / 'assurance/reporting-reference-ast.v.gz').read_bytes()).decode()
    mapping = source.renaming(reference, (WORK / 'Main-preview.v').read_text())
    expected = copy.deepcopy(old)
    expected['temporary_renaming'] = mapping
    for name, module in modules.items():
        original = {row['name']: row for row in json.loads(module.MANIFEST.read_text())['rocq_declarations']}
        for row in expected['declarations'][name]:
            row['full_type'] = source.adapt(original[row['name']]['full_type'], mapping)
    verify_files(old['dependency_sha256'], historical_dependencies=True)
    source.rebuild(expected)
    if before != source_inputs():
        raise ValueError('current source replay inputs changed while checking')
    headers = re.findall(r'^#\s+\d+\s+"([^"]+)"', (ROOT / '.tools/reporting/current/leancage_m3.i').read_text(), re.M)
    host = {name: digest for name, digest in old['host_inputs_sha256'].items() if not name.startswith(str(ROOT) + '/native/')}
    for name in headers:
        if not name.startswith('<'):
            path = Path(name) if Path(name).is_absolute() else ROOT / name
            host[str(path.absolute())] = source.sha(path)
    for name, digest in host.items():
        if source.sha(name) != digest:
            raise ValueError('source frontend/runtime dependency changed: ' + name)
    record = dict(schema_version=2, baseline_revision=evidence().REVISION, predecessor=evidence().binding(),
                  full_m4_complete=False, ordinary_lean_security_claim=False, original_obligations_closed=[],
                  delivery='Preserve accepted input, argument, digest and initialization source theorems after fresh entry integration.',
                  source_boundary='Current complete-helper AST through the accepted input/history frontier; changed admission and terminal receiver bodies require their separate application proofs.',
                  inputs_sha256=before, dependency_sha256=old['dependency_sha256'], host_inputs_sha256=host,
                  cache_sha256=cache_inputs(), namespaces=old['namespaces'], temporary_renaming=mapping,
                  declarations=expected['declarations'], reporting_slice=reporting_slice(),
                  kernel_check=dict(exit_code=0, log_sha256=source.sha(WORK / 'kernel-check.log'), roots=old['kernel_check']['roots']),
                  remaining_connections=old['remaining_connections'])
    path = WORK / 'workspace-source-proposal.json'
    path.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('Current workspace source proposal written: ' + str(path))


def historical():
    files = evidence().read_baseline()
    record = json.loads(gzip.decompress(files['assurance/reporting-source.json.gz']))
    if record['schema_version'] != 1 or record['full_m4_complete'] is not False:
        raise ValueError('historical reporting source scope differs')
    verify_files(record['dependency_sha256'], historical_dependencies=True)
    verify_files(record['cache_sha256'], ROOT / '.tools/reporting/rebase')
    print('Historical reporting source inputs and matching checked artifacts verified at the preserved revision.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true', help='rebuild consumers against the reviewed current source binding')
    parser.add_argument('--collect', action='store_true', help='write an ignored proposal after actual-source proof replay')
    parser.add_argument('--historical', action='store_true', help='check the preserved prior source/caches, without a current-helper claim')
    parser.add_argument('--current-profile', action='store_true', help='select the current native-source profile')
    args = parser.parse_args()
    if args.historical:
        if args.collect or args.rebuild or args.current_profile:
            parser.error('--historical cannot select current-source work')
        historical()
    elif args.current_profile:
        if not RECORD.is_file():
            return 1
        record = json.loads(gzip.decompress(RECORD.read_bytes()))
        return 0 if source.sha(ROOT / 'native/leancage_m3.c') == record['inputs_sha256']['native/leancage_m3.c'] else 1
    elif args.collect:
        collect()
    else:
        check(args.rebuild)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        print('Workspace source check failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
