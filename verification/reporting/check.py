#!/usr/bin/env python3
"""Check the current reporting-source binding, reusing matching checked artifacts."""
# §AR-tooling.checks: Rebuild only missing or explicitly invalidated source consumers.
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import sys

import source

ROOT, WORK = source.ROOT, source.WORK
RECORD = ROOT / 'assurance/reporting-source.json.gz'


def verify_files(files, root=ROOT):
    for name, expected in files.items():
        if Path(name).is_absolute() or '..' in Path(name).parts:
            raise ValueError('noncanonical reporting dependency path')
        path = root / name
        if not path.is_file() or source.sha(path) != expected:
            raise ValueError('reporting source/dependency identity differs: ' + name)


def check(rebuild=False):
    record = json.loads(gzip.decompress(RECORD.read_bytes()))
    if (record['schema_version'] != 1 or record['full_m4_complete'] is not False or
            record['ordinary_lean_security_claim'] is not False or record['original_obligations_closed'] != []):
        raise ValueError('reporting-source scope differs')
    verify_files(record['inputs_sha256'])
    verify_files(record['dependency_sha256'])
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
        raise ValueError('current source prefix or temporary mapping differs')

    modules = source.consumers()
    for name, module in modules.items():
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

    spec = importlib.util.spec_from_file_location('reporting_native_extract', ROOT / 'm4/extract.py')
    extract = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(extract)
    import hashlib
    slice_hash = hashlib.sha256(extract.extract((ROOT / 'native/leancage_m3.c').read_text()).encode()).hexdigest()
    if slice_hash != record['preserved_reporting_slice_sha256']:
        raise ValueError('previously checked reporting slice changed')
    print('Current helper source consumers and preserved reporting slice checked; matching proof artifacts reused.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true', help='rebuild affected consumers against the frozen source binding')
    parser.add_argument('--current-profile', action='store_true', help='select the corrected native-source profile')
    args = parser.parse_args()
    if args.current_profile:
        record = json.loads(gzip.decompress(RECORD.read_bytes()))
        return 0 if source.sha(ROOT / 'native/leancage_m3.c') == record['inputs_sha256']['native/leancage_m3.c'] else 1
    check(args.rebuild)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        print('Reporting source check failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
