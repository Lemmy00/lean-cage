"""Validate the explicit navigation amendment without refreshing frozen evidence."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-parent.audit: Only enumerated document/dependency fingerprints may change.
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RECORD = ROOT / 'assurance/m4-parent-navigation.json'
BEFORE = ROOT / 'assurance/m4-parent-navigation-before.json.gz'
DOCUMENTS = {'AGENTS.md', 'README.md', 'docs/development.md', 'docs/roadmap.md',
             'docs/functional-spec/FS-assurance.md', 'docs/architecture/README.md',
             'docs/decisions/architectural/README.md'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def validate(record=None, original=None, root=ROOT):
    record = json.loads(RECORD.read_text()) if record is None else record
    original = json.loads(gzip.decompress(BEFORE.read_bytes())) if original is None else original
    if (record['schema_version'] != 1 or set(record['files']) != set(original)
            or {p for p, row in record['files'].items() if row['kind'] == 'documentation'} != DOCUMENTS):
        raise ValueError('navigation amendment inventory differs')
    files = record['files']
    for path, row in files.items():
        relative = Path(path)
        if relative.is_absolute() or '..' in relative.parts or str(relative) != path:
            raise ValueError('noncanonical amendment path')
        if row['before_sha256'] != sha(original[path].encode()) or row['after_sha256'] != sha((root / path).read_bytes()):
            raise ValueError('navigation amendment bytes differ: ' + path)
        if row['kind'] not in {'documentation', 'dependency_metadata'}:
            raise ValueError('unknown amendment kind')
        if row['kind'] == 'dependency_metadata':
            if not path.startswith('assurance/') or not path.endswith('.json') or 'checkpoint' in path:
                raise ValueError('amendment must preserve frozen candidate/checkpoint inputs')

    digest_pairs = {(row['before_sha256'], row['after_sha256']) for row in files.values()}

    def compare(before, after, key=''):
        if before == after:
            return
        if isinstance(before, dict) and isinstance(after, dict) and set(before) == set(after):
            for name in before:
                compare(before[name], after[name], name)
            return
        if isinstance(before, list) and isinstance(after, list) and len(before) == len(after):
            for old, new in zip(before, after):
                compare(old, new, key)
            return
        if isinstance(before, str) and isinstance(after, str):
            if key in files and (before, after) == (files[key]['before_sha256'], files[key]['after_sha256']):
                return
            if key in {'claims_sha256', 'manifest_sha256', 'decoder_baseline_manifest_sha256'} and (before, after) in digest_pairs:
                return
        raise ValueError('navigation amendment alters a non-fingerprint value: ' + key)

    for path, row in files.items():
        if row['kind'] == 'dependency_metadata':
            compare(json.loads(original[path]), json.loads((root / path).read_text()))
    return record


def check():
    record = validate()
    if sha(BEFORE.read_bytes()) != record['before_archive_sha256']:
        raise ValueError('navigation preimage archive differs')
    for filename, field in [
            ('m4-parent-checkpoint-proof-output.json.gz', 'frozen_candidate_snapshot_sha256'),
            ('m4-initialization-proof-output.json.gz', 'initialization_snapshot_sha256')]:
        if sha((ROOT / 'assurance' / filename).read_bytes()) != record[field]:
            raise ValueError('frozen proof snapshot differs: ' + filename)
    receipt = json.loads((ROOT / 'assurance/m4-parent-baseline-validation.json').read_text())
    log = (ROOT / 'assurance/m4-parent-baseline-check.log.gz').read_bytes()
    if (receipt['exit_code'] != 0 or type(receipt['exit_code']) is not int
            or receipt['command'] != ['./scripts/check_m4_all.sh']
            or receipt['log_sha256'] != sha(gzip.decompress(log))
            or receipt['compressed_log_sha256'] != sha(log)
            or receipt['frozen_candidate_snapshot_sha256'] != record['frozen_candidate_snapshot_sha256']
            or receipt['initialization_snapshot_sha256'] != record['initialization_snapshot_sha256']):
        raise ValueError('pre-amendment replay receipt differs')
    print(f'Navigation amendment checked: {len(DOCUMENTS)} documents; '
          f'{len(record["files"])-len(DOCUMENTS)} metadata records; frozen snapshots preserved.')
    return record


def validate_candidate_sources(expected, actual, record):
    if set(expected) != set(actual):
        raise ValueError('frozen candidate source inventory differs')
    for path in expected:
        if expected[path] == actual[path]:
            continue
        row = record['files'].get(path)
        if row is None or (expected[path], actual[path]) != (row['before_sha256'], row['after_sha256']):
            raise ValueError('unamended frozen candidate source differs: ' + path)


def replay_candidate():
    """Rebuild preserved proofs against identical artifacts and explicitly amended navigation.

    The exact pre-amendment source replay is preserved in the baseline receipt.
    The original verifier, snapshot and candidate sources are never rewritten.
    """
    record = check()
    import importlib.util
    spec = importlib.util.spec_from_file_location('amended_frozen_parent', ROOT / 'm4/parent-checkpoint/verify.py')
    candidate = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(candidate)
    expected = json.loads(gzip.decompress(candidate.SNAPSHOT.read_bytes()))
    actual = candidate.collect()
    for key in candidate.COMPARE_KEYS:
        if key == 'source_sha256':
            validate_candidate_sources(expected[key], actual[key], record)
        elif expected[key] != actual[key]:
            raise ValueError('frozen candidate statement/foundation/artifact differs: ' + key)
    print('Frozen candidate proofs, foundations, exports and compiled artifacts preserved; navigation amendments explicit.')


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay-candidate', action='store_true')
    args = parser.parse_args()
    replay_candidate() if args.replay_candidate else check()
