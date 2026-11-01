#!/usr/bin/env python3
"""Check frozen checkpoint receipt integrity, not theorem acceptance or completion.

This additive check never rewrites the checkpoint or replays its proof commands.
Its identities are the archived inputs at review checkpoint 80d4bbe.
"""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-controller.composition: Preserve the unaccepted parent checkpoint boundary.
# §REQ-proof-integrity.provenance: Check archived evidence without widening its claim.
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parents[2]
RECEIPT = 'assurance/m4-parent-checkpoint-validation.json'
RECEIPT_SHA256 = 'f1bfcf2eca69767c63ff75b5357531f8eb682a55e87215ab2f08142cdfe68442'
BASELINE = '2db87b46d861ffd1c10e295a985818197b8c6170'
STATUS = ('kernel-checked review candidate; independent statement review and '
          'maintained-gate integration pending')
SNAPSHOT = {
    'path': 'assurance/m4-parent-checkpoint-proof-output.json.gz',
    'sha256': 'e56d65d8d303b5ebe5bd9c33279f99a975439cbd013af359b7b3c8275258bc9c',
    'uncompressed_sha256': '35eb5418e0eae9aa6f52477a10baf246a09d19cacb7b0762a2363cdd999fba21',
}
IDENTITIES = {
    'native_source_sha256': (
        'native/leancage_m3.c',
        'fe20ad61706bb8e8463d32e5c9a1a9f3bf038ff52cc9f2ac40ba14c1a010d82c'),
    'original_obligations_sha256': (
        'assurance/m4-obligations.json',
        '77f760ca9447b8ee05ec0e24efc637b35ff6a62356657515ffc68f0999182064'),
}
# Expected hashes are independent of the receipt being checked: no refresh mode.
EXPECTED = {
    'repository': (['./scripts/check.sh'],
                   'f86903216bd241d5bce53af4c3865ac6b9c26dfd993e3312ea6ed44c48493bd5'),
    'initialization': (['python3', 'm4/initialization/check.py'],
                       '4439ae29d4f217266077f0b6d9c5231abc3010bda482f68c6ae0a4b075d42275'),
    'candidate-collection': (['python3', 'm4/parent-checkpoint/verify.py', '--collect'],
                            'e3cd72606aedd8842ea625c441a09b77be7c6c1aba8d461ba8ffaaeb82989f85'),
    'candidate-snapshot': (['python3', 'm4/parent-checkpoint/verify.py'],
                          '2fbaca0791789a96260412e03b069862c7330feac63ec02ae0821c3f547af434'),
    'format': (['./scripts/grund.sh', 'fmt', '--check'],
               'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'),
    'diff': (['git', 'diff', '--cached', '--check'],
             'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'),
}


class IntegrityError(ValueError):
    """The archived checkpoint and its recorded identities disagree."""


def read(root, relative):
    """Read a canonical repository-relative file, refusing escapes through links."""
    if (not isinstance(relative, str) or not relative or '\\' in relative or '\0' in relative
            or PurePosixPath(relative).is_absolute()
            or '..' in PurePosixPath(relative).parts
            or PurePosixPath(relative).as_posix() != relative):
        raise IntegrityError('noncanonical repository-relative path: ' + repr(relative))
    root = Path(root).resolve()
    path = (root / relative).resolve()
    if not path.is_relative_to(root):
        raise IntegrityError('evidence path escapes repository: ' + relative)
    try:
        return path.read_bytes()
    except OSError as error:
        raise IntegrityError('cannot read evidence: ' + relative) from error


def decode(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise IntegrityError('duplicate JSON key: ' + key)
            result[key] = value
        return result

    def constant(value):
        raise IntegrityError('nonfinite JSON number: ' + value)

    try:
        return json.loads(raw, object_pairs_hook=pairs, parse_constant=constant)
    except (ValueError, UnicodeError) as error:
        raise IntegrityError('invalid evidence JSON: ' + str(error)) from error


def same(actual, expected, label):
    # JSON encoding keeps False distinct from 0, and True distinct from 1.
    if json.dumps(actual, sort_keys=True) != json.dumps(expected, sort_keys=True):
        raise IntegrityError('checkpoint differs: ' + label)


def hash_matches(raw, expected, label):
    same(hashlib.sha256(raw).hexdigest(), expected, label)


def check(root=ROOT):
    receipt_bytes = read(root, RECEIPT)
    receipt = decode(receipt_bytes)
    try:
        for key, expected in {
                'schema_version': 1, 'baseline_commit': BASELINE, 'status': STATUS,
                'accepted_claims_changed': False, 'original_obligations_closed': 0,
                'full_controller_complete': False, 'full_m4_complete': False}.items():
            same(receipt[key], expected, key)
        same(receipt['baseline_ci']['scope'], 'foundation checks only', 'CI scope')
        same(receipt['baseline_ci']['conclusion'], 'success', 'recorded CI conclusion')
        same(receipt['snapshot'], SNAPSHOT, 'snapshot identities')
        packed = read(root, receipt['snapshot']['path'])
        hash_matches(packed, SNAPSHOT['sha256'], 'compressed snapshot')
        raw = gzip.decompress(packed)
        hash_matches(raw, SNAPSHOT['uncompressed_sha256'], 'plain snapshot')
        snapshot = decode(raw)
        for key, expected in {
                'schema_version': 1, 'baseline_commit': BASELINE, 'review_candidate': True,
                'integrated': False, 'full_controller_complete': False,
                'full_m4_complete': False}.items():
            same(snapshot[key], expected, 'snapshot ' + key)

        records = receipt['validation']
        if not isinstance(records, list):
            raise IntegrityError('receipt records must be a list')
        names = [record['name'] for record in records]
        if len(names) != len(set(names)) or set(names) != set(EXPECTED):
            raise IntegrityError('duplicate, missing or unexpected receipt')
        for record in records:
            name = record['name']
            command, expected_hash = EXPECTED[name]
            same(record['command'], command, name + ' command')
            same(record['exit_code'], 0, name + ' exit code')
            same(record['log'], 'assurance/m4-parent-checkpoint-' + name + '-check.log',
                 name + ' log path')
            same(record['log_sha256'], expected_hash, name + ' recorded log hash')
            hash_matches(read(root, record['log']), expected_hash, name + ' log bytes')

        for key, (path, expected_hash) in IDENTITIES.items():
            same(receipt[key], expected_hash, key)
            hash_matches(read(root, path), expected_hash, path)
            same(snapshot['source_sha256'][path], expected_hash, 'snapshot ' + path)

        counts = receipt['candidate']
        for key, actual in {
                'rocq_theorem_records': len(snapshot['rocq_declarations']),
                'lean_theorem_records': len(snapshot['lean_declarations']),
                'compiled_artifacts': len(snapshot['artifact_sha256']),
                'source_identities': len(snapshot['source_sha256'])}.items():
            same(counts[key], actual, key)
        modules = Counter(Path(path).suffix for path in snapshot['artifact_sha256'])
        same(counts['rocq_modules'], modules['.vo'], 'Rocq module count')
        same(counts['lean_modules'], modules['.olean'], 'Lean module count')
        same(counts['imported_computational_records'], 1, 'imported endpoint count')
        foundations = Counter((tuple(record['assumption_names']),
                               tuple(record['definitional_uip']))
                              for record in snapshot['rocq_declarations'])
        expected_foundations = [dict(count=count, assumption_names=list(names),
                                    definitional_uip=list(uip))
                               for (names, uip), count in foundations.items()]
        same(sorted(receipt['foundations'], key=lambda item: json.dumps(item, sort_keys=True)),
             sorted(expected_foundations, key=lambda item: json.dumps(item, sort_keys=True)),
             'recorded foundations')
        exports = {name: {'declarations': len(value['inventory']['declarations']),
                          'sha256': value['sha256']}
                   for name, value in snapshot['exports'].items()}
        same(receipt['exports'], exports, 'strict export identities')
        # Also freeze ancillary prose, timing and CI metadata; this is a historical receipt.
        hash_matches(receipt_bytes, RECEIPT_SHA256, 'complete archived receipt')
    except (KeyError, TypeError, AttributeError, OSError) as error:
        raise IntegrityError('malformed checkpoint evidence: ' + str(error)) from error
    return {'receipts': len(records), 'integrity_only': True,
            'review_candidate': True, 'full_m4_complete': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT,
                        help='repository root; supports disposable evidence copies')
    args = parser.parse_args()
    try:
        result = check(args.root)
    except IntegrityError as error:
        print('Checkpoint receipt integrity failed: ' + str(error), file=sys.stderr)
        return 1
    print(f'{result["receipts"]} frozen checkpoint receipts and snapshot identities match. '
          'Integrity only; theorem acceptance and full M4 completion remain open.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
