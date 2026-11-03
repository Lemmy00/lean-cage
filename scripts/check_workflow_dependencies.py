#!/usr/bin/env python3
"""Check the workflow merge's explicit documentation-only dependency amendment."""
# §AR-tooling.checks: Preserve checked proof bodies and validate only changed fingerprints.
import base64
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = '9ee41cf54a5dd21eea1742f74952ad2d369d7a16'
WORKFLOW = '02c60d1b038db64c3f370a05e0054fc2236b4cba'
DOCUMENTS = {'AGENTS.md', 'M4-CONTINUE.md', 'docs/architecture/AR-product.md',
             'docs/architecture/AR-tooling.md', 'docs/development.md', 'docs/roadmap.md'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def at_revision(revision, path):
    return subprocess.check_output(['git', 'show', revision + ':' + path], cwd=ROOT)


def check():
    record = json.loads((ROOT / 'assurance/workflow-dependency-amendment.json').read_text())
    archive = (ROOT / 'assurance/workflow-dependency-before.json.gz').read_bytes()
    if (record['schema_version'] != 1 or record['baseline_revision'] != BASE or
            record['workflow_revision'] != WORKFLOW or sha(archive) != record['before_archive_sha256']):
        raise ValueError('workflow amendment provenance differs')
    before = {name: base64.b64decode(value, validate=True)
              for name, value in json.loads(gzip.decompress(archive)).items()}
    files = record['files']
    navigation = json.loads(at_revision(BASE, 'assurance/m4-parent-navigation.json'))
    metadata = {name for name, row in navigation['files'].items() if row['kind'] == 'dependency_metadata'}
    metadata |= {'assurance/m4-parent-navigation.json', 'assurance/m4-parent-evidence.json',
                 'assurance/m4-parent-proof-output.json.gz'}
    validation_tools = {'m4/parent/amendment.py'}
    if (set(before) != set(files) or set(files) - (DOCUMENTS | metadata | validation_tools) or
            {name for name, row in files.items() if row['kind'] == 'documentation'} != DOCUMENTS):
        raise ValueError('workflow amendment inventory differs')
    for name, row in files.items():
        if (Path(name).is_absolute() or '..' in Path(name).parts or
                sha(before[name]) != row['before_sha256'] or
                sha((ROOT / name).read_bytes()) != row['after_sha256'] or
                before[name] != at_revision(BASE, name)):
            raise ValueError('workflow amendment bytes differ: ' + name)
        if name in DOCUMENTS and (ROOT / name).read_bytes() != at_revision(WORKFLOW, name):
            raise ValueError('workflow document differs from requested merge: ' + name)
        kind = 'documentation' if name in DOCUMENTS else 'validation_tooling' if name in validation_tools else 'dependency_metadata'
        if row['kind'] != kind:
            raise ValueError('workflow amendment kind differs: ' + name)

    pairs = {(row['before_sha256'], row['after_sha256']) for row in files.values()}

    def compare(old, new):
        if old == new:
            return
        if isinstance(old, dict) and isinstance(new, dict) and set(old) == set(new):
            for key in old:
                compare(old[key], new[key])
            return
        if isinstance(old, list) and isinstance(new, list) and len(old) == len(new):
            for x, y in zip(old, new):
                compare(x, y)
            return
        if isinstance(old, str) and isinstance(new, str) and (old, new) in pairs:
            return
        raise ValueError('workflow amendment changes a non-fingerprint value')

    for name in set(files) - DOCUMENTS - validation_tools:
        old, new = before[name], (ROOT / name).read_bytes()
        if name.endswith('.gz'):
            old, new = gzip.decompress(old), gzip.decompress(new)
        compare(json.loads(old), json.loads(new))
    for name in ['assurance/m4-parent-checkpoint-proof-output.json.gz',
                 'assurance/m4-initialization-proof-output.json.gz',
                 'assurance/m4-parent-navigation-before.json.gz',
                 'assurance/m4-parent-navigation-stage1.json']:
        if (ROOT / name).read_bytes() != at_revision(BASE, name):
            raise ValueError('preserved historical evidence differs: ' + name)
    print('Workflow documents and dependency fingerprints checked; proof evidence preserved.')


if __name__ == '__main__':
    check()
