#!/usr/bin/env python3
"""Check foundation input fingerprints without rebuilding or changing evidence."""
# §AR-tooling.checks: Cached reporting checks must preserve foundation input consistency.
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


def audits():
    for name in ('audit_axioms', 'audit_m2', 'audit_m3'):
        spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        yield module


def check_sources(audit):
    expected = json.loads(audit.MANIFEST.read_text())['source_sha256']
    actual = audit.required_sources()
    changed = sorted(name for name in expected.keys() | actual.keys()
                     if expected.get(name) != actual.get(name))
    if changed:
        raise ValueError(f'{audit.MANIFEST.name}: source/dependency identities differ:\n  '
                         + '\n  '.join(changed))


def main():
    errors = []
    for audit in audits():
        try:
            check_sources(audit)
        except (ValueError, KeyError, OSError) as error:
            errors.append(str(error))
    if errors:
        raise ValueError('\n'.join(errors))
    print('Foundation input inventories match the reviewed manifests; no proofs rebuilt.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        print('Foundation input check failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
