#!/usr/bin/env python3
"""Preserve actual initializer object setup, SDK boundaries and rejection prefixes."""
# §AR-host-boundary.acceptance: Bind actual initializer source to its reviewed caller interfaces.
from pathlib import Path
import gzip
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'verification/host'
WORK = ROOT / '.tools/host/gateway'
OUT = ROOT / 'assurance'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    baseline = json.loads((OUT / 'host-module-reference-review.json').read_text())
    expected = set(baseline['transitive_assumptions'])
    query = SOURCE / 'GatewayInitializerObjectsQuery.v'
    logs = sorted(WORK.glob('initializer-objects-*.out'))
    assert len(logs) == 89, len(logs)
    for path in logs:
        if path.name.endswith('-assumptions.out'):
            actual = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', path.read_text(), re.M)) - {'Axioms'}
            assert actual <= expected, (path.name, actual - expected)
    modules = set()
    pending = ['GatewayInitializerObjectsQuery']
    while pending:
        name = pending.pop()
        if name in modules:
            continue
        modules.add(name)
        path = SOURCE / (name + '.v')
        if not path.exists():
            path = WORK / (name + '.v')
        for group in re.findall(r'From\s+HostGateway\s+Require\s+Import\s+([A-Za-z0-9_\s]+)\.', path.read_text()):
            pending.extend(group.split())
    inputs = {}
    for name in sorted(modules):
        path = SOURCE / (name + '.v')
        if not path.exists():
            path = WORK / (name + '.v')
        for selected in [path, WORK / (name + '.vo')]:
            assert selected.is_file(), selected
            inputs[str(selected.relative_to(ROOT))] = sha(selected)
    for path in [ROOT / 'linux/host_python.c', WORK / 'source-inputs.json', WORK / 'gateway-code.ndjson',
                 SOURCE / 'gateway.py', Path(__file__).resolve()]:
        inputs[str(path.relative_to(ROOT))] = sha(path)
    for name in ['linux/host_python.c', '.tools/host/gateway/GatewaySource.v']:
        assert inputs[name] == baseline['inputs'][name], name
    build_names = ['gateway-initializer-objects-final.log']
    for name in build_names:
        text = (ROOT / '.tools/host' / name).read_text()
        assert text.strip().endswith(': checked') and 'Error:' not in text and 'Traceback' not in text, name
    artifacts = {}
    payloads = {
        'audit.v': query.read_bytes(),
        'audit.log': b''.join(('\n' + path.name + '\n').encode() + path.read_bytes() for path in logs),
        'build.log': b''.join(('\n' + name + '\n').encode() +
                              (ROOT / '.tools/host' / name).read_bytes() for name in build_names),
    }
    for suffix, data in payloads.items():
        path = OUT / ('host-initializer-objects-' + suffix + '.gz')
        path.write_bytes(gzip.compress(data, mtime=0))
        artifacts[str(path.relative_to(ROOT))] = {
            'sha256': sha(path), 'source_sha256': hashlib.sha256(data).hexdigest()}
    record = {
        'schema': 'leancage-host-initializer-objects-review-v1',
        'accepted_security_delivery': False,
        'specs': ['FS-host-boundary.caller.initialization', 'AR-host-boundary.primitives',
                  'AR-host-boundary.interfaces.gateway', 'REQ-proof-integrity.statement'],
        'declarations': re.findall(r'Check @([A-Za-z0-9_]+)', query.read_text()),
        'result': 'Actual post-bootstrap initializer source derives the import, attribute lookup, class-global stores, library release, module creation version3, Workspace publication, Cancellation publication and Outcome publication calls with exact arguments/continuations. Same-run pointer stores publish returned values without a vacant-global or writable-capacity premise. Every failed creation/publication returns NULL. Active/completed guard rejection excludes non-error pending external calls without assuming eventual return.',
        'connection': 'gateway_actual_initializer_import joins the real bootstrap Return0 suffix to its actual SDK primitive, original source pathlib bytes, same returned reference/credit and nonNULL derived from the real failure branch. The other source frontiers feed the full post-bootstrap semantic initializer. Full-program syntax inventory identifies the sole direct class writer/private caller, unexposed class-cell addresses, and the sole indirect-call owner (Outcome traverse).',
        'inputs_and_scope': [
            'Individual SDK import/attribute/module/reference-transfer laws permit cached, immortal and public aliases. They give no C-global memory frame, private-object claim or complete-initializer result.',
            'The source-only boundary/rejection proofs require actual current flag loads and an ambient-closed property. Actual guarded entry, query/SDK callback authority and final class/global/region producers remain required.',
            'The generic same-run pointer-store receipt permits NULL and nonNULL replacement, including retries; existing history adapters archive overwritten unreleased owners.',
            'The syntax inventory records direct assignments/calls and address exposure; it does not claim indirect stores or SDK callbacks are harmless. The Outcome traversal visitor remains an explicit SDK capability.',
            'Waiting, ambient interference, blocked and lost states remain; returned-value facts are partial correctness.'
        ],
        'statement_review': 'Reviewed exact full caller/source/SDK types, new-reference and AddObject/AddObjectRef count semantics, original byte/symbol bindings, actual NULL/nonzero failure barriers, finite pending-call guards, source-inventory scope and all transitive assumptions. No new axiom, unchecked compiler shortcut or assumed complete application behavior.',
        'transitive_assumptions': sorted(expected),
        'consumer': 'Complete post-bootstrap initializer/class/reference/callback composition supplies the already checked public success/failure completion and operational callback flag consumers.',
        'remaining': [
            'Full SDK callback source/global-write authority and actual source-owned reference/region composition.',
            'Final module/Outcome/getter result identity and complete transport/host custody composition.',
            'Final identified public/hostile M5.2 acceptance, then main integration.'
        ],
        'artifacts': artifacts, 'inputs': inputs,
    }
    (OUT / 'host-initializer-objects-review.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('Actual initializer object source/rejection record preserved; semantic caller composition remains active.')


if __name__ == '__main__':
    main()
