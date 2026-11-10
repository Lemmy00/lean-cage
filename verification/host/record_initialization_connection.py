#!/usr/bin/env python3
"""Preserve the checked public initialization-to-bootstrap source connection."""
# §AR-host-boundary.acceptance: Record the source slice and its pending consumers.
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
    expected = set(json.loads((OUT / 'host-module-reference-review.json').read_text())['transitive_assumptions'])
    query = SOURCE / 'GatewayInitializationConnectionQuery.v'
    logs = sorted(WORK.glob('initialization-connection-*.out'))
    assert len(logs) >= 12
    for path in logs:
        if path.name.endswith('-assumptions.out'):
            actual = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', path.read_text(), re.M)) - {'Axioms'}
            assert actual <= expected, (path.name, actual - expected)
    modules = set()
    pending = ['GatewayInitializationConnectionQuery']
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
            assert selected.exists(), selected
            inputs[str(selected.relative_to(ROOT))] = sha(selected)
    for path in [ROOT / 'linux/host_python.c', WORK / 'source-inputs.json', WORK / 'gateway-code.ndjson',
                 ROOT / 'verification/host/gateway.py']:
        inputs[str(path.relative_to(ROOT))] = sha(path)
    build_names = ['gateway-initialization-flagged-connection.log', 'gateway-initialization-connection-query.log']
    for name in build_names:
        value = (ROOT / '.tools/host' / name).read_text()
        assert value.strip().endswith(': checked') and 'Error:' not in value and 'Traceback' not in value, name
    artifacts = {}
    payloads = {
        'audit.v': query.read_bytes(),
        'audit.log': b''.join(('\n' + path.name + '\n').encode() + path.read_bytes() for path in logs),
        'build.log': b''.join(('\n' + name + '\n').encode() + (ROOT / '.tools/host' / name).read_bytes() for name in build_names),
    }
    for suffix, data in payloads.items():
        path = OUT / ('host-initialization-connection-' + suffix + '.gz')
        path.write_bytes(gzip.compress(data, mtime=0))
        artifacts[str(path.relative_to(ROOT))] = {'sha256': sha(path), 'source_sha256': hashlib.sha256(data).hexdigest()}
    record = {
        'schema': 'leancage-host-initialization-connection-review-v1', 'accepted_security_delivery': False,
        'specs': ['FS-host-boundary.caller.initialization', 'AR-host-boundary.primitives', 'REQ-proof-integrity.statement'],
        'declarations': ['GatewayInitializationConnection.gateway_actual_public_bootstrap_connection',
                         'GatewayInitializationCaller.gateway_actual_loaded_initialization_body',
                         'GatewayInitializationGuarded.gateway_actual_initialization_guarded_path',
                         'GatewayInitializationResult.gateway_actual_initialization_null_body',
                         'GatewayInitializationInterpreter.gateway_actual_initialization_interpreter',
                         'GatewayBootstrapFlagged.gateway_actual_bootstrap_flagged'],
        'result': 'A SAME actual public PyInit__host Callstate-to-nonNULL-return trace supplies both real Get/GetID0 checks, source flag0 checks and active store1, a SAME nonNULL private host_initialize invocation, and the complete real bootstrap Return0/path validation. At bootstrap return it retains every source descriptor, aggregate active/retired reference scope, and actual active1/completed0 flag cells/capacities.',
        'connection': 'The public caller prefix, standalone bootstrap run and remaining public suffix use identical event subsequences, memories, worlds and nested continuations. No entry/guard/bootstrap-success or later SDK acknowledgement premise supplies the output. The at-load region producer is used once; after the actual flag store the consumer carries derived current regions instead of reasserting every mutable global initializer.',
        'primitive_inputs': ['Individual actual interpreter-pointer/64-bit-ID query contracts and held-thread identity; query native/heap footprints.',
                             'Existing per-loader/libc/thread/reference contracts and ELF mapping/read-only/storage observations.',
                             'Protected bootstrap write authority excludes actual flag/descriptor blocks; source symbol and extent proofs produce that restriction.'],
        'failure_and_loss': 'Real zero/nonzero/error guards, blocked and source/committed-loss transitions remain. A NULL private-body return is proved to remain NULL through the actual public clear/return source, independently of a post-body memory frame. Return guarantees are partial correctness.',
        'transitive_assumptions': sorted(expected),
        'remaining': ['Complete post-bootstrap import/attribute/class/module reference and callback composition, including returned failures/retries.',
                      'Final source-derived initialized-flag producer consumed by all actual public callbacks.',
                      'Complete host-boundary parser/native/custody/result joins and final identified acceptance; M5.2 remains incomplete.'],
        'artifacts': artifacts, 'inputs': inputs,
    }
    (OUT / 'host-initialization-connection-review.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('Public initialization-to-bootstrap source connection recorded; post-bootstrap consumers remain pending.')


if __name__ == '__main__':
    main()
