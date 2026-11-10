#!/usr/bin/env python3
"""Preserve the checked actual public callback initialization guard."""
# §AR-host-boundary.acceptance: Record the actual source and caller inputs.
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
    query = SOURCE / 'GatewayPublicInitializationQuery.v'
    logs = sorted(WORK.glob('public-initialization-*.out'))
    assert len(logs) == 19, len(logs)
    for path in logs:
        if path.name.endswith('-assumptions.out'):
            actual = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', path.read_text(), re.M)) - {'Axioms'}
            assert actual <= expected, (path.name, actual - expected)
    modules = set()
    pending = ['GatewayPublicInitializationQuery']
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
    build_names = ['gateway-attached-native-final.log', 'gateway-public-initialization-source-final.log']
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
        path = OUT / ('host-public-initialization-' + suffix + '.gz')
        path.write_bytes(gzip.compress(data, mtime=0))
        artifacts[str(path.relative_to(ROOT))] = {
            'sha256': sha(path), 'source_sha256': hashlib.sha256(data).hexdigest()}
    record = {
        'schema': 'leancage-host-public-initialization-review-v1', 'accepted_security_delivery': False,
        'specs': ['FS-host-boundary.caller.initialization', 'AR-host-boundary.primitives',
                  'REQ-proof-integrity.statement'],
        'declarations': ['GatewayPublicInitializationCaller.gateway_actual_uninitialized_callback',
                         'GatewayPublicInitializationBoundary.gateway_uninitialized_callback_excludes_operation',
                         'GatewayPublicInitializationGuard.gateway_public_guard_source_prefix',
                         'GatewayPublicInitializationGuard.actual_public_guard_global_scope',
                         'GatewayPublicInitializationContexts.gateway_initialization_context_public_cells',
                         'GatewayInitializationAllocation.gateway_initialization_rooted_entry'],
        'result': 'A SAME actual exchange/path/workspace-constructor/CLI internal Callstate, with current completed0 cells, cannot reach an external operational callee other than PyErr_SetString. Actual entry allocation preserves these cells; source allocation derives global-name nonshadowing. Both actual completed0 and completed1 source guard paths retain the exact loaded word and original body/denial continuation.',
        'connection': 'The direct caller theorem extracts actual function entry before the selected external operation without assuming any later method return, ACK, engine birth or eventual success. The final normal initializer context supplies the exact flag-cell interface through a normal-to-attached representation inclusion.',
        'inputs_and_scope': ['Current native completed-flag capacities and actual Mint32 loads have named producers in the initializer success/failure source branches.',
                             'The attached runtime contract contains only ambient and native stack allocate/store/free representation laws. It imposes no SDK whole-call callback or application C-global preservation conclusion.',
                             'The same method source may post its actual error, block, lose or return. A separate nested invocation must have its own actual source/call identity; this theorem does not attribute other invocations or arbitrary host-global effects to this one.',
                             'Full module/class/argument caller composition must produce these entry contexts; source function bodies are unchanged.'],
        'statement_review': 'Reviewed full types, exact four maintained function bodies, actual stack/global-scope derivation, 32-bit flag word and branch arguments, arbitrary-prefix external-call exclusion, error-posting whitelist and transitive axioms. No future completion, initialized helper or whole SDK frame is an input.',
        'transitive_assumptions': sorted(expected),
        'consumer': 'Actual public callback admission and exposed early classes consume the source completed flag. Full initializer post-bootstrap module/reference/callback production and final host composition remain in progress.',
        'remaining': ['Complete post-bootstrap class/module/reference/callback producers and actual initialized public results.',
                      'Whole parser/transport/EOF/reap/native custody application joins and useful combined runtime interpretation.',
                      'Integrated identified M5.2 acceptance and main integration.'],
        'artifacts': artifacts, 'inputs': inputs,
    }
    (OUT / 'host-public-initialization-review.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('Actual public initialization guard consumers recorded; full application composition remains pending.')


if __name__ == '__main__':
    main()
