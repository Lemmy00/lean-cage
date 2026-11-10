#!/usr/bin/env python3
"""Preserve the checked actual public initializer success/failure flag stores."""
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
    query = SOURCE / 'GatewayInitializationReturnsQuery.v'
    logs = sorted(WORK.glob('initialization-return-*.out'))
    assert len(logs) == 17, len(logs)
    for path in logs:
        if path.name.endswith('-assumptions.out'):
            actual = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', path.read_text(), re.M)) - {'Axioms'}
            assert actual <= expected, (path.name, actual - expected)
    modules = set()
    pending = ['GatewayInitializationReturnsQuery']
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
    build_names = ['gateway-attached-native-final.log']
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
        path = OUT / ('host-initialization-returns-' + suffix + '.gz')
        path.write_bytes(gzip.compress(data, mtime=0))
        artifacts[str(path.relative_to(ROOT))] = {
            'sha256': sha(path), 'source_sha256': hashlib.sha256(data).hexdigest()}
    record = {
        'schema': 'leancage-host-initialization-returns-review-v1', 'accepted_security_delivery': False,
        'specs': ['FS-host-boundary.caller.initialization', 'AR-host-boundary.primitives',
                  'REQ-proof-integrity.statement'],
        'declarations': ['GatewayInitializationCompletion.gateway_actual_initialization_completed',
                         'GatewayInitializationFailure.gateway_actual_initialization_failed',
                         'GatewayInitializationCompletion.gateway_initialization_owned_module_live',
                         'GatewayInitializationCells.gateway_initialization_cells_store',
                         'GatewayReturnScope.gateway_terminal_return_scope'],
        'result': 'On the SAME actual public-wrapper suffix after private initialization, a source-owned module reference and normal current regions derive pointer validity, completed1/active0 source stores, identical returned module and retained current region/reference context. A NULL private return instead derives active0 with the prior completed cell unchanged and a final NULL result under exception-capable individual runtime contracts.',
        'connection': 'The actual Returnstate continuation, source temporary assignment, pointer condition, two exact Mint32 writes and final return are checked Clight paths. Aggregate source ownership supplies the module root. Store arguments/authority/order and terminal flag loads are derived, not a successful-initialization or whole-helper frame premise.',
        'inputs_and_scope': ['Success uses the actual module source ledger entry, current concrete regions/aggregate active-retired scope and original individual thread/interpreter/profile contracts.',
                             'Failure uses current native flag-cell capacities/loads and the narrow gateway_attached_native_runtime rooted discipline. This discipline permits pending exceptions; no clear objects-ready or SDK callback-frame premise is imposed after a failed operation.',
                             'The failure result retains exactly rooted runtime state and actual flag cells. It does not invent a successful class/module graph, reference cleanup or path-retention observation.',
                             'Waiting, interference, blocked and lost prefixes remain; final-return claims are partial correctness.'],
        'statement_review': 'Reviewed complete quantified types, selected module ownership to live-pointer derivation, precise original/native store contracts and arguments, symbol separation and widths, normal versus exception-capable contexts, terminal suffix, and transitive axioms. No new axiom, sorry/admit, compiler-trust shortcut or assumed application conclusion.',
        'transitive_assumptions': sorted(expected),
        'interface_amendment': 'Native cleanup now requires only attached ambient/stack allocation/store/free representation laws; unrelated SDK error-call footprints are absent. The previous supporting source/query/record is preserved in assurance/host-initialization-native-projection-before.json.gz.',
        'consumer': 'The full public initializer must supply the actual post-private-body current module/reference/region context (or the failure flag/rooted context); its post-bootstrap source/SDK composition remains in progress.',
        'remaining': ['Actual post-bootstrap import/attribute/class/module reference and callback composition producing these suffix inputs on every returned branch.',
                      'Actual final initialized-flag/type-root consumer in every public callback and complete host boundary/result/physical custody composition.',
                      'Integrated identified M5.2 acceptance and main integration.'],
        'artifacts': artifacts, 'inputs': inputs,
    }
    (OUT / 'host-initialization-returns-review.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('Actual success/failure flag-store branches recorded; full module-body producer remains pending.')


if __name__ == '__main__':
    main()
