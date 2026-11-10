#!/usr/bin/env python3
"""Record checked source callers, shared native data and their actual consumers."""
# §AR-host-boundary.acceptance: Supporting evidence retains its partial scope until integration.
from pathlib import Path
import gzip
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / '.tools/host/gateway'
OUT = ROOT / 'assurance'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    expected = json.loads((OUT / 'host-module-reference-review.json').read_text())['transitive_assumptions']
    queries = sorted(WORK.glob('source-connection-*.out'))
    assert queries, 'run GatewaySourceConnectionsQuery first'
    for path in queries:
        if path.name.endswith('-assumptions.out'):
            found = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', path.read_text(), re.M)) - {'Axioms'}
            assert found <= set(expected), (path, found - set(expected))
    logs = ['gateway-dictionary-all-receipts.log', 'gateway-source-connections-query.log',
            'native-exec-rows-build.log', 'native-source-connections-audit.log']
    for name in logs:
        value = (ROOT / '.tools/host' / name).read_text()
        assert not re.search(r'(^|\n)(Error:|error:|Traceback)', value), name
        assert ': checked' in value or 'Build completed successfully' in value or 'depends on axioms:' in value, name
    ordinary = (ROOT / '.tools/host/native-source-connections-audit.log').read_text()
    declarations = re.findall(r'depends on axioms: \[([^]]*)\]', ordinary, re.S)
    assert len(declarations) == 7
    for names in declarations:
        actual = {re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in names.split(',')}
        assert actual <= {'propext', 'Classical.choice', 'Quot.sound'}, actual
    assert digest(WORK / 'native-code.ndjson') == 'f6bb9b8b88cd7e99d6438a3b8fba82a4eb6688e3d5825073f3a04f66a57f16d2'
    artifacts = {}
    payloads = {
        'audit.v': (ROOT / 'verification/host/GatewaySourceConnectionsQuery.v').read_bytes(),
        'audit.lean': (ROOT / '.tools/host/native-source-connections-audit.lean').read_bytes(),
        'audit.log': b''.join(('\n' + path.name + '\n').encode() + path.read_bytes() for path in queries),
        'ordinary.log': ordinary.encode(),
        'build.log': b''.join(('\n' + name + '\n').encode() + (ROOT / '.tools/host' / name).read_bytes() for name in logs[:-1]),
    }
    for suffix, payload in payloads.items():
        path = OUT / ('host-source-connections-' + suffix + '.gz')
        path.write_bytes(gzip.compress(payload, mtime=0))
        artifacts[str(path.relative_to(ROOT))] = {'sha256': digest(path), 'source_sha256': hashlib.sha256(payload).hexdigest()}
    modules = [
        'GatewaySourceConnectionsQuery', 'GatewayBootstrapHistory', 'GatewayInitializationHistory',
        'GatewayReferenceHistoryThreads', 'GatewayBootstrapReferenceScope', 'GatewayPendingNativeRows',
        'GatewayNativeSourceBinding', 'GatewayNativeReferences', 'GatewayNativeChannels', 'GatewayExchangeNativePrepared',
        'GatewaySendNoReceive', 'GatewaySourceBoundCalls', 'GatewaySourceIntegerReceipt',
        'GatewayReferenceDictionaryChild', 'GatewayReferenceDictionaryResume', 'GatewayDictionaryCallReceipts',
        'GatewayDictionarySecondReceipt', 'GatewayDictionaryInsertStatus', 'GatewayDictionaryInsertReceipt',
        'GatewayDictionaryReleaseReceipts',
    ]
    paths = [ROOT / 'verification/host' / (name + '.v') for name in modules]
    paths += [WORK / (name + '.vo') for name in modules]
    paths += [ROOT / 'verification/host' / (name + '.lean') for name in [
        'NativeCode', 'NativeChannelCode', 'FilesystemNativeCodeRows', 'FilesystemNativeForkRows',
        'FilesystemNativeChannelRows', 'FilesystemNativeExecRows']]
    paths += [ROOT / 'linux/host_python.c', WORK / 'GatewaySource.v', WORK / 'GatewaySource.vo',
              WORK / 'native-code.ndjson', WORK / 'GatewayNativeImport.vo', WORK / 'native-channels-extension.json']
    record = {
        'schema': 'leancage-host-source-connections-review-v1', 'accepted_security_delivery': False,
        'specs': ['FS-host-boundary.caller.initialization', 'FS-host-boundary.caller',
                  'AR-host-boundary.interfaces.gateway', 'REQ-proof-integrity.statement'],
        'status': 'supporting checked caller and primitive connections; complete M5.2 remains in progress',
        'result': [
            'The actual bootstrap and initializer bootstrap guard retain the SAME aggregate active/retired reference scope and actual descriptors.',
            'Actual entry-derived pending spawn arguments and all four live IPC leases select an already observed native spawn row without a future SDK return/reply premise.',
            'The source-built child file actions derive shared channel evidence for the SAME full actual exec table; the ordinary consumer derives its actual engine binding.',
            'The actual sender performs no receive on its data channel.',
            'Actual dictionary key, duplicate, second recursion, insertion and key/child release cuts retain SAME execution prefixes, SDK operations and continuations; nonnull progress forces positive key, Contains0 and DictSet0.',
        ],
        'shared_data': {'declarations': 127, 'preserved_native100': True,
                        'extension': '27 checked dependencies for pure channel observations; previous 100 fingerprints unchanged'},
        'assumptions': {'rocq_compcert': expected, 'ordinary_lean': ['propext', 'Classical.choice', 'Quot.sound'],
                        'primitive_contracts': 'Full inputs printed with the theorem types; individual Linux/SDK effects and actual memory/heap representations, never an enclosing helper safe-frame premise.'},
        'loss': 'Original waiting, interference, source loss and committed-loss transitions remain. Return claims are partial correctness; pending native claims require no later SDK acknowledgement.',
        'remaining': [
            'Complete guarded initialization and active/global/retired reference accounting through public class/module consumers.',
            'Recursive parser fold, public result provenance, complete EOF/reaping and same actual engine response queue.',
            'Whole physical custody and exact source-bound birth/exec/handoff composition, final identified bundle acceptance and main integration.',
        ],
        'artifacts': artifacts, 'inputs': {str(path.relative_to(ROOT)): digest(path) for path in paths},
    }
    (OUT / 'host-source-connections-review.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('Checked source connections recorded; integrated host delivery remains in progress.')


if __name__ == '__main__':
    main()
