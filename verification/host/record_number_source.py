#!/usr/bin/env python3
"""Preserve the checked same-call numeric lexer and first constructor boundary."""
# §AR-host-boundary.acceptance: Bind numeric source proofs and their pending semantic consumer.
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
    query = SOURCE / 'GatewayJsonNumberSourceQuery.v'
    logs = sorted(WORK.glob('number-source-*.out'))
    assert len(logs) == 31, len(logs)
    for path in logs:
        if path.name.endswith('-assumptions.out'):
            actual = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', path.read_text(), re.M)) - {'Axioms'}
            assert actual <= expected, (path.name, actual - expected)
    modules = set()
    pending = ['GatewayJsonNumberSourceQuery']
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
    build_names = ['gateway-json-number-source-lexical.log', 'gateway-json-number-source-calls.log',
                   'gateway-json-number-source-connection.log', 'gateway-json-number-source-query.log']
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
        path = OUT / ('host-number-source-' + suffix + '.gz')
        path.write_bytes(gzip.compress(data, mtime=0))
        artifacts[str(path.relative_to(ROOT))] = {
            'sha256': sha(path), 'source_sha256': hashlib.sha256(data).hexdigest()}
    record = {
        'schema': 'leancage-host-number-source-review-v1', 'accepted_security_delivery': False,
        'specs': ['FS-host-boundary.caller', 'AR-host-boundary.interfaces.gateway',
                  'REQ-proof-integrity.statement'],
        'declarations': ['GatewayJsonNumberSourceConnection.gateway_actual_json_number_constructor',
                         'GatewayJsonNumberSourceLexical.gateway_actual_json_number_lexical_source',
                         'GatewayJsonNumberCallEntry.gateway_actual_json_number_call_entry',
                         'GatewayJsonNumberSourceCalls.gateway_json_number_long_call',
                         'GatewayJsonNumberSourceCalls.gateway_json_number_decode_call',
                         'GatewayJsonNumberLexical.json_number_lexical_sound'],
        'result': 'A SAME actual host_json_number Callstate-to-nonNULL-return trace derives actual bound pointer/64-bit count, complete valid JSON number grammar for those retained bytes, exact sign/digit/integer-end/index temporaries and the first real Long0 or UTF8 constructor with identical ABI arguments, actual API definition, continuation and remaining suffix.',
        'connection': 'The whole source sign, zero/nonzero guard, increment-before-test integer loop, fraction loop, exponent/sign loop and final full-consumption guard produce the lexical decision. Syntax/leading-byte failures, missing fraction/exponent digits and trailing bytes reach the actual invalid-label NULL return. No lexer correctness, constructor-success or complete-helper success premise supplies these source decisions.',
        'inputs_and_scope': ['An ambient-closed caller property provides the actual retained per-byte loads and the 65536-byte input bound; the scalar/private-storage producer must instantiate it.',
                             'This slice calls no external primitive before its first constructor. Source/internal, ambient, blocked and lost cases retain their original semantics.',
                             'The first-constructor cut requires an actual nonNULL final return and proves partial correctness, not eventual return or SDK progress.'],
        'statement_review': 'Reviewed full theorem types, individual source/ABI/path adapters, exact SAME execution/event/world/memory binding, arbitrary bytes including high signed characters, 64-bit bounds, zero/sign/leading-zero/fraction/exponent/trailing rejection, and transitive axioms. No new axiom, native_decide, sorry/admit or application-safe conclusion is assumed.',
        'transitive_assumptions': sorted(expected),
        'consumer': 'The recursive host response parser joins this actual first-constructor cut to its per-operation numeric construction/reference semantics; that final consumer remains in progress.',
        'remaining': ['Complete bounded integer chunk/negative construction and aggregate reference/storage semantics.',
                      'Whole recursive parser, exact transport/EOF/reap/public Outcome/getter provenance and physical host custody composition.',
                      'Final integrated identified M5.2 acceptance and main integration.'],
        'artifacts': artifacts, 'inputs': inputs,
    }
    (OUT / 'host-number-source-review.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('Actual numeric source/first-constructor connection recorded; final parser consumer remains pending.')


if __name__ == '__main__':
    main()
