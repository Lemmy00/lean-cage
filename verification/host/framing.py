#!/usr/bin/env python3
"""Check typed response-prefix identity and its actual native parser-result consumer."""
# §DA-host-engine.framing: Preserve the strict shared-data boundary and full checked statements.
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
WORK = ROOT / '.tools/host/framing'
RECORD = ROOT / 'assurance/host-framing-review.json'
EPOCH = ROOT / 'assurance/host-framing-source-epoch.json'
EPOCH_FIELDS = {'source_bindings', 'compiled_objects', 'kernel_check', 'reused_evidence'}
MODULES = ['GatewayCanonicalBytes', 'GatewayCanonicalSubject', 'GatewayPrefixReader',
           'GatewaySourceFraming', 'GatewayResponseFraming', 'GatewayDecodedFraming']
DECLARATIONS = [
    'gateway_plain_word_encoding', 'gateway_plain_tag_encoding',
    'gateway_heap_value_canonical', 'gateway_heap_array_canonical', 'gateway_heap_dictionary_canonical',
    'gateway_prefix_word_actual', 'gateway_prefix_step_refines', 'gateway_prefix_read_monotone',
    'gateway_source_encoding_readable', 'gateway_source_prefix_strict', 'gateway_source_prefix_unique',
    'gateway_source_response_readable', 'gateway_response_prefix_strict', 'gateway_response_prefix_unique',
    'gateway_response_complete_prefix', 'gateway_decoded_response_prefix',
    'gateway_source_value_complete_prefix', 'gateway_reference_decoded_writer',
]
INTERFACES = ['gateway_canonical_subject', 'gateway_prefix_mode', 'gateway_subject_mode',
              'gateway_prefix_word', 'gateway_prefix_scalar', 'gateway_prefix_step', 'gateway_prefix_read',
              'gateway_prefix_refines', 'gateway_prefix_readable', 'gateway_response_prefix_read',
              'gateway_response_readable']


def load(name, path):
    specification = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


GATEWAY = load('host_framing_gateway', 'verification/host/gateway.py')
AUDIT = load('host_framing_audit', 'scripts/audit_host.py')


def dependencies():
    found, pending = {}, list(MODULES)
    while pending:
        name = pending.pop()
        if name in found:
            continue
        source = HERE / (name + '.v')
        if not source.is_file():
            source = GATEWAY.WORK / (name + '.v')
        found[name] = source
        for group in re.findall(r'From\s+HostGateway\s+Require\s+Import\s+([A-Za-z0-9_\s]+)\.', source.read_text()):
            pending.extend(group.split())
    return found


def verify_reused_objects(sources):
    baseline = json.loads(gzip.decompress((ROOT / 'assurance/host-checkpoint-rocq-record.json.gz').read_bytes()))
    amendment = json.loads((ROOT / 'assurance/host-outcome-copy-amendment.json').read_text())
    replay = ROOT / amendment['replay']['snapshot']['path']
    if GATEWAY.sha(replay) != amendment['replay']['snapshot']['sha256']:
        raise ValueError('Private-copy replay archive differs')
    copied = json.loads(gzip.decompress(replay.read_bytes()))
    known = {name: (row['source_sha256'], row['object_sha256']) for name, row in baseline['completed'].items()}
    known.update({name: (row['source'], row['object']) for name, row in copied['checked'].items()})
    evidence = [ROOT / 'assurance/host-checkpoint-rocq-record.json.gz',
                ROOT / 'assurance/host-outcome-copy-amendment.json', replay,
                ROOT / 'assurance/host-source-comment-amendment.json']
    epoch_path = ROOT / 'assurance/host-channel-invocations-review.json'
    if epoch_path.is_file():
        epoch = json.loads(epoch_path.read_text())
        source_path = ROOT / 'assurance/host-observation-source-amendment.json'
        source = json.loads(source_path.read_text())
        if (epoch['schema'] != 'leancage-host-channel-invocations-component-v1'
                or epoch['complete_delivery'] is not False or source['accepted_security_delivery'] is not False):
            raise ValueError('Unreviewed source epoch or attempted delivery promotion')
        if epoch['source_epoch']['clight_sha256'] != source['after_clight_sha256']:
            raise ValueError('Observation/source replay epoch differs')
        proof = source['source_retention_proof']
        if GATEWAY.sha(ROOT / proof['path']) != proof['sha256']:
            raise ValueError('Source retention proof differs')

        def archived(role):
            entry = epoch['evidence'][role]
            path = ROOT / entry['path']
            raw = path.read_bytes()
            data = gzip.decompress(raw)
            import hashlib
            if (hashlib.sha256(raw).hexdigest() != entry['sha256']
                    or hashlib.sha256(data).hexdigest() != entry['uncompressed_sha256']):
                raise ValueError('Source replay archive differs: ' + role)
            evidence.append(path)
            return data

        current = json.loads(archived('canonical-replay'))
        inputs = archived('canonical-inputs')
        import hashlib
        if (current['status'] != 'passed' or current['failed'] or current['blocked'] or current['input_drift']
                or current['inputs_sha256'] != hashlib.sha256(inputs).hexdigest()):
            raise ValueError('Incomplete source replay')
        known.update({name: (row['source'], row['object']) for name, row in current['completed'].items()})
        evidence.extend([epoch_path, source_path, ROOT / proof['path']])
        outcome_path = ROOT / 'assurance/host-outcome-source-amendment.json'
        if outcome_path.is_file():
            outcome = json.loads(outcome_path.read_text())
            if (outcome['schema'] != 'leancage-host-outcome-source-amendment-v1'
                    or outcome['accepted_security_delivery'] is not False
                    or outcome['before_c_sha256'] != source['after_c_sha256']
                    or outcome['before_clight_sha256'] != source['after_clight_sha256']):
                raise ValueError('Outcome source amendment predecessor differs')
            for name, expected in outcome['artifacts'].items():
                if GATEWAY.sha(ROOT / name) != expected:
                    raise ValueError('Outcome source amendment artifact differs: ' + name)
                evidence.append(ROOT / name)
            retained = outcome['source_retention_proof']
            if GATEWAY.sha(ROOT / retained['path']) != retained['sha256']:
                raise ValueError('Outcome source retention proof differs')
            final = json.loads(gzip.decompress((ROOT / outcome['replay']['record']).read_bytes()))
            final_inputs = gzip.decompress((ROOT / outcome['replay']['inputs']).read_bytes())
            if (final['status'] != 'passed' or final['failed'] or final['blocked'] or final['input_drift']
                    or final['excluded'] or final['inputs_sha256'] != hashlib.sha256(final_inputs).hexdigest()):
                raise ValueError('Incomplete Outcome source replay')
            known.update({name: (row['source'], row['object']) for name, row in final['completed'].items()})
            evidence.extend([outcome_path, ROOT / retained['path']])
            source = outcome
        if (GATEWAY.sha(ROOT / 'linux/host_python.c') != source['after_c_sha256']
                or GATEWAY.sha(GATEWAY.WORK / 'GatewaySource.v') != source['after_clight_sha256']):
            raise ValueError('Current C/Clight differs from the reviewed source amendment chain')
    for name, source in sources.items():
        if name in MODULES:
            continue
        actual = (GATEWAY.sha(source), GATEWAY.sha(GATEWAY.WORK / (name + '.vo')))
        if known.get(name) != actual:
            raise ValueError('No matching compiled dependency evidence: ' + name)
    return {str(path.relative_to(ROOT)): GATEWAY.sha(path) for path in evidence}


def verify_review(result):
    reviewed = json.loads(RECORD.read_text())
    if result == reviewed:
        return
    stable = {key: value for key, value in result.items() if key not in EPOCH_FIELDS}
    original = {key: value for key, value in reviewed.items() if key not in EPOCH_FIELDS}
    if stable != original:
        raise ValueError('Framing statements, bodies, interfaces or assumptions differ from review')
    epoch = json.loads(EPOCH.read_text())
    if (epoch['schema'] != 'leancage-host-framing-source-epoch-v1'
            or epoch['accepted_security_delivery'] is not False
            or epoch['previous_review_sha256'] != GATEWAY.sha(RECORD)
            or epoch['current'] != {key: result[key] for key in EPOCH_FIELDS}):
        raise ValueError('Framing source epoch differs from its explicit amendment')


def input_bindings(sources):
    selected = set(sources.values())
    selected.update(AUDIT.modules(['GatewayFraming']).values())
    selected.update(ROOT / name for name in [
        'verification/host/framing.py', 'verification/host/gateway.py', 'scripts/host_axiom_query.lean',
        'host/lake-manifest.json', 'host/lean-toolchain', 'm4/bridge/profile.py',
        'm4/bridge/toolchain-lock.json', 'm4/bridge/strict-importer.patch',
        '.tools/host/gateway/gateway-code.ndjson', '.tools/host/gateway/GatewaySource.v'])
    return {str(path.relative_to(ROOT)): GATEWAY.sha(path) for path in sorted(selected)}


def check():
    WORK.mkdir(parents=True, exist_ok=True)
    sources = dependencies()
    before = input_bindings(sources)
    reused = verify_reused_objects(sources)
    build = subprocess.run(['lake', 'build', 'GatewayFraming'], cwd=ROOT / 'host', capture_output=True, text=True)
    (WORK / 'ordinary-build.log').write_text(build.stdout + build.stderr)
    build.check_returncode()
    for name in MODULES:
        GATEWAY.compile_file(name)
    helper = (ROOT / 'scripts/host_axiom_query.lean').read_text().removeprefix('import Lean\n')
    ordinary = 'import Lean\nimport GatewayFraming\nset_option maxRecDepth 1000000\n' + helper
    ordinary += '\n#host_audit_module GatewayFraming\n'
    (WORK / 'OrdinaryQuery.lean').write_text(ordinary)
    checked = subprocess.run(['lake', 'env', 'lean', str(WORK / 'OrdinaryQuery.lean')],
                             cwd=ROOT / 'host', capture_output=True, text=True, timeout=120)
    (WORK / 'ordinary-query.log').write_text(checked.stdout + checked.stderr)
    checked.check_returncode()
    rows = [json.loads(line.split('HOST_AUDIT ', 1)[1]) for line in checked.stdout.splitlines() if 'HOST_AUDIT ' in line]
    ordinary_types = {row['name']: row for row in rows if row.get('theorem')}
    inventories = [row for row in rows if row.get('module') == 'GatewayFraming']
    if len(inventories) != 1 or set(inventories[0]['declarations']) != set(ordinary_types):
        raise ValueError('Incomplete ordinary theorem inventory')
    for name, row in ordinary_types.items():
        if set(row['axioms']) - AUDIT.LOGICAL or row['kernel_body'] is None:
            raise ValueError('Unexpected ordinary foundation or missing proof: ' + name)
    lines = ['(* §REQ-proof-integrity.statement: Inspect the exact source-framing types and assumptions. *)',
             'From HostGateway Require Import ' + ' '.join(MODULES) + '.',
             'Set Printing Depth 100000.', 'Set Printing Width 120.']
    for index, name in enumerate(DECLARATIONS):
        lines += [f'Redirect "framing-{index:02}-type" Check @{name}.',
                  f'Redirect "framing-{index:02}-assumptions" Print Assumptions {name}.']
    for index, name in enumerate(INTERFACES):
        lines += [f'Redirect "framing-interface-{index:02}" Print {name}.']
    query = GATEWAY.WORK / 'GatewayFramingQuery.v'
    query.write_text('\n'.join(lines) + '\n')
    result = GATEWAY.PROFILE.run(['rocq', 'c', '-q', *GATEWAY.flags(), str(query)], cwd=GATEWAY.WORK, timeout=120)
    (WORK / 'native-query.log').write_text(result.stdout)
    declarations = []
    allowed = set(json.loads((ROOT / 'assurance/host-outcome-copy-amendment.json').read_text())['queries']['axioms'])
    for index, name in enumerate(DECLARATIONS):
        assumptions = (GATEWAY.WORK / f'framing-{index:02}-assumptions.out').read_text()
        axioms, uip = GATEWAY.CONNECTION.foundations(assumptions)
        if set(axioms) - allowed:
            raise ValueError('Unexpected native foundation: ' + name + ': ' + repr(set(axioms) - allowed))
        declarations.append(dict(name=name, type=(GATEWAY.WORK / f'framing-{index:02}-type.out').read_text(),
                                 assumptions=assumptions, axioms=axioms, definitional_uip=uip))
    kernel = GATEWAY.PROFILE.run(['rocq', 'check', '-silent', *GATEWAY.flags(checker=True),
                                  'HostGateway.GatewayFramingQuery'], cwd=GATEWAY.WORK, timeout=120)
    (WORK / 'kernel-check.log').write_text(kernel.stdout)
    if before != input_bindings(sources) or reused != verify_reused_objects(sources):
        raise ValueError('Framing inputs changed during checking')
    return dict(schema='leancage-host-typed-framing-review-v1', accepted_security_delivery=False,
                specs=['FS-host-boundary.caller', 'AR-host-boundary.interfaces.gateway', 'DA-host-engine.framing'],
                ordinary=ordinary_types, declarations=declarations, reused_evidence=reused,
                native_interfaces={name: (GATEWAY.WORK / f'framing-interface-{index:02}.out').read_text()
                                   for index, name in enumerate(INTERFACES)},
                kernel_check=dict(exit_code=0, command=['rocq', 'check', '-silent', *GATEWAY.flags(checker=True),
                                                       'HostGateway.GatewayFramingQuery'],
                                  stdout_sha256=GATEWAY.sha(WORK / 'kernel-check.log')),
                source_bindings=before,
                compiled_objects={name: GATEWAY.sha(GATEWAY.WORK / (name + '.vo')) for name in sources},
                consumer='GatewayDecodedFraming.gateway_reference_decoded_writer consumes the actual call72 parse result and retains its original source owner, graph snapshot and descriptor, indexed by the same writer value.',
                result='A complete typed response/value prefix identifies the exact status/value and leaves no pending suffix. The real writer and parser heap supply their canonical tags; no future write acknowledgement or engine return is required.',
                remaining=['The actual physical channel/history must produce the common writer/caller byte prefix.',
                           'Full initialization, public Outcome, filesystem custody and integrated host acceptance remain assigned.'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--propose', action='store_true')
    arguments = parser.parse_args()
    result = check()
    proposal = WORK / 'proposal.json'
    proposal.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    if not arguments.propose:
        verify_review(result)
    print('Typed source framing and actual parser-result consumer checked; integrated M5.2 remains incomplete.')


if __name__ == '__main__':
    main()
