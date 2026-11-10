#!/usr/bin/env python3
"""Inspect exact source-provenance and retention declarations on a checked source graph."""
# §REQ-proof-integrity.statement: Record full types and assumptions without promoting a delivery.
import argparse
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
WORK = ROOT / '.tools/host/source-epoch'
REVIEW = ROOT / 'assurance/host-private-address-source-review.json'
MODULES = ['GatewayPointerOrigins', 'GatewayPointerMemory', 'GatewayPointerExpressions',
           'GatewayGlobalAddresses', 'GatewayPointerEntry', 'GatewayPointerControl',
           'GatewayPointerLabels', 'GatewayPointerExecution', 'GatewayInitializerOwnedStores',
           'GatewayObservationSourceRepair', 'GatewayOutcomeSourceRepair']
INTERFACES = ['gateway_pointer_avoids', 'gateway_memval_avoids', 'gateway_memory_avoids', 'gateway_expression_addresses',
              'gateway_lvalue_addresses', 'gateway_private_cell_name', 'gateway_private_cell',
              'gateway_assignment_address_inputs', 'gateway_statement_addresses',
              'gateway_pointer_statement', 'gateway_pointer_cont', 'gateway_pointer_source',
              'gateway_initializer_owning_store', 'gateway_source_addresses',
              'gateway_pointer_definition', 'gateway_pointer_definition_entry',
              'gateway_observation_repaired_identifier', 'gateway_observation_retained_definition',
              'gateway_outcome_repaired_identifier', 'gateway_outcome_retained_definition',
              'gateway_outcome_variable_definition']
ALLOWED = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
           'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep',
           'Events.external_functions_sem', 'Events.inline_assembly_sem'}


def load():
    spec = importlib.util.spec_from_file_location('host_epoch_gateway', HERE / 'gateway.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


GATEWAY = load()


def record(replay):
    replay = replay.resolve()
    completed = json.loads(replay.read_text())
    input_path = replay.parent / 'inputs.json'
    inputs = json.loads(input_path.read_text())
    if (completed['status'] != 'passed' or completed['excluded'] or completed['failed']
            or completed['blocked'] or completed['input_drift']
            or GATEWAY.sha(input_path) != completed['inputs_sha256']):
        raise ValueError('A complete matching source replay is required')
    GATEWAY.PROFILE.verify_tools()
    sources = {}
    pending = list(MODULES)
    while pending:
        name = pending.pop()
        if name in sources:
            continue
        row = completed['completed'][name]
        source = ROOT / inputs['sources'][name]
        if (GATEWAY.sha(source) != row['source']
                or GATEWAY.sha(GATEWAY.WORK / (name + '.vo')) != row['object']):
            raise ValueError('Source/object replay binding differs: ' + name)
        sources[name] = row
        pending.extend(inputs['dependencies'][name])
    declarations = []
    for module in MODULES:
        text = (HERE / (module + '.v')).read_text()
        names = re.findall(r'^(?:Theorem|Lemma|Definition|Fixpoint|Record|Inductive|with)\s+'
                           r'((?:gateway_|actual_)[A-Za-z0-9_]+)', text, re.M)
        declarations.extend((module, name) for name in names)
    WORK.mkdir(parents=True, exist_ok=True)
    lines = ['From HostGateway Require Import ' + ' '.join(MODULES) + '.',
             'Set Printing Depth 100000.', 'Set Printing Width 120.']
    for index, (module, name) in enumerate(declarations):
        full = module + '.' + name
        lines += [f'Redirect "source-epoch-{index:03}-type" Check @{full}.',
                  f'Redirect "source-epoch-{index:03}-axioms" Print Assumptions {full}.']
    for index, name in enumerate(INTERFACES):
        lines.append(f'Redirect "source-epoch-interface-{index:02}" Print {name}.')
    query = GATEWAY.WORK / 'GatewaySourceEpochQuery.v'
    query.write_text('\n'.join(lines) + '\n')
    compiled = GATEWAY.PROFILE.run(['rocq', 'c', '-q', *GATEWAY.flags(), str(query)],
                                   cwd=GATEWAY.WORK, timeout=120)
    (WORK / 'query.log').write_text(compiled.stdout)
    rows = []
    for index, (module, name) in enumerate(declarations):
        assumptions = (GATEWAY.WORK / f'source-epoch-{index:03}-axioms.out').read_text()
        axioms, uip = GATEWAY.CONNECTION.foundations(assumptions)
        if set(axioms) - ALLOWED or set(uip) - {'Lean.eq'}:
            raise ValueError('Unexpected foundation: ' + module + '.' + name)
        rows.append(dict(module=module, name=name,
                         type=(GATEWAY.WORK / f'source-epoch-{index:03}-type.out').read_text(),
                         assumptions=assumptions, axioms=axioms, definitional_uip=uip))
    command = ['rocq', 'check', '-silent', *GATEWAY.flags(checker=True), 'HostGateway.GatewaySourceEpochQuery']
    checked = GATEWAY.PROFILE.run(command, cwd=GATEWAY.WORK, timeout=120)
    (WORK / 'kernel.log').write_text(checked.stdout)
    for name, row in sources.items():
        if (GATEWAY.sha(ROOT / inputs['sources'][name]) != row['source']
                or GATEWAY.sha(GATEWAY.WORK / (name + '.vo')) != row['object']):
            raise ValueError('Source/object drift during query: ' + name)
    return dict(schema='leancage-host-source-provenance-review-v1', accepted_security_delivery=False,
                declarations=rows, interfaces={name: (GATEWAY.WORK / f'source-epoch-interface-{index:02}.out').read_text()
                                               for index, name in enumerate(INTERFACES)},
                replay=dict(path=str(replay.relative_to(ROOT)), sha256=GATEWAY.sha(replay),
                            inputs_sha256=GATEWAY.sha(input_path)),
                source_objects=sources, kernel_check=dict(command=command, exit_code=0,
                                                           stdout_sha256=GATEWAY.sha(WORK / 'kernel.log')),
                current_c_sha256=GATEWAY.sha(ROOT / 'linux/host_python.c'),
                current_clight_sha256=GATEWAY.sha(GATEWAY.WORK / 'GatewaySource.v'),
                tool_sha256=GATEWAY.sha(Path(__file__)),
                result='Actual Clight expression, assignment, entry and internal control steps preserve private-cell address provenance from explicit input origins; exact source inventories identify the private cells and exposed addresses. Actual owning stores conserve current plus retired credits. Both source repairs retain their precisely identified unaffected definitions.',
                remaining=['Actual loaded/native/managed input producers and expanded SDK callback history must produce the initial and per-call pointer scopes.',
                           'Linked runtime visitor capabilities require the actual source-aligned environment and typed indirect-call adapter; the canonical unit environment is not a full CPython image.',
                           'Active/completed source guards and exact callback entries must derive global-write exclusion and the full initializer context.',
                           'The complete host public caller, transport and filesystem guarantee remains assigned; this is supporting source evidence.'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', type=Path, required=True)
    parser.add_argument('--propose', action='store_true')
    args = parser.parse_args()
    result = record(args.replay)
    (WORK / 'proposal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    if not args.propose and result != json.loads(REVIEW.read_text()):
        raise ValueError('Source statements/bindings differ; review the proposal without refreshing expectations')
    print('Complete source statements/interfaces/axioms and independent kernel check passed; delivery remains open.')


if __name__ == '__main__':
    main()
