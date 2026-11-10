#!/usr/bin/env python3
"""Review the maintained result-validation source and its exact primitive interfaces."""
# §REQ-proof-integrity.statement: Supporting source checks do not complete the host guarantee.
import argparse
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
WORK = ROOT / '.tools/host/validation-source'
REVIEW = ROOT / 'assurance/host-validation-source-review.json'
MODULES = [
    'GatewayOutcomeValidationSource', 'GatewayOutcomeValidationPaths',
    'GatewayOutcomeValidationProgress', 'GatewayOutcomeValidationMetadata',
    'GatewayOutcomeFilesSource', 'GatewayOutcomeFilesIteration',
    'GatewayOutcomeValidationContext', 'GatewayDictionaryIteration',
    'GatewayBuiltinValidation', 'GatewayTypeLiteralSource', 'GatewayTypeOptionalSource',
    'GatewayValidationEntry', 'GatewayValidationTypeChecks', 'GatewayValidationNames',
    'GatewayValidationSlots', 'GatewayValidationFailureJoin',
]
INTERFACES = [
    'gateway_outcome_validation_context', 'gateway_dictionary_next_outputs',
    'gateway_dictionary_iteration_runtime', 'gateway_validation_check_post',
    'gateway_validation_slot_region', 'gateway_validation_slot_snapshot',
    'gateway_validation_source_region', 'gateway_validation_lookup_cont',
    'gateway_validation_next_cont', 'gateway_validation_name_cont', 'gateway_validation_bytes_cont',
]


def record(replay):
    spec = importlib.util.spec_from_file_location('host_validation_epoch', HERE / 'source_epoch.py')
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    engine.MODULES, engine.INTERFACES, engine.WORK = MODULES, INTERFACES, WORK
    result = engine.record(replay)
    result.update(schema='leancage-host-validation-source-review-v1',
                  audit_engine_sha256=result['tool_sha256'],
                  tool_sha256=engine.GATEWAY.sha(Path(__file__)))
    result['result'] = (
        'Actual Outcome entry supplies its native validation slots. Retained relocated source '
        'regions supply the fourteen-name table and JSON bytes. Actual required/optional type '
        'helpers retain the received builtin graph and source credits on positive return; '
        'defined pointer comparisons and missing-lookup rejection use actual Clight steps. '
        'A single DictNext borrow accounts for each native output store, separately from ownership.')
    result['remaining'] = [
        'The original decoded caller and source-region history must supply the validation entry inputs.',
        'The complete fourteen-field/JSON/files iteration must produce readiness at the SAME actual private-copy call.',
        'That call must consume the maintained copy/Path/owned-Outcome and original Workspace return proofs.',
        'Physical channel provenance, global filesystem custody, public caller integration and final identified VM acceptance remain M5.2 work.',
    ]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', type=Path, required=True)
    parser.add_argument('--propose', action='store_true')
    args = parser.parse_args()
    result = record(args.replay)
    (WORK / 'proposal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    if not args.propose and result != json.loads(REVIEW.read_text()):
        raise ValueError('Validation statements/interfaces/bindings differ; review the proposal')
    print('Validation source types, assumptions and independent kernel check passed; M5.2 remains open.')


if __name__ == '__main__':
    main()
