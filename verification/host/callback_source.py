#!/usr/bin/env python3
"""Review actual source callback control, primitive interfaces and class-cell consumers."""
# §FS-assurance.evidence: New source connections retain complete statements and assumptions.
import argparse
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
REVIEW = ROOT / 'assurance/host-callback-source-review.json'
WORK = ROOT / '.tools/host/callback-source'
MODULES = [
    'GatewayLinkedSource', 'GatewayLinkedPointerExecution', 'GatewayLoaderOrigins',
    'GatewayOrdinarySource', 'GatewayOrdinaryControl', 'GatewayOrdinaryExecution', 'GatewayOrdinaryMemory',
    'GatewayCallbackEntries', 'GatewayRuntimeMemory', 'GatewayRuntimeCoverage', 'GatewayCoveredPointers',
    'GatewayNoStoreControl', 'GatewayReadOnlyBarrier', 'GatewayNoStoreEntry', 'GatewayInitializationQueryControl',
    'GatewayInitializationNoStores', 'GatewayGuardedInitializer', 'GatewaySourceCallbacks', 'GatewayScopedBackend',
    'GatewaySourceFrames', 'GatewayGuardedFrames', 'GatewayCallbackGuards', 'GatewayCallbackInitialization',
    'GatewayCallbackRetention', 'GatewayLinkedAddresses', 'GatewayPointerEquivalence', 'GatewayRuntimeRetention',
    'GatewaySDKCapabilities', 'GatewaySourcePathExecution', 'GatewayGCVisitorSource', 'GatewayCallerClassCells',
    'GatewayRuntimeEpisodes', 'GatewayObservedCallbacks',
]
INTERFACES = [
    'gateway_linked_program', 'gateway_runtime_registration', 'gateway_loaded_fragment_origins',
    'gateway_ordinary_signature', 'gateway_ordinary_callee', 'gateway_ordinary_action', 'gateway_ordinary_source',
    'gateway_callback_registered', 'gateway_callback_expression', 'gateway_callback_body',
    'gateway_callback_dynamic', 'gateway_runtime_memory_step', 'gateway_runtime_memory_steps',
    'gateway_runtime_memory_scope', 'gateway_callback_memory_origin', 'gateway_callback_pointer_origin',
    'gateway_covered_step', 'gateway_covered_steps', 'gateway_nostore_control', 'gateway_readonly_source',
    'gateway_initialization_query_laws', 'gateway_source_callbacks', 'gateway_scoped_backend',
    'gateway_source_frame_control', 'gateway_reentry_guard', 'gateway_interpreter_result_shapes',
    'gateway_sdk_capabilities', 'gateway_runtime_episode', 'gateway_observed_step', 'gateway_observed_callbacks',
]


def record(replay):
    spec = importlib.util.spec_from_file_location('host_callback_source_engine', HERE / 'source_epoch.py')
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    engine.MODULES = MODULES
    engine.INTERFACES = INTERFACES
    engine.WORK = WORK
    result = engine.record(replay)
    result['schema'] = 'leancage-host-callback-source-review-v1'
    result['tool_sha256'] = engine.GATEWAY.sha(Path(__file__))
    result['query_engine_sha256'] = engine.GATEWAY.sha(HERE / 'source_epoch.py')
    before = ROOT / 'assurance/host-callback-before-dynamic.json.gz'
    if before.is_file():
        result['source_admission_revision'] = dict(
            predecessor=str(before.relative_to(ROOT)), predecessor_sha256=engine.GATEWAY.sha(before),
            reason='Review identified the actual native sigaction handler passed dynamically. Source admission now includes actual function-address value uses outside direct C call positions, alongside static relocations and exports; private initializer exclusion and all affected source proofs are checked again.')
    result['result'] = (
        'Actual registered application callback source trees derive private-address origin retention and a '
        'conditional five-cell class/flag frame. The real initializer rejects guarded reentry at every source '
        'prefix; ordinary source excludes those writers. Genuine external SDK linkage preserves source '
        'functions, layouts and private global addresses. World-indexed callback episodes retain the same '
        'actual SDK occurrence and source history. Runtime/caller consumers derive later class-cell loads. '
        'A nonempty SDK visitor binding has a constructive maintained traverse source path.')
    result['remaining'] = [
        'Actual runtime adapters must supply per-fragment loader origins and each same-occurrence SDK memory/world episode; these are explicit primitive contracts, not proved CPython internals.',
        'Physical source resumption must match the surviving process/image/exec incarnation; symbolic live control alone proves no physical liveness after exec or exit.',
        'The cumulative original initializer must produce class/root tickets, immutable FromSpec bindings and bootstrap-buffer retention; the source callback frame alone supplies none of these ownership facts.',
        'Original public argument extraction, Outcome validation/copy/presentation ownership, physical channel provenance, filesystem custody and final M5.2 acceptance remain delivery work.',
    ]
    fixture = ROOT / '.tools/host/gc-visitor-result.json'
    if fixture.is_file():
        result['native_gc_fixture'] = dict(path=str(fixture.relative_to(ROOT)),
                                           sha256=engine.GATEWAY.sha(fixture), result=json.loads(fixture.read_text()))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', type=Path, required=True)
    parser.add_argument('--propose', action='store_true')
    args = parser.parse_args()
    result = record(args.replay)
    (WORK / 'proposal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    if not args.propose and result != json.loads(REVIEW.read_text()):
        raise ValueError('Callback source statements/interfaces/bindings differ; inspect the proposal')
    print('Callback source statements/interfaces/axioms and independent kernel check passed; delivery remains open.')


if __name__ == '__main__':
    main()
