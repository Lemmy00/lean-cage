#!/usr/bin/env python3
"""Replay additive effect/endpoint evidence; never regenerate expectations."""
# §AR-m4-effects.gate: Full statements, foundations and preserved source identities.
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'm4'))
from bootstrap import WORK, digest, environment
from prover import compile_file, flags

DIRECTORY = ROOT / 'm4/connection'
MANIFEST = ROOT / 'assurance/m4-connection-claims.json'
EVIDENCE = ROOT / 'assurance/m4-connection-evidence.json'
OBLIGATIONS = ROOT / 'assurance/m4-obligations.json'
WRITEALL_EVIDENCE = ROOT / 'assurance/m4-writeall-evidence.json'
BASELINE_CLAIMS = ROOT / 'assurance/m4-writeall-baseline-claims.json'
PRIMITIVES_BASELINE = ROOT / 'assurance/m4-primitives-baseline-claims.json'
PRIMITIVES_EVIDENCE = ROOT / 'assurance/m4-primitives-evidence.json'
WRITERS_BASELINE = ROOT / 'assurance/m4-writers-baseline-claims.json'
WRITERS_EVIDENCE = ROOT / 'assurance/m4-writers-evidence.json'
LIBRARY_BASELINE = ROOT / 'assurance/m4-library-baseline-claims.json'
LIBRARY_EVIDENCE = ROOT / 'assurance/m4-library-evidence.json'
STRUCTURES_BASELINE = ROOT / 'assurance/m4-structures-baseline-claims.json'
STRUCTURES_EVIDENCE = ROOT / 'assurance/m4-structures-evidence.json'
CALLERS_BASELINE = ROOT / 'assurance/m4-callers-baseline-claims.json'
CALLERS_EVIDENCE = ROOT / 'assurance/m4-callers-evidence.json'
DECODER_BASELINE = ROOT / 'assurance/m4-decoder-baseline-claims.json'
DECODER_EVIDENCE = ROOT / 'assurance/m4-decoder-evidence.json'
SENDER_BASELINE = ROOT / 'assurance/m4-sender-baseline-claims.json'
SENDER_EVIDENCE = ROOT / 'assurance/m4-sender-evidence.json'
RECEIVER_BASELINE = ROOT / 'assurance/m4-receiver-baseline-claims.json'
RECEIVER_EVIDENCE = ROOT / 'assurance/m4-receiver-evidence.json'
SENDER_QUERY_MODULES = ['IO', 'Machine', 'ClightSteps', 'WriteMemory', 'WriteAll', 'WriteWitnesses', 'Deterministic', 'ErrorNumber', 'Readers', 'StoreSteps', 'WriteBytes', 'Writers', 'CodecRoundtrip', 'Library', 'ProcessEffects', 'LibraryMachine', 'LibraryPreservation', 'LibraryControl', 'GlobalReads', 'Fault', 'LibraryWitnesses', 'LocalAccess', 'ScalarMemory', 'ResultLayout', 'ResultSource', 'ResultSafety', 'ResultWitnesses', 'CallContexts', 'CallAccess', 'CallPaths', 'WriteCallers', 'FreshMemory', 'CallProgress', 'ExitControl', 'CallEvents', 'FailureSource', 'CallEventsDraft', 'CallProgressDraft', 'ExitControlDraft', 'HelperProgress', 'ReportingTrace', 'ExitEvents', 'ExitEventsDraft', 'FailureSourceDraft', 'FreshMemoryDraft', 'FailureMemory', 'FailureContract', 'FailureContractDraft', 'FailureMemoryDraft', 'FailureBranches', 'FailureBranchesDraft', 'HelperProgressDraft', 'FailureSafety', 'FailureSafetyDraft', 'FailureExit', 'ReportingTraceDraft', 'FailureTrace', 'FailureTraceDraft', 'FailureRuns', 'FailureRunsDraft', 'FailureError', 'FailureErrorDraft', 'FailureWitnesses', 'FrameBytes', 'ComparisonControl', 'SourcePaths', 'DecoderLayout', 'DecoderSource', 'DecoderMemory', 'SequencePaths', 'SourceReach', 'DecoderCompare', 'DecoderControl', 'DecoderHeader', 'DecoderZeros', 'DecoderFields', 'SwitchControl', 'DecoderCommon', 'DecoderTags', 'DecoderValidity', 'DecoderInput', 'DecoderPayload', 'SourceConsequences', 'DecoderAssembly', 'ComparisonRuns', 'SourceGuarantees', 'ComparisonGuarantees', 'DecoderProgram', 'DecoderRuns', 'DecoderAllocation', 'DecoderWitnesses', 'FrameRecord', 'WriteEffects', 'SenderSelectors', 'SenderGlobals', 'FrameAllocation', 'FrameCopy', 'SenderSource', 'BytePatch', 'SenderStorage', 'SenderAccess', 'SenderOperations', 'SenderEncodingPrefix', 'SenderZeros', 'SenderMemory', 'CopyControl', 'CopyPaths', 'SenderCopies', 'SenderEncodingTail', 'PatchLayout', 'SenderWire', 'SenderEncoding', 'SenderReportMemory', 'SenderReturn', 'ProcedureCalls', 'WriteGuarantees', 'ReportPaths', 'SenderGuards', 'SenderReportingSteps', 'SenderWriteReturn', 'SenderGuardStages', 'ReportConsequences', 'SenderLastReport', 'SenderShortReport', 'SenderOutcome', 'SenderDuplicate', 'SenderBadReserved', 'SenderReporting', 'CopyTrace', 'CopyComposition', 'ReportTrace', 'ReportRuns', 'ReportPrefixes', 'SenderProgram', 'SenderRuns', 'SenderWitnesses', 'ReportSuccessfulRuns', 'SenderSuccessfulRuns', 'ReportFailedRuns', 'SenderFailedRuns', 'ReportFirstWrite', 'SenderLossRuns', 'SenderSamples', 'SenderOutcomes', 'FinishSource', 'FinishControl', 'SourceQuietRuns', 'FinishMemory', 'FinishPreparation', 'FinishProgram', 'FinishPublication', 'FinishWitnesses', 'FinishDetails', 'FinishRuns']
DECODER_QUERY_MODULES = ['IO', 'Machine', 'ClightSteps', 'WriteMemory', 'WriteAll', 'WriteWitnesses', 'Deterministic', 'ErrorNumber', 'Readers', 'StoreSteps', 'WriteBytes', 'Writers', 'CodecRoundtrip', 'Library', 'ProcessEffects', 'LibraryMachine', 'LibraryPreservation', 'LibraryControl', 'GlobalReads', 'Fault', 'LibraryWitnesses', 'LocalAccess', 'ScalarMemory', 'ResultLayout', 'ResultSource', 'ResultSafety', 'ResultWitnesses', 'CallContexts', 'CallAccess', 'CallPaths', 'WriteCallers', 'FreshMemory', 'CallProgress', 'ExitControl', 'CallEvents', 'FailureSource', 'CallEventsDraft', 'CallProgressDraft', 'ExitControlDraft', 'HelperProgress', 'ReportingTrace', 'ExitEvents', 'ExitEventsDraft', 'FailureSourceDraft', 'FreshMemoryDraft', 'FailureMemory', 'FailureContract', 'FailureContractDraft', 'FailureMemoryDraft', 'FailureBranches', 'FailureBranchesDraft', 'HelperProgressDraft', 'FailureSafety', 'FailureSafetyDraft', 'FailureExit', 'ReportingTraceDraft', 'FailureTrace', 'FailureTraceDraft', 'FailureRuns', 'FailureRunsDraft', 'FailureError', 'FailureErrorDraft', 'FailureWitnesses', 'FrameBytes', 'ComparisonControl', 'SourcePaths', 'DecoderLayout', 'DecoderSource', 'DecoderMemory', 'SequencePaths', 'SourceReach', 'DecoderCompare', 'DecoderControl', 'DecoderHeader', 'DecoderZeros', 'DecoderFields', 'SwitchControl', 'DecoderCommon', 'DecoderTags', 'DecoderValidity', 'DecoderInput', 'DecoderPayload', 'SourceConsequences', 'DecoderAssembly', 'ComparisonRuns', 'SourceGuarantees', 'ComparisonGuarantees', 'DecoderProgram', 'DecoderRuns', 'DecoderAllocation', 'DecoderWitnesses']
BASELINE_QUERY_MODULES = ['IO', 'Machine', 'ClightSteps', 'WriteMemory', 'WriteAll', 'WriteWitnesses', 'Deterministic', 'ErrorNumber', 'Readers', 'StoreSteps', 'WriteBytes', 'Writers', 'CodecRoundtrip', 'Library', 'ProcessEffects', 'LibraryMachine', 'LibraryPreservation', 'LibraryControl', 'GlobalReads', 'Fault', 'LibraryWitnesses', 'LocalAccess', 'ScalarMemory', 'ResultLayout', 'ResultSource', 'ResultSafety', 'ResultWitnesses', 'CallContexts', 'CallAccess', 'CallPaths', 'WriteCallers', 'FreshMemory', 'CallProgress', 'ExitControl', 'HelperProgress', 'CallEvents', 'ReportingTrace', 'ExitEvents', 'FailureSource', 'FailureMemory', 'FailureBranches', 'FailureContract', 'FailureSafety', 'FailureTrace', 'FailureRuns', 'FailureError', 'FailureExit', 'FailureWitnesses']
COMPAT_MODULES = ['CallEventsDraft', 'CallProgressDraft', 'ExitControlDraft', 'ExitEventsDraft', 'FailureBranchesDraft', 'FailureContractDraft', 'FailureErrorDraft', 'FailureMemoryDraft', 'FailureRunsDraft', 'FailureSafetyDraft', 'FailureSourceDraft', 'FailureTraceDraft', 'FreshMemoryDraft', 'HelperProgressDraft', 'ReportingTraceDraft']
MODULES = ['IO', 'Machine', 'ClightSteps', 'WriteMemory', 'WriteAll', 'WriteWitnesses', 'Deterministic', 'ErrorNumber', 'Readers', 'StoreSteps', 'WriteBytes', 'Writers', 'CodecRoundtrip', 'Library', 'ProcessEffects', 'LibraryMachine', 'LibraryPreservation', 'LibraryControl', 'GlobalReads', 'Fault', 'LibraryWitnesses', 'LocalAccess', 'ScalarMemory', 'ResultLayout', 'ResultSource', 'ResultSafety', 'ResultWitnesses', 'CallContexts', 'CallAccess', 'CallPaths', 'WriteCallers', 'FreshMemory', 'CallProgress', 'ExitControl', 'CallEvents', 'FailureSource', 'CallEventsDraft', 'CallProgressDraft', 'ExitControlDraft', 'HelperProgress', 'ReportingTrace', 'ExitEvents', 'ExitEventsDraft', 'FailureSourceDraft', 'FreshMemoryDraft', 'FailureMemory', 'FailureContract', 'FailureContractDraft', 'FailureMemoryDraft', 'FailureBranches', 'FailureBranchesDraft', 'HelperProgressDraft', 'FailureSafety', 'FailureSafetyDraft', 'FailureExit', 'ReportingTraceDraft', 'FailureTrace', 'FailureTraceDraft', 'FailureRuns', 'FailureRunsDraft', 'FailureError', 'FailureErrorDraft', 'FailureWitnesses', 'FrameBytes', 'ComparisonControl', 'SourcePaths', 'DecoderLayout', 'DecoderSource', 'DecoderMemory', 'SequencePaths', 'SourceReach', 'DecoderCompare', 'DecoderControl', 'DecoderHeader', 'DecoderZeros', 'DecoderFields', 'SwitchControl', 'DecoderCommon', 'DecoderTags', 'DecoderValidity', 'DecoderInput', 'DecoderPayload', 'SourceConsequences', 'DecoderAssembly', 'ComparisonRuns', 'SourceGuarantees', 'ComparisonGuarantees', 'DecoderProgram', 'DecoderRuns', 'DecoderAllocation', 'DecoderWitnesses', 'FrameRecord', 'WriteEffects', 'SenderSelectors', 'SenderGlobals', 'FrameAllocation', 'FrameCopy', 'SenderSource', 'BytePatch', 'SenderStorage', 'SenderAccess', 'SenderOperations', 'SenderEncodingPrefix', 'SenderZeros', 'SenderMemory', 'CopyControl', 'CopyPaths', 'SenderCopies', 'SenderEncodingTail', 'PatchLayout', 'SenderWire', 'SenderEncoding', 'SenderReportMemory', 'SenderReturn', 'ProcedureCalls', 'WriteGuarantees', 'ReportPaths', 'SenderGuards', 'SenderReportingSteps', 'SenderWriteReturn', 'SenderGuardStages', 'ReportConsequences', 'SenderLastReport', 'SenderShortReport', 'SenderOutcome', 'SenderDuplicate', 'SenderBadReserved', 'SenderReporting', 'CopyTrace', 'CopyComposition', 'ReportTrace', 'ReportRuns', 'ReportPrefixes', 'SenderProgram', 'SenderRuns', 'SenderWitnesses', 'ReportSuccessfulRuns', 'SenderSuccessfulRuns', 'ReportFailedRuns', 'SenderFailedRuns', 'ReportFirstWrite', 'SenderLossRuns', 'SenderSamples', 'SenderOutcomes', 'FinishSource', 'FinishControl', 'SourceQuietRuns', 'FinishMemory', 'FinishPreparation', 'FinishProgram', 'FinishPublication', 'FinishWitnesses', 'FinishDetails', 'FinishRuns', 'ReceiverSource', 'ReceiverReadSource', 'ReceiverReadMemory', 'ReceiverReadControl', 'ReceiverRouting', 'ReceiverReadReturns', 'ReceiverReadStep', 'ResultOwnership', 'ReceiverAllocation', 'ReceiverPreparation', 'ReceiverMemory', 'ReceiverInput', 'ReceiverChoice', 'ReceiverSelectionSource', 'ReceiverCopyMemory', 'ReceiverFree', 'ReceiverTailSource', 'ReceiverConstruction', 'ReceiverEntry', 'CloseControl', 'ReceiverTrace', 'ReceiverReadHistory', 'ReceiverSelection', 'ReceiverClassification', 'ReceiverCloseMemory', 'ReceiverCloseSource', 'ReceiverTerminal', 'ReceiverTerminalTrace', 'ReceiverLoopTrace', 'ReceiverOutcomes', 'ReceiverBounds', 'ReceiverAccepted', 'ReceiverReadRuns', 'ReceiverTerminalRuns', 'ReceiverWitnessInputs', 'ReceiverErrorRuns', 'ReceiverRetries', 'ReceiverRuns', 'ReceiverFaultRuns', 'ReceiverSamples', 'ReceiverReadGuarantee', 'ReceiverProgram', 'ReceiverLossRuns']
ALLOWED_COQ = {
    'ClassicalDedekindReals.sig_not_dec', 'ClassicalDedekindReals.sig_forall_dec',
    'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic',
    'Events.external_functions_sem', 'Events.inline_assembly_sem',
}
ALLOWED_LEAN = {'propext', 'Classical.choice', 'Quot.sound'}


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [p for p in (DIRECTORY / 'compat').iterdir() if p.is_file()]
    paths += [ROOT / 'scripts/check_m4.sh', ROOT / 'scripts/check_m4_connection.sh',
              ROOT / 'docs/architecture/AR-m4-effects.md',
              ROOT / 'docs/decisions/architectural/DA-m4-effects.md',
              ROOT / 'docs/decisions/architectural/README.md',
              ROOT / 'docs/roadmap.md', ROOT / 'docs/architecture/README.md',
              ROOT / 'docs/reviews/M4-progress.md',
              ROOT / 'docs/reviews/M4-writeall.md', ROOT / 'docs/reviews/M4-primitives.md',
              ROOT / 'docs/reviews/M4-writers.md', ROOT / 'docs/reviews/M4-library.md',
              ROOT / 'docs/architecture/AR-m4-library.md',
              ROOT / 'docs/architecture/AR-m4-structures.md', ROOT / 'docs/reviews/M4-structures.md',
              ROOT / 'docs/architecture/AR-m4-callers.md', ROOT / 'docs/reviews/M4-callers.md',
              CALLERS_BASELINE, STRUCTURES_BASELINE, DECODER_BASELINE, SENDER_BASELINE, RECEIVER_BASELINE,
              ROOT / 'docs/architecture/AR-m4-receiver.md', ROOT / 'docs/reviews/M4-receiver.md',
              ROOT / 'docs/architecture/AR-m4-sender.md', ROOT / 'docs/reviews/M4-sender.md',
              ROOT / 'docs/architecture/AR-m4-decoder.md', ROOT / 'docs/reviews/M4-decoder.md',
              ROOT / 'docs/functional-spec/FS-assurance.md', LIBRARY_BASELINE,
              BASELINE_CLAIMS, PRIMITIVES_BASELINE, WRITERS_BASELINE, OBLIGATIONS]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}


def verify_hashes(expected, root=ROOT):
    for relative, expected_hash in expected.items():
        path = Path(relative)
        if path.is_absolute() or '..' in path.parts:
            raise ValueError(f'non-project evidence path: {relative}')
        if digest(root / path) != expected_hash:
            raise ValueError(f'stale or tampered connection input: {relative}')


def module_source(module):
    return DIRECTORY / ('compat' if module in COMPAT_MODULES else '') / (module + '.v')


def project_imports(source):
    source = re.sub(r'\(\*.*?\*\)', '', source, flags=re.S)
    imports = []
    pattern = r'(?:(?:From\s+(\w+)\s+)?Require\s+(?:(?:Import|Export)\s+)?([\w.\s]+?)\.(?!\w))'
    if re.search(r'\b(?:Require|Load)\b', re.sub(pattern, '', source)):
        raise ValueError('unsupported proof import syntax')
    for match in re.finditer(pattern, source):
        namespace, names = match.groups()
        if namespace is None:
            if any('.' in name for name in names.split()):
                raise ValueError('undeclared qualified project proof import')
            imports.extend(names.split())
        elif namespace not in {'Coq', 'compcert'}:
            raise ValueError(f'undeclared proof namespace: {namespace}')
    return imports


def declaration_names():
    authored = list(DIRECTORY.rglob('*.v'))
    if len(authored) != len(MODULES) or {p.stem for p in authored} != set(MODULES):
        raise ValueError('Rocq module inventory does not cover every authored proof file')
    records = []
    available = {'Slice', 'Codec'}  # Both are checked by the preserved M4.1 gate.
    for module in MODULES:
        source = module_source(module).read_text()
        source = re.sub(r'\(\*.*?\*\)', '', source, flags=re.S)
        for imported in project_imports(source):
            if imported not in available:
                raise ValueError(f'undeclared or unordered project proof import: {module}: {imported}')
        if re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Abort)\b', source):
            raise ValueError(f'unfinished/custom-axiom connection proof: {module}')
        names = re.findall(r'^\s*(?:Theorem|Lemma|Example|Corollary|Fact|Remark|Proposition)\s+(\w+)', source, re.M)
        if not names:
            raise ValueError(f'empty theorem inventory: {module}')
        records += [module + '.' + name for name in names]
        available.add(module)
    return records


def rocq_inventory():
    names = declaration_names()
    # Keep the preceding manifest's printing context; new modules cannot shadow
    # names in frozen full statements. Both contexts still audit full assumptions.
    groups = [
        (BASELINE_QUERY_MODULES, [(i, n) for i, n in enumerate(names)
                                 if n.split('.')[0] in BASELINE_QUERY_MODULES]),
        (DECODER_QUERY_MODULES, [(i, n) for i, n in enumerate(names)
                   if n.split('.')[0] in DECODER_QUERY_MODULES and n.split('.')[0] not in BASELINE_QUERY_MODULES]),
        (SENDER_QUERY_MODULES, [(i, n) for i, n in enumerate(names)
                   if n.split('.')[0] in SENDER_QUERY_MODULES and n.split('.')[0] not in DECODER_QUERY_MODULES]),
        (MODULES, [(i, n) for i, n in enumerate(names)
                   if n.split('.')[0] not in SENDER_QUERY_MODULES]),
    ]
    for group, (modules, selected) in enumerate(groups):
        for batch, start in enumerate(range(0, len(selected), 100)):
            query = ['Require Import ' + ' '.join(modules) + '.',
                     'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
            for i, name in selected[start:start + 100]:
                query += [f'Redirect "connection-type-{i}" Check @{name}.',
                          f'Redirect "connection-axioms-{i}" Print Assumptions {name}.']
            filename = f'ConnectionAudit{group}_{batch}.v'
            (WORK / 'input' / filename).write_text('\n'.join(query) + '\n')
            result = compile_file(filename)
            if result.returncode:
                raise ValueError(result.stdout + result.stderr)
    records = []
    for i, name in enumerate(names):
        full_type = (WORK / f'input/connection-type-{i}.out').read_text().strip()
        assumptions = (WORK / f'input/connection-axioms-{i}.out').read_text().strip()
        axioms = sorted(set(re.findall(r'^([A-Za-z0-9_.]+)(?:\s*:|\s*$)', assumptions, re.M)) - {'Axioms'})
        if set(axioms) - ALLOWED_COQ:
            raise ValueError(f'unreviewed Rocq foundation: {name}: {axioms}')
        if '...' in full_type:
            raise ValueError(f'truncated Rocq statement: {name}')
        records.append({'name': name, 'full_type': full_type,
                        'transitive_assumptions': assumptions, 'assumption_names': axioms})
    return records


def lean_inventory():
    spec = importlib.util.spec_from_file_location('connection_m3_audit', ROOT / 'scripts/audit_m3.py')
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    source = (DIRECTORY / 'Endpoints.lean').read_text()
    source = source.replace('import LeanCageM3\n', '', 1)
    source += '''
elab "#audit_connection" : command => do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name info =>
    if info.isTheorem && (`LeanCageM4).isPrefixOf name then names.push name else names
  logInfo m!"LEANCAGE_AUDIT {(Lean.Json.mkObj [("inventory", toJson (names.map Name.toString))]).compress}"
  for name in names do
    logInfo m!"LEANCAGE_AUDIT {(← declarationRecord name).compress}"
#audit_connection
'''
    records = audit.query_environment(extra_source=source)
    inventory = [r['inventory'] for r in records if 'inventory' in r]
    actual = sorted([r for r in records if 'name' in r], key=lambda r: r['name'])
    if len(inventory) != 1 or not actual or sorted(inventory[0]) != [r['name'] for r in actual]:
        raise ValueError('missing or inconsistent actual Lean theorem inventory')
    for record in actual:
        if not record['is_theorem'] or set(record['axioms']) - ALLOWED_LEAN:
            raise ValueError(f'unreviewed Lean claim/foundations: {record}')
    return actual


def validate_obligations(data):
    expected = set()
    for filename in ['AR-lifecycle.md', 'AR-workspace.md']:
        expected.update(re.findall(r'^\| (M4-[a-z0-9-]+) \|',
                                   (ROOT / 'docs/architecture' / filename).read_text(), re.M))
    entries = data['obligations']
    keys = [entry['key'] for entry in entries]
    if len(expected) != 16 or len(keys) != len(set(keys)) or set(keys) != expected:
        raise ValueError('missing/duplicate/extra original M2/M3 correspondence obligation')
    for entry in entries:
        if entry['status'] != 'open' or entry['closure_evidence']:
            raise ValueError(f'unreviewed correspondence closure: {entry["key"]}')
        if not entry['required_proof'] or not entry['source_boundary']:
            raise ValueError(f'missing concrete correspondence boundary: {entry["key"]}')
    if data['m4_complete'] is not False:
        raise ValueError('open correspondence obligations cannot complete M4')


def validate_claims(expected, actual):
    if any('...' in record['full_type'] for record in actual['rocq_declarations']):
        raise ValueError('truncated Rocq statement')
    for key in ['rocq_declarations', 'lean_declarations']:
        if not actual[key] or actual[key] != expected[key]:
            raise ValueError(f'reviewed connection statement/assumption inventory differs: {key}')


def validate_preserved_claims(previous, actual):
    for key in ['rocq_declarations', 'lean_declarations']:
        old = previous[key]
        current = {record['name']: record for record in actual[key]}
        if not old or any(current.get(record['name']) != record for record in old):
            raise ValueError(f'previous connection proof changed or disappeared: {key}')


def validate_artifacts(expected, actual, *, subset=False):
    if not expected or any(actual.get(name) != value for name, value in expected.items()):
        raise ValueError('checked proof artifact identity differs')
    if not subset and set(actual) != set(expected):
        raise ValueError('checked proof artifact inventory differs')


def collect():
    before = sources()
    logs = {}
    for module in MODULES:
        filename = module + '.v'
        shutil.copyfile(module_source(module), WORK / 'input' / filename)
        result = compile_file(filename)
        if result.returncode:
            raise ValueError(result.stdout + result.stderr)
        logs[filename] = result.stdout + result.stderr
    rocq = rocq_inventory()
    result = subprocess.run([str(WORK / 'root/usr/bin/coqchk'), '-silent', *flags(), *MODULES],
                            cwd=WORK / 'input', env=environment(), capture_output=True,
                            text=True, timeout=180)
    if result.returncode:
        raise ValueError(result.stdout + result.stderr)
    lean = lean_inventory()
    if sources() != before:
        raise ValueError('connection sources changed during proof replay')
    report = {'source_sha256': sources(), 'rocq_declarations': rocq, 'lean_declarations': lean,
              'logs': logs, 'coqchk_output': result.stdout + result.stderr,
              'artifact_sha256': {module + '.vo': digest(WORK / 'input' / (module + '.vo'))
                                  for module in MODULES}}
    (WORK / 'connection-report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def check():
    expected = json.loads(MANIFEST.read_text())
    evidence = json.loads(EVIDENCE.read_text())
    writeall = json.loads(WRITEALL_EVIDENCE.read_text())
    primitives = json.loads(PRIMITIVES_EVIDENCE.read_text())
    writers = json.loads(WRITERS_EVIDENCE.read_text())
    library = json.loads(LIBRARY_EVIDENCE.read_text())
    structures = json.loads(STRUCTURES_EVIDENCE.read_text())
    callers = json.loads(CALLERS_EVIDENCE.read_text())
    decoder = json.loads(DECODER_EVIDENCE.read_text())
    sender = json.loads(SENDER_EVIDENCE.read_text())
    receiver = json.loads(RECEIVER_EVIDENCE.read_text())
    if receiver['status'] != 'complete terminal-error receiver source submilestone; M4.2-M4.6 incomplete':
        raise ValueError('local receiver source cannot complete M4 correspondence')
    if digest(MANIFEST) != receiver['claims_sha256']:
        raise ValueError('receiver reviewed claim manifest identity differs')
    verify_hashes(receiver['preserved_sha256'])
    verify_hashes(receiver['archived_receipts_sha256'])
    if sender['status'] != 'complete frame sender and finish source submilestone; M4.2-M4.6 incomplete':
        raise ValueError('local sender and finish source cannot complete M4 correspondence')
    if digest(RECEIVER_BASELINE) != sender['claims_sha256']:
        raise ValueError('sender reviewed claim manifest identity differs')
    verify_hashes(sender['preserved_sha256'])
    verify_hashes(sender['archived_receipts_sha256'])
    if decoder['status'] != 'complete private-frame decoder source submilestone; M4.2-M4.6 incomplete':
        raise ValueError('local decoder source cannot complete M4 correspondence')
    if digest(SENDER_BASELINE) != decoder['claims_sha256']:
        raise ValueError('decoder reviewed claim manifest identity differs')
    verify_hashes(decoder['preserved_sha256'])
    verify_hashes(decoder['archived_receipts_sha256'])
    if callers['status'] != 'caller composition and complete child-failure source submilestone complete; M4.2-M4.6 incomplete':
        raise ValueError('child-failure source cannot complete M4 correspondence')
    if digest(DECODER_BASELINE) != callers['claims_sha256']:
        raise ValueError('caller reviewed claim manifest identity differs')
    verify_hashes(callers['preserved_sha256'])
    verify_hashes(callers['archived_receipts_sha256'])
    if structures['status'] != 'result constructor source submilestone complete; M4.2-M4.6 incomplete':
        raise ValueError('local result construction cannot complete M4 correspondence')
    if digest(CALLERS_BASELINE) != structures['claims_sha256']:
        raise ValueError('structure reviewed claim manifest identity differs')
    verify_hashes(structures['preserved_sha256'])
    verify_hashes(structures['archived_receipts_sha256'])
    if library['status'] != 'local library effects and fault source submilestone complete; M4.2-M4.6 incomplete':
        raise ValueError('local library effects cannot complete M4 correspondence')
    if digest(STRUCTURES_BASELINE) != library['claims_sha256']:
        raise ValueError('library reviewed claim manifest identity differs')
    verify_hashes(library['preserved_sha256'])
    verify_hashes(library['archived_receipts_sha256'])
    if writers['status'] != 'byte writers and codec round trip source submilestone complete; M4.2-M4.6 incomplete':
        raise ValueError('local codecs cannot complete M4 correspondence')
    if digest(LIBRARY_BASELINE) != writers['claims_sha256']:
        raise ValueError('byte writers reviewed claim manifest identity differs')
    verify_hashes(writers['preserved_sha256'])
    verify_hashes(writers['archived_receipts_sha256'])
    if primitives['status'] != 'reporting primitives source submilestone complete; M4.2-M4.6 incomplete':
        raise ValueError('local reporting primitives cannot complete M4 correspondence')
    if digest(WRITERS_BASELINE) != primitives['claims_sha256']:
        raise ValueError('reporting primitives reviewed claim manifest identity differs')
    verify_hashes(primitives['preserved_sha256'])
    verify_hashes(primitives['archived_receipts_sha256'])
    if writeall['status'] != 'write_all source submilestone complete; M4.2-M4.6 incomplete':
        raise ValueError('write_all alone cannot complete whole-slice or M4 correspondence')
    if digest(PRIMITIVES_BASELINE) != writeall['claims_sha256']:
        raise ValueError('write_all reviewed claim manifest identity differs')
    verify_hashes(writeall['preserved_sha256'])
    verify_hashes(writeall['archived_receipts_sha256'])
    if expected.get('m4_complete') is not False or evidence.get('status') != 'partial-M4.2; M4.2-M4.6 incomplete':
        raise ValueError('this partial effect/endpoint package cannot claim M4 completion')
    if sources() != expected['source_sha256']:
        raise ValueError('authored connection sources differ from reviewed evidence')
    verify_hashes(evidence['preserved_sha256'])
    verify_hashes(evidence['compiled_dependencies_sha256'])
    verify_hashes(evidence['archived_receipts_sha256'])
    # Require the old maintained-source/tool/ABI gate to have run on these exact inputs.
    # The shell wrapper runs it first; this direct invocation checks its source-bound report too.
    old = json.loads((ROOT / 'assurance/m4-evidence.json').read_text())
    old_claims = json.loads((ROOT / 'assurance/m4-claims.json').read_text())
    prior = json.loads((WORK / 'check-report.json').read_text())
    spec = importlib.util.spec_from_file_location('connection_legacy_check', ROOT / 'm4/check.py')
    legacy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(legacy)
    if legacy.sources() != old_claims['source_sha256'] or prior['source_sha256'] != legacy.sources():
        raise ValueError('M4.1 source replay is stale; run scripts/check_m4_connection.sh')
    legacy.validate_input_artifacts(old['source_connection'], WORK / 'input')
    if prior['rocq_declarations'] != old_claims['rocq_declarations']:
        raise ValueError('M4.1 theorem replay differs')
    for name, expected_hash in old['runtime_inputs_sha256'].items():
        path = Path(name) if Path(name).is_absolute() else ROOT / name
        if digest(path) != expected_hash:
            raise ValueError(f'proof/runtime input differs: {name}')
    for name, expected_hash in prior['artifact_sha256'].items():
        if digest(WORK / 'input' / name) != expected_hash:
            raise ValueError(f'M4.1 compiled input differs: {name}')
    validate_obligations(json.loads(OBLIGATIONS.read_text()))
    actual = collect()
    if actual['source_sha256'] != expected['source_sha256']:
        raise ValueError('reviewed connection source identities changed during replay')
    verify_hashes(evidence['preserved_sha256'])
    verify_hashes(evidence['compiled_dependencies_sha256'])
    validate_claims(expected, actual)
    validate_preserved_claims(json.loads(BASELINE_CLAIMS.read_text()), actual)
    validate_preserved_claims(json.loads(PRIMITIVES_BASELINE.read_text()), actual)
    validate_artifacts(writeall['artifact_sha256'], actual['artifact_sha256'], subset=True)
    validate_preserved_claims(json.loads(WRITERS_BASELINE.read_text()), actual)
    validate_artifacts(primitives['artifact_sha256'], actual['artifact_sha256'], subset=True)
    validate_preserved_claims(json.loads(LIBRARY_BASELINE.read_text()), actual)
    validate_artifacts(writers['artifact_sha256'], actual['artifact_sha256'], subset=True)
    validate_preserved_claims(json.loads(STRUCTURES_BASELINE.read_text()), actual)
    validate_artifacts(library['artifact_sha256'], actual['artifact_sha256'], subset=True)
    validate_preserved_claims(json.loads(CALLERS_BASELINE.read_text()), actual)
    validate_artifacts(structures['artifact_sha256'], actual['artifact_sha256'], subset=True)
    validate_preserved_claims(json.loads(DECODER_BASELINE.read_text()), actual)
    validate_artifacts(callers['artifact_sha256'], actual['artifact_sha256'], subset=True)
    validate_preserved_claims(json.loads(SENDER_BASELINE.read_text()), actual)
    validate_artifacts(decoder['artifact_sha256'], actual['artifact_sha256'], subset=True)
    validate_preserved_claims(json.loads(RECEIVER_BASELINE.read_text()), actual)
    validate_artifacts(sender['artifact_sha256'], actual['artifact_sha256'], subset=True)
    validate_artifacts(receiver['artifact_sha256'], actual['artifact_sha256'])
    result = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', str(DIRECTORY),
                             '-p', 'test_*.py', '-v'], cwd=ROOT,
                            capture_output=True, text=True, timeout=60)
    if result.returncode:
        raise ValueError(result.stdout + result.stderr)
    print(result.stdout + result.stderr, end='')
    print(f'Connection checked: {len(actual["rocq_declarations"])} Rocq theorems, '
          f'{len(actual["lean_declarations"])} Lean theorems, coqchk passed; 16 original obligations OPEN')
    print('Universal write_all, errno, byte reader/writer source safety and codec round trips checked; '
          'local library effects, fault, result construction, actual caller composition, complete fail_child, private decode_frame, frame sending, finish publication/exit mapping and complete terminal receiver with exact read-trace classification checked; '
          'whole-slice C/Lean simulation, Linux/compiler/runtime correspondence and full M4 remain UNPROVED')


if __name__ == '__main__':
    check()
