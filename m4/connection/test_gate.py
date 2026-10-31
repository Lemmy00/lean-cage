#!/usr/bin/env python3
"""Evidence-boundary regressions; no host workloads or Linux effects."""
# §AR-m4-effects.gate: Reject stale bytes, statement/axiom drift and invented closure.
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('connection_gate', Path(__file__).with_name('check.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class EvidenceGate(unittest.TestCase):
    def setUp(self):
        self.claims = json.loads(gate.MANIFEST.read_text())
        self.obligations = json.loads(gate.OBLIGATIONS.read_text())

    def test_reviewed_inventory(self):
        gate.validate_claims(self.claims, self.claims)
        self.assertEqual([r['name'] for r in self.claims['rocq_declarations']], gate.declaration_names())

    def test_universal_source_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'WriteAll.source_write_all_body', 'WriteAll.actual_program_symbols',
            'WriteAll.write_all_prefix_safety', 'WriteAll.write_all_defined_prefix',
            'WriteAll.write_all_return_exact', 'WriteAll.write_all_success_exists',
            'WriteWitnesses.arbitrary_write_ownership',
            'WriteWitnesses.source_retries_then_success',
            'WriteWitnesses.source_short_write_then_success',
            'WriteWitnesses.source_error_return', 'WriteWitnesses.source_zero_return',
            'WriteWitnesses.source_wait_then_partial_loss',
        }.issubset(names))

    def test_omitted_proof_module_rejected(self):
        with patch.object(gate, 'MODULES', gate.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, 'every authored proof file'):
                gate.declaration_names()

    def test_preserved_claim_cannot_disappear(self):
        previous = json.loads(gate.BASELINE_CLAIMS.read_text())
        gate.validate_preserved_claims(previous, self.claims)
        for key in ['rocq_declarations', 'lean_declarations']:
            actual = copy.deepcopy(self.claims)
            old_name = previous[key][0]['name']
            actual[key] = [record for record in actual[key] if record['name'] != old_name]
            with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
                gate.validate_preserved_claims(previous, actual)

    def test_preserved_claim_cannot_change(self):
        previous = json.loads(gate.BASELINE_CLAIMS.read_text())
        for key, field in [('rocq_declarations', 'transitive_assumptions'),
                           ('lean_declarations', 'axioms')]:
            actual = copy.deepcopy(self.claims)
            old_name = previous[key][0]['name']
            record = next(record for record in actual[key] if record['name'] == old_name)
            record[field] = 'changed foundation'
            with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
                gate.validate_preserved_claims(previous, actual)

    def test_stale_source_and_path_escape(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'input').write_bytes(b'reviewed')
            record = {'input': hashlib.sha256(b'reviewed').hexdigest()}
            gate.verify_hashes(record, root)
            (root / 'input').write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'tampered'):
                gate.verify_hashes(record, root)
            for path in ['../outside', '/absolute']:
                with self.assertRaisesRegex(ValueError, 'non-project'):
                    gate.verify_hashes({path: '0' * 64}, root)

    def test_theorem_and_assumption_drift(self):
        for field in ['full_type', 'transitive_assumptions', 'assumption_names']:
            actual = copy.deepcopy(self.claims)
            actual['rocq_declarations'][0][field] = 'altered'
            with self.assertRaisesRegex(ValueError, 'inventory differs'):
                gate.validate_claims(self.claims, actual)
        actual = copy.deepcopy(self.claims)
        actual['lean_declarations'][0]['axioms'] = ['sorryAx']
        with self.assertRaisesRegex(ValueError, 'inventory differs'):
            gate.validate_claims(self.claims, actual)

    def test_missing_or_empty_proof(self):
        for key in ['rocq_declarations', 'lean_declarations']:
            for value in [[], self.claims[key][1:]]:
                actual = copy.deepcopy(self.claims)
                actual[key] = value
                with self.assertRaisesRegex(ValueError, 'inventory differs'):
                    gate.validate_claims(self.claims, actual)

    def test_all_original_obligations_present(self):
        gate.validate_obligations(self.obligations)
        self.assertEqual(len(self.obligations['obligations']), 16)

    def test_obligation_removal_or_duplicate(self):
        for duplicate in [False, True]:
            actual = copy.deepcopy(self.obligations)
            actual['obligations'].pop()
            if duplicate:
                actual['obligations'].append(actual['obligations'][0])
            with self.assertRaisesRegex(ValueError, 'correspondence obligation'):
                gate.validate_obligations(actual)

    def test_invented_completion(self):
        actual = copy.deepcopy(self.obligations)
        actual['m4_complete'] = True
        with self.assertRaisesRegex(ValueError, 'cannot complete'):
            gate.validate_obligations(actual)
        for field, value in [('status', 'proved'), ('closure_evidence', ['source hash'])]:
            actual = copy.deepcopy(self.obligations)
            actual['obligations'][0][field] = value
            with self.assertRaisesRegex(ValueError, 'unreviewed correspondence closure'):
                gate.validate_obligations(actual)

    def test_reporting_primitives_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'ErrorNumber.source_error_number_body', 'ErrorNumber.source_execution',
            'ErrorNumber.normalize_signed', 'ErrorNumber.normalize_range',
            'ErrorNumber.error_number_return_exact', 'ErrorNumber.error_number_defined_prefix',
            'ErrorNumber.error_number_all_prefixes', 'ErrorNumber.error_number_at_most_35_steps',
            'ErrorNumber.error_number_loss_every_prefix',
            'ErrorNumber.arbitrary_errno_source_witness',
            'Readers.reader_execution', 'Readers.reader_return_exact',
            'Readers.reader_all_prefixes', 'Readers.reader_defined_prefix',
            'Readers.reader_loss_every_prefix',
            'Readers.arbitrary_get32_input', 'Readers.arbitrary_get64_input',
        }.issubset(names))

    def test_preserved_artifacts_and_complete_extension(self):
        previous = {'IO.vo': 'old-proof'}
        extended = {**previous, 'Readers.vo': 'new-proof'}
        gate.validate_artifacts(previous, extended, subset=True)
        gate.validate_artifacts(extended, extended)
        for actual in [{'Readers.vo': 'new-proof'}, {**extended, 'IO.vo': 'changed-proof'}]:
            with self.assertRaisesRegex(ValueError, 'artifact identity differs'):
                gate.validate_artifacts(previous, actual, subset=True)
        with self.assertRaisesRegex(ValueError, 'artifact inventory differs'):
            gate.validate_artifacts(previous, extended)
        with self.assertRaisesRegex(ValueError, 'artifact identity differs'):
            gate.validate_artifacts({}, extended, subset=True)

    def test_all_write_loop_claims_preserved(self):
        previous = json.loads(gate.PRIMITIVES_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 126)
        self.assertEqual(len(previous['lean_declarations']), 12)
        gate.validate_preserved_claims(previous, self.claims)
        for field in ['full_type', 'transitive_assumptions', 'assumption_names']:
            actual = copy.deepcopy(self.claims)
            record = next(r for r in actual['rocq_declarations']
                          if r['name'] == 'WriteAll.write_all_prefix_safety')
            record[field] = 'changed previously checked claim'
            with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
                gate.validate_preserved_claims(previous, actual)

    def test_truncated_statement_cannot_be_approved(self):
        actual = copy.deepcopy(self.claims)
        actual['rocq_declarations'][0]['full_type'] = 'forall x, ...'
        with self.assertRaisesRegex(ValueError, 'truncated Rocq statement'):
            gate.validate_claims(actual, actual)

    def test_writer_source_and_roundtrip_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'StoreSteps.store_path_all', 'StoreSteps.store_path_defined_prefix',
            'StoreSteps.store_path_loss_every_prefix',
            'WriteBytes.byte_writes_permissions', 'WriteBytes.byte_writes_outside',
            'WriteBytes.byte_writes_content', 'WriteBytes.writer_prefix_content',
            'Writers.writer_execution', 'Writers.writer_return_exact',
            'Writers.writer_all_prefixes', 'Writers.writer_defined_prefix',
            'Writers.writer_loss_every_prefix', 'Writers.put32_first_byte_loss',
            'Writers.arbitrary_put32_input', 'Writers.arbitrary_put64_input',
            'Writers.arbitrary_unaligned_writer_inputs',
            'CodecRoundtrip.put_get32_word', 'CodecRoundtrip.put_get64_word',
            'CodecRoundtrip.put32_source_roundtrip', 'CodecRoundtrip.put64_source_roundtrip',
        }.issubset(names))

    def test_all_reporting_primitives_preserved(self):
        previous = json.loads(gate.WRITERS_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 173)
        self.assertEqual(len(previous['lean_declarations']), 12)
        gate.validate_preserved_claims(previous, self.claims)
        actual = copy.deepcopy(self.claims)
        record = next(r for r in actual['rocq_declarations']
                      if r['name'] == 'Readers.reader_all_prefixes')
        record['full_type'] = 'weakened preserved reader claim'
        with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
            gate.validate_preserved_claims(previous, actual)

    def test_library_effects_and_source_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'Library.strcmp_zero_iff', 'Library.memcmp_zero_iff',
            'Library.copy_nonprefix_schedule_exists', 'Library.partial_copy_source',
            'ProcessEffects.close_error_stores_errno', 'ProcessEffects.allocated_close_effects',
            'LibraryMachine.original_event_exact', 'LibraryMachine.exit_never_returns',
            'LibraryMachine.no_library_builtin_bypass',
            'LibraryPreservation.store_path_library_projection',
            'LibraryPreservation.execution_library_projection',
            'LibraryPreservation.write_all_library_projection',
            'Fault.fault_return_exact', 'Fault.fault_all_prefixes', 'Fault.fault_defined_prefix',
            'Fault.fault_success_after_waits', 'LibraryWitnesses.source_fault_inputs_inhabited',
            'LibraryWitnesses.equal_fault_source_witness',
            'LibraryWitnesses.unequal_fault_source_witness',
        }.issubset(names))

    def test_all_writer_claims_preserved(self):
        previous = json.loads(gate.LIBRARY_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 227)
        self.assertEqual(len(previous['lean_declarations']), 12)
        gate.validate_preserved_claims(previous, self.claims)
        actual = copy.deepcopy(self.claims)
        record = next(r for r in actual['rocq_declarations']
                      if r['name'] == 'CodecRoundtrip.put64_source_roundtrip')
        record['full_type'] = 'weakened preserved round-trip claim'
        with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
            gate.validate_preserved_claims(previous, actual)

    def test_structures_source_and_memory_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'LocalAccess.assignment_source_edge', 'LocalAccess.function_entry_source_edge',
            'LocalAccess.local_void_return_edge', 'ScalarMemory.scalar_stores_fields',
            'ScalarMemory.copied_scalar_load', 'ResultLayout.result_abi_layout',
            'ResultLayout.result_struct_copy_fields', 'ResultSource.result_construction_source_path',
            'ResultSafety.result_source_execution', 'ResultSafety.result_return_exact',
            'ResultSafety.result_all_prefixes', 'ResultSafety.result_defined_prefix',
            'ResultSafety.result_loss_every_prefix', 'ResultSafety.result_freed_local_has_no_permission',
            'ResultWitnesses.arbitrary_result_source_input',
            'ResultWitnesses.arbitrary_result_source_witness',
        }.issubset(names))

    def test_all_library_claims_preserved(self):
        previous = json.loads(gate.STRUCTURES_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 323)
        self.assertEqual(len(previous['lean_declarations']), 12)
        gate.validate_preserved_claims(previous, self.claims)
        actual = copy.deepcopy(self.claims)
        record = next(r for r in actual['rocq_declarations'] if r['name'] == 'Fault.fault_return_exact')
        record['full_type'] = 'weakened previously checked fault source'
        with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
            gate.validate_preserved_claims(previous, actual)

    def test_callers_and_complete_failure_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'CallContexts.plug_clight_step', 'CallContexts.unplug_clight_step',
            'CallContexts.plug_library_step', 'CallContexts.unplug_library_step',
            'CallContexts.caller_run_decomposition', 'WriteCallers.write_caller_decomposition',
            'FailureMemory.failure_prepare_execution', 'FailureMemory.failure_packet_write_owned',
            'FailureSafety.failure_all_prefixes_defined', 'FailureSafety.failure_never_returns',
            'FailureTrace.failure_reporting_prefix', 'FailureExit.failure_only_exit_125',
            'FailureRuns.failure_successful_exit_exists', 'FailureError.failure_failed_report_exit_exists',
            'FailureError.failure_partial_loss_exists', 'FailureWitnesses.failure_inputs_inhabited',
            'FailureWitnesses.normal_failure_execution', 'FailureWitnesses.dropped_failure_execution',
            'FailureWitnesses.short_failure_execution', 'FailureWitnesses.failed_failure_execution',
            'FailureWitnesses.lost_failure_execution',
        }.issubset(names))

    def test_all_structure_claims_preserved(self):
        previous = json.loads(gate.CALLERS_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 373)
        self.assertEqual(len(previous['lean_declarations']), 12)
        gate.validate_preserved_claims(previous, self.claims)
        actual = copy.deepcopy(self.claims)
        record = next(r for r in actual['rocq_declarations'] if r['name'] == 'ResultSafety.result_return_exact')
        record['full_type'] = 'weakened result construction'
        with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
            gate.validate_preserved_claims(previous, actual)

    def test_complete_decoder_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'DecoderInput.decoder_memories_exist', 'DecoderAssembly.decoder_after_comparison_source',
            'DecoderProgram.decoder_source_connection', 'DecoderProgram.decoder_whole_source_guarantee',
            'DecoderProgram.decoder_all_returns', 'DecoderProgram.decoder_all_prefixes',
            'DecoderProgram.decoder_defined_prefix', 'DecoderProgram.decoder_freed_local_has_no_permission',
            'DecoderRuns.decoder_finite_return_exists', 'DecoderRuns.decoder_arbitrary_waits_and_loss',
            'DecoderRuns.decoder_loss_from_every_live_prefix', 'DecoderAllocation.arbitrary_decoder_source_input',
            'DecoderWitnesses.every_accepted_tag_executes',
            'DecoderWitnesses.early_rejection_executes_without_output_write',
            'DecoderWitnesses.late_rejection_executes_after_output_write',
        }.issubset(names))

    def test_all_caller_claims_preserved(self):
        previous = json.loads(gate.DECODER_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 494)
        self.assertEqual(len(previous['lean_declarations']), 12)
        gate.validate_preserved_claims(previous, self.claims)
        actual = copy.deepcopy(self.claims)
        record = next(r for r in actual['rocq_declarations']
                      if r['name'] == 'FailureSafety.failure_all_prefixes_defined')
        record['full_type'] = 'weakened child-failure execution'
        with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
            gate.validate_preserved_claims(previous, actual)

    def test_unknown_and_forward_project_imports_rejected(self):
        original = gate.module_source
        first = gate.MODULES[0]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'changed.v'
            for imported in ['IncidentalCachedProof', gate.MODULES[-1]]:
                path.write_text(original(first).read_text() + '\nRequire Import ' + imported + '.\n')
                with patch.object(gate, 'module_source',
                                  side_effect=lambda name: path if name == first else original(name)):
                    with self.assertRaisesRegex(ValueError, 'undeclared or unordered'):
                        gate.declaration_names()

    def test_compatibility_closure_cannot_disappear(self):
        self.assertEqual(len(gate.COMPAT_MODULES), 15)
        self.assertTrue(all(gate.module_source(name).parent.name == 'compat'
                            for name in gate.COMPAT_MODULES))
        with patch.object(gate, 'MODULES', [m for m in gate.MODULES if m not in gate.COMPAT_MODULES]):
            with self.assertRaisesRegex(ValueError, 'every authored proof file'):
                gate.declaration_names()

    def test_import_parser_covers_plain_require_and_rejects_bypass(self):
        self.assertEqual(gate.project_imports('Require IO. Require Export Machine.'), ['IO', 'Machine'])
        self.assertEqual(gate.project_imports('From Coq Require Import List.'), [])
        for source in ['Load "cached.v".', 'Require Cached.Hidden.', 'From Cached Require Import Proof.']:
            with self.assertRaises(ValueError):
                gate.project_imports(source)

    def test_complete_sender_and_finish_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'SenderEncoding.sender_encoding_connection', 'SenderReporting.sender_reporting_source',
            'SenderProgram.sender_whole_source_guarantee', 'SenderProgram.sender_all_returns',
            'SenderProgram.sender_all_prefixes', 'SenderProgram.sender_defined_prefix',
            'SenderProgram.sender_returned_locals_have_no_permissions',
            'SenderSuccessfulRuns.sender_complete_report_exists', 'SenderFailedRuns.sender_failed_report_exists',
            'SenderLossRuns.sender_one_byte_loss_exists', 'SenderWitnesses.arbitrary_sender_input',
            'SenderSamples.sender_sample_successful_executions', 'SenderSamples.sender_sample_failed_execution',
            'SenderSamples.sender_sample_partial_loss', 'SenderOutcomes.sender_zero_return_counts',
            'FinishProgram.finish_whole_source_guarantee', 'FinishProgram.finish_all_returns',
            'FinishProgram.finish_all_prefixes', 'FinishProgram.finish_defined_prefix',
            'FinishDetails.finish_returned_exit_status', 'FinishPublication.finish_publication_outcome_exists',
            'FinishWitnesses.allocated_finish_publication_outcomes',
        }.issubset(names))

    def test_decoder_checkpoint_is_preserved(self):
        previous = json.loads(gate.SENDER_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 680)
        self.assertEqual(len(previous['lean_declarations']), 12)
        self.assertEqual(len(gate.DECODER_QUERY_MODULES), 91)
        gate.validate_preserved_claims(previous, self.claims)
        actual = copy.deepcopy(self.claims)
        record = next(r for r in actual['rocq_declarations']
                      if r['name'] == 'DecoderProgram.decoder_all_returns')
        record['full_type'] = 'weakened decoder acceptance and mutation'
        with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
            gate.validate_preserved_claims(previous, actual)

    def test_complete_receiver_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'ReceiverEntry.receiver_entry_prepared', 'ReceiverSelection.receiver_selection_source',
            'ReceiverConstruction.receiver_construction_source', 'ReceiverFree.receiver_free_permissions',
            'ReceiverProgram.receiver_program_guarantee', 'ReceiverProgram.receiver_all_prefixes',
            'ReceiverProgram.receiver_defined_prefix', 'ReceiverOutcomes.receiver_return_trace_exact',
            'ReceiverOutcomes.receiver_read_nine_byte_bound', 'ReceiverAccepted.receiver_actual_setup_bounds',
            'ReceiverRuns.receiver_complete_run', 'ReceiverFaultRuns.receiver_complete_retry_run',
            'ReceiverFaultRuns.receiver_complete_error_run', 'ReceiverLossRuns.receiver_partial_read_loss',
            'ReceiverWitnessInputs.receiver_inputs_inhabited',
            'ReceiverSamples.receiver_setup_actual_run', 'ReceiverSamples.receiver_short_actual_run',
            'ReceiverSamples.receiver_ninth_byte_actual_run', 'ReceiverSamples.receiver_exit_actual_run',
            'ReceiverSamples.receiver_signal_actual_run', 'ReceiverSamples.receiver_stopped_status_actual_run',
            'ReceiverSamples.receiver_arbitrary_signal_domain_actual_run',
        }.issubset(names))

    def test_sender_checkpoint_is_preserved(self):
        previous = json.loads(gate.RECEIVER_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 875)
        self.assertEqual(len(previous['lean_declarations']), 12)
        self.assertEqual(len(gate.SENDER_QUERY_MODULES), 154)
        gate.validate_preserved_claims(previous, self.claims)
        actual = copy.deepcopy(self.claims)
        record = next(r for r in actual['rocq_declarations']
                      if r['name'] == 'SenderProgram.sender_all_returns')
        record['full_type'] = 'weakened sender publication result'
        with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
            gate.validate_preserved_claims(previous, actual)


if __name__ == '__main__':
    unittest.main()
