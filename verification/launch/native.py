#!/usr/bin/env python3
"""Check the maintained native entry graph and its exact ordinary-Lean value interface."""
# §AR-entry.caller.receipt: One canonical graph serves the actual source and public proof consumers.
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path(__file__).resolve().parent
REQUIRED = {
    "EntryNative.NativeHandoffImage.handoff_guest_image_current",
    "EntryNative.NativeHandoffTrace.handoff_guest_image_flags",
    "EntryNative.NativeHandoffConnection.handoff_snapshot_worker_connection",
    "EntryNative.NativeHandoffConnection.handoff_guest_worker_values",
    "EntryNative.NativeHandoffNonvacuity.handoff_source_useful_image",
    "EntryFailure.FailureMachine.current_entry_failure_caller_prefix",
    "EntryProcess.ProcessAdmissionPhysical.actual_admission_establishes_scope",
    "EntryProcess.ProcessReleaseSafety.release_transport_requires_checked_resume",
    "EntryProcess.ProcessReleaseBytes.release_actual_wire_bytes",
    "EntryProcess.ProcessClockRun.clock_all_source_returns",
    "EntryProcess.ProcessCallerConnection.caller_source_history_ordinary_Lean",
    "EntryNamespace.NamespaceProcessProducer.actual_parent_source_produces_unreaped",
    "EntryNamespace.NamespaceSourceFork.actual_source_fork_occurrence",
    "EntryNamespace.NamespaceForkParent.actual_positive_fork_parent_return",
    "EntryNamespace.NamespaceParentEntry.actual_parent_creation_reaches_setup",
    "EntryNamespace.NamespaceGrantCaller.actual_fork_parent_private_grant",
    "EntryNamespace.NamespaceGuestDescriptor.actual_namespace_guest_caller_write_descriptors",
    "EntryNamespace.NamespaceParentInput.namespace_actual_useful_parent",
    "EntryProcess.ProcessJournal.actual_source_produces_journal",
    "EntryProcess.ProcessSourceRecording.source_event_schedule_covers",
    "EntryProcess.ProcessSourceTables.source_table_close_later_absence",
    "EntryProcess.ProcessCgroupRecording.actual_placement_produces_ordinary",
    "EntryProcess.ProcessCgroupRecording.actual_cgroup_absence_produces_ordinary",
    "EntryProcess.ProcessPhysicalWitness.actual_source_and_physical_admission_useful",
    "EntryProcess.ProcessSourceCheckpoint.actual_source_admission_close_checkpoint",
    "EntryNamespace.NamespaceForkGrant.actual_same_fork_source_write_authorized",
    "EntryNamespace.NamespacePostForkClosure.actual_fork_return_no_capability_export",
    "EntryNamespace.NamespaceLaunchWorldWitness.namespace_actual_local_grant_owned",
    "EntryNamespace.NamespaceChildWorldWitness.namespace_actual_parent_and_child_entry",
    "EntryNamespace.NamespaceAdmissionGuarantee.actual_recorded_fork_admission",
    "EntryNamespace.NamespaceWitnessConnection.namespace_actual_source_ordinary_entry",
    "EntryProcess.ProcessSourceAdmission.source_process_admission_options_checkpoint",
    "EntryNamespace.NamespacePreparedFork.actual_prepared_source_common_fork_owned",
    "EntryNamespace.NamespacePreparedAdmission.namespace_actual_parent_storage",
    "EntryNamespace.NamespacePreparedAdmission.actual_prepared_recorded_fork_admission",
    "EntryNamespace.NamespacePreparedAdmission.actual_prepared_recorded_fork_from_raw",
    "EntryNamespace.NamespacePreparedCgroupFrame.actual_prepared_parent_cgroup_load",
    "EntryNamespace.NamespaceAdmissionSlices.recorded_grant_actual_admission_source",
    "EntryNamespace.NamespaceApplicationPositions.recorded_fork_application_positions",
    "EntryNamespace.NamespaceRecordedLiveness.recorded_resume_parent_alive_strict",
    "EntryNamespace.NamespaceCgroupAuthority.actual_parent_closed_cgroup_absent",
    "EntryNamespace.NamespaceCgroupAuthority.actual_parent_closed_cgroup_write_outside",
    "EntryNamespace.NamespaceChildCgroup.actual_same_fork_child_write_outside_cgroup",
    "EntryNamespace.NamespacePublicReceipt.recorded_fork_public_source_receipt",
    "EntryNamespace.NamespaceScopeBridge.recorded_source_parent_live",
    "EntryNamespace.NamespaceScopeBridge.recorded_fork_public_source_from_journal",
    "EntryNamespace.NamespaceSourceCgroup.actual_source_writer_cgroup_classification",
    "EntryNamespace.NamespaceScopeFactory.actual_fork_source_scope_producer",
    "EntryNamespace.NamespaceScopeFactory.actual_prepared_source_scope_from_raw",
    "EntryNamespace.NamespaceDescriptorOrigin.actual_useful_descriptor_origin",
    "EntryProcess.ProcessJournalLiveness.journal_parent_live_before_checkpoint",
    "EntryProcess.ProcessSourceSlices.source_process_schedule_cut",
    "EntryProcess.ProcessSourceFiles.source_process_schedule_files",
    "EntryProcess.ProcessCapabilityBirth.capability_birth_foreign_absence",
    "EntryProcess.ProcessEntryWitness.actual_useful_source_recording_chain",
    "EntryProcess.ProcessEntryComposition.entry_actual_recorded_composition",
    "EntryProcess.ProcessEntryComposition.entry_actual_io_recording",
    "EntryProcess.ProcessPrimitiveWitness.entry_primitive_native_capability",
    "EntryProcess.ProcessPrimitiveWitness.entry_primitive_metadata_capability",
    "EntryProcess.ProcessPrimitivePrefix.entry_worker_prefix_capabilities",
    "EntryProcess.ProcessPrimitiveHistory.entry_worker_tail_capabilities",
    "EntryProcess.ProcessEntryQueue.actual_prepared_recorded_entry_queue",
    "EntryProcess.ProcessEntryTickBridge.entry_runtime_ticks_ordinary",
    "EntryProcess.ProcessEntryAcceptance.actual_entry_acceptance",
    "EntryProcess.ProcessEntryAcceptance.entry_complete_scope",
}

# Types and bodies are recorded by process.py, not reconstructed from these names.
REQUIRED_INTERFACES = {
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerPhysical_Tick_primitive",
    "EntryNamespace.NamespaceGrantInputs.ParentPreparedInput",
    "EntryNamespace.NamespaceSourceFork.ActualSourceFork",
    "EntryNamespace.NamespaceAdmissionGuarantee.RecordedForkAdmission",
    "EntryNamespace.NamespaceAdmissionSlices.RecordedAdmissionSource",
    "EntryNamespace.NamespaceApplicationPositions.ApplicationPositions",
    "EntryNamespace.NamespacePublicReceipt.PublicSourceReceipt",
    "EntryNamespace.NamespaceCgroupAuthority.PreparedCgroupHandles",
    "EntryNamespace.NamespaceScopeBridge.public_scope_inputs",
    "EntryNamespace.NamespaceScopeFactory.SourceScopeProduction",
    "EntryNamespace.NamespaceScopeFactory.source_scope_produced",
    "EntryNamespace.NamespaceDescriptorOrigin.SourceDescriptorOrigin",
    "EntryProcess.ProcessEntryAcceptance.EntryAcceptance",
    "EntryProcess.ProcessEntryAcceptance.Build_EntryAcceptance",
    "EntryProcess.ProcessEntryAcceptance.ActualEntrySources",
    "EntryProcess.ProcessEntryAcceptance.Build_ActualEntrySources",
    "EntryProcess.ProcessImport.LeanCage_Entry_SourceScopeInputs",
    "EntryProcess.ProcessImport.LeanCage_Entry_SourceScopeInputs_mk",
    "EntryProcess.ProcessImport.LeanCage_Entry_SourceScopeProducer",
}


def source_driver():
    spec = importlib.util.spec_from_file_location("entry_shared_source_driver", DIRECTORY / "process.py")
    driver = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(driver)
    return driver


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--propose", action="store_true",
                        help="write the shared source/type/assumption proposal; never accept expectations")
    args = parser.parse_args()
    driver = source_driver()
    subprocess.run([sys.executable, str(DIRECTORY / "arguments.py")], cwd=ROOT, check=True)
    command = [sys.executable, str(DIRECTORY / "process.py")]
    if args.propose:
        command.append("--propose")
    subprocess.run(command, cwd=ROOT, check=True)
    record = (json.loads((driver.WORK / "proposal.json").read_text()) if args.propose else
              json.loads(gzip.decompress(driver.RECORD.read_bytes())))
    names = {declaration["name"] for declaration in record["declarations"]}
    missing = REQUIRED - names
    if missing:
        raise ValueError("entry source graph omits required current interfaces: " + ", ".join(sorted(missing)))
    interfaces = {interface["name"] for interface in record["interfaces"]}
    missing_interfaces = REQUIRED_INTERFACES - interfaces
    if missing_interfaces:
        raise ValueError("entry source graph omits reviewed interface types/bodies: " +
                         ", ".join(sorted(missing_interfaces)))
    if record["frontend_command"][-1] != "linux/workspace.c":
        raise ValueError("entry proof graph did not translate the maintained production source")
    print("Current native entry/value/caller interfaces " +
          ("proposed for statement review." if args.propose else "checked against the reviewed shared source graph."))


if __name__ == "__main__":
    main()
