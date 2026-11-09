#!/usr/bin/env python3
"""Check the shared source and strict proof graph for guest entry and its native callers."""
# §AR-entry.caller: Preserve actual C, ordinary Lean, strict bridge and predecessor source bindings.
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path(__file__).resolve().parent
WORK = ROOT / ".tools/launch/process"
SOURCE = WORK / "source"
NAMESPACE = WORK / "namespace"
FAILURE = WORK / "failure"
REPORTING = WORK / "reporting"
RECORD = ROOT / "assurance/entry-process.json.gz"
MODULES = ("ProcessExpressions", "ProcessControl", "ProcessMachine", "ProcessAuxiliary", "ProcessControlMachine",
           "ProcessContexts", "ProcessCalls", "ProcessPaths", "ProcessTrace", "ProcessLineage", "ProcessStructure",
           "ProcessAllocation", "ProcessReturns", "ProcessWait", "ProcessStatus",
           "ProcessPrimitiveCases", "ProcessRoutine", "ProcessWaitRejection", "ProcessWaitSafety",
           "ProcessAdmissionWait", "ProcessAdmissionEvents",
           "ProcessRelease", "ProcessReleaseSafety", "ProcessReleaseBytes", "ProcessReleaseWitness",
           "ProcessNumeric", "ProcessNumericWitness", "ProcessWriteWitness", "ProcessPlacement", "ProcessCallee", "ProcessAdmissionTail",
           "ProcessAdmissionNumeric", "ProcessAdmissionFormat", "ProcessAdmission", "ProcessAdmissionWitness",
           "ProcessAdmissionNonvacuity", "ProcessClock", "ProcessClockMemory",
           "ProcessClockRun", "ProcessMemory", "ProcessDescriptor", "ProcessScope", "ProcessScopeRecording", "ProcessOwnership", "ProcessAdmissionBridge", "ProcessAdmissionPhysical", "ProcessPhysicalTrace", "ProcessFileTrace",
           "ProcessPhysicalWitness",
           "ProcessGlobalCalls", "ProcessCaller", "ProcessCallerConnection", "ProcessPreparedOrigins", "ProcessOptions", "ProcessSourceOrigin", "ProcessJournal",
           "ProcessSourceRecording", "ProcessSourceTables", "ProcessCgroupRecording", "ProcessSourceWorlds", "ProcessJournalLiveness",
           "ProcessSourceAdmission", "ProcessSourceClose", "ProcessSourceCheckpoint", "ProcessSourceSlices", "ProcessSourceFiles",
           "ProcessCapabilityRecording", "ProcessCapabilityBirth", "ProcessNativeCapabilities",
           "ProcessLaunchWitness", "ProcessLaunchRecordingWitness", "ProcessPreparationWitness", "ProcessParentRecordingWitness", "ProcessChildRecordingWitness", "ProcessChildTickWitness", "ProcessChildOtherWitness", "ProcessWorkerOtherWitness", "ProcessParentCapabilityWitness", "ProcessRecordedComposition", "ProcessEntryWitness", "ProcessEntryComposition", "ProcessEntryObservations", "ProcessQueueWitness", "ProcessPrimitiveWitness", "ProcessPrimitiveData", "ProcessPrimitiveRuns", "ProcessPrimitiveHistory", "ProcessPrimitivePrefix", "ProcessPrimitiveWorlds", "ProcessEntryQueue", "ProcessEntryObservationsRuntime", "ProcessEntryTickBridge", "ProcessEntryAcceptance",
           "ProcessImport", "ProcessConnection", "ProcessNamespace")

INTERFACES = (
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerPhysical_Tick",
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerPhysical_Tick_mk",
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerPhysical_Tick_primitive",
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerPhysical_PrimitiveLabel",
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect",
    "EntryProcess.ProcessNativeCapabilities.PrimitiveDescriptorSample",
    "EntryProcess.ProcessNativeCapabilities.RecordedNativeCapability",
    "EntryProcess.ProcessNativeCapabilities.RecordedMetadataCapability",
    "EntryProcess.ProcessOwnership.LinuxProcessContract",
    "EntryProcess.ProcessOwnership.Build_LinuxProcessContract",
    "EntryProcess.ProcessSourceRecording.SourcePrimitive",
    "EntryProcess.ProcessSourceRecording.SourceProcessView",
    "EntryProcess.ProcessSourceRecording.SourceSnapshot",
    "EntryProcess.ProcessSourceRecording.SourceEventSchedule",
    "EntryProcess.ProcessSourceTables.SourceTableSchedule",
    "EntryProcess.ProcessSourceWorlds.SourceProcessSchedule",
    "EntryProcess.ProcessSourceWorlds.SourceOtherContract",
    "EntryProcess.ProcessSourceWorlds.SourceOtherAuthority",
    "EntryProcess.ProcessJournal.CallerSourceRun",
    "EntryProcess.ProcessJournal.SourceProgramOwner",
    "EntryProcess.ProcessSourceAdmission.SourceOptionsAt",
    "EntryNamespace.NamespaceGrantInputs.ParentPreparedInput",
    "EntryNamespace.NamespaceSourceFork.ActualSourceFork",
    "EntryProcess.ProcessCapabilityBirth.PairCapabilityContract",
    "EntryProcess.ProcessCapabilityBirth.ForkCapabilityContract",
    "EntryProcess.ProcessCapabilityRecording.NativeCapabilityContract",
    "EntryProcess.ProcessCapabilityRecording.MetadataCapabilityContract",
    "EntryProcess.ProcessCapabilityRecording.RecordedCapabilityStep",
    "EntryProcess.ProcessCapabilityRecording.CapabilityHistory",
    "EntryProcess.ProcessCapabilityBirth.CapabilityPreparation",
    "EntryProcess.ProcessCapabilityBirth.SourcePairOccurrence",
    "EntryProcess.ProcessCapabilityBirth.SourceForkOccurrence",
    "EntryProcess.ProcessCapabilityBirth.CapabilityBirth",
    "EntryNamespace.NamespaceAdmissionGuarantee.RecordedForkAdmission",
    "EntryNamespace.NamespaceAdmissionSlices.RecordedAdmissionSource",
    "EntryNamespace.NamespaceApplicationPositions.ApplicationPositions",
    "EntryNamespace.NamespaceCgroupAuthority.PreparedCgroupHandles",
    "EntryNamespace.NamespacePublicReceipt.PublicSourceReceipt",
    "EntryNamespace.NamespaceScopeBridge.public_scope_inputs",
    "EntryNamespace.NamespaceScopeFactory.SourceScopeProduction",
    "EntryNamespace.NamespaceScopeFactory.source_scope_produced",
    "EntryNamespace.NamespaceDescriptorOrigin.SourceDescriptorOrigin",
    "EntryProcess.ProcessImport.LeanCage_Entry_SourceScopeInputs",
    "EntryProcess.ProcessImport.LeanCage_Entry_SourceScopeInputs_mk",
    "EntryProcess.ProcessImport.LeanCage_Entry_SourceScopeProducer",
    "EntryProcess.ProcessLaunchWitness.launch_operation",
    "EntryProcess.ProcessLaunchWitness.LaunchSteps",
    "EntryProcess.ProcessLaunchWitness.LaunchNamespaceRecording",
    "EntryProcess.ProcessLaunchWitness.LaunchFileRecording",
    "EntryProcess.ProcessLaunchRecordingWitness.ProgramRecording",
    "EntryProcess.ProcessLaunchRecordingWitness.OwnedProgramRecording",
    "EntryProcess.ProcessLaunchRecordingWitness.ActualForkCallerRuns",
    "EntryProcess.ProcessLaunchRecordingWitness.actual_fork_caller_runs",
    "EntryProcess.ProcessParentRecordingWitness.ParentRecording",
    "EntryProcess.ProcessEntryComposition.EntryRecordedComposition",
    "EntryProcess.ProcessEntryComposition.EntryIORecording",
    "EntryProcess.ProcessEntryAcceptance.ActualEntrySources",
    "EntryProcess.ProcessEntryAcceptance.Build_ActualEntrySources",
    "EntryProcess.ProcessEntryAcceptance.EntryAcceptance",
    "EntryProcess.ProcessEntryAcceptance.Build_EntryAcceptance",
    "EntryProcess.ProcessEntryAcceptance.entry_prefix_tables",
    "EntryProcess.ProcessEntryAcceptance.entry_tail_tables",
    "EntryProcess.ProcessEntryAcceptance.entry_complete_ticks",
    "EntryProcess.ProcessEntryAcceptance.entry_complete_native",
    "EntryProcess.ProcessEntryAcceptance.entry_complete_metadata",
    "EntryProcess.ProcessEntryAcceptance.entry_complete_external",
    "EntryProcess.ProcessEntryAcceptance.entry_complete_context",
    "EntryProcess.ProcessEntryAcceptance.entry_complete_capabilities",
    "EntryProcess.ProcessEntryAcceptance.entry_exec_offset",
    "EntryProcess.ProcessEntryAcceptance.entry_ordinary_ticks",
    "EntryProcess.ProcessEntryAcceptance.entry_common_labels",
    "EntryProcess.ProcessEntryAcceptance.entry_child_labels",
    "EntryProcess.ProcessPrimitiveHistory.entry_descriptor_observation",
    "EntryProcess.ProcessPrimitiveHistory.entry_primitive_plan",
    "EntryProcess.ProcessPrimitiveHistory.entry_runtime_ticks",
    "EntryProcess.ProcessPrimitiveHistory.entry_runtime_native",
    "EntryProcess.ProcessPrimitiveHistory.entry_runtime_metadata",
    "EntryProcess.ProcessPrimitiveHistory.PrimitiveTableChain",
    "EntryProcess.ProcessPrimitiveRuns.entry_worker_prefix",
    "EntryProcess.ProcessPrimitiveRuns.entry_worker_tail",
    "EntryProcess.ProcessPrimitiveWitness.entry_primitive_descriptor_sample",
    "EntryProcess.ProcessPrimitiveWitness.entry_primitive_native_capability",
    "EntryProcess.ProcessPrimitiveWitness.entry_primitive_metadata_capability",
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerWitness_FDData_Frame",
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerWitness_FDData_tick",
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerWitness_FDData_objects",
    "EntryProcess.ProcessImport.LeanCage_Entry_CallerWitness_FDData_flags",
)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROFILE = load("entry_process_profile", "m4/bridge/profile.py")
FOUNDATIONS = load("entry_process_foundations", "verification/reporting/connection.py")
REPORTING_ADAPTER = load("entry_reporting_adapter", "verification/reporting/entry.py")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


ADAPTED_FAILURE = {name: ROOT / "m4/connection" / (name + ".v")
                   for name in ("FailureSource", "FailureMemory", "FailureBranches")}


def proof_origin(prefix, module):
    if prefix == "EntryReporting":
        return REPORTING_ADAPTER.proof_origin(module)
    if prefix == "EntryFailure" and module in ADAPTED_FAILURE:
        return ADAPTED_FAILURE[module]
    return DIRECTORY / (module + ".v")


def proof_text(prefix, module):
    if prefix == "EntryReporting":
        return REPORTING_ADAPTER.proof_text(module)
    source = proof_origin(prefix, module).read_text()
    if prefix == "EntryFailure" and module in ADAPTED_FAILURE:
        # Exactly the adapter used by failure.py.prepare, with the shared AST.
        source = source.replace("Slice.prog", "EntrySource.prog")
        source = source.replace("FailureSourceDraft", "EntryFailure.FailureSource")
        source = source.replace("FailureMemoryDraft", "EntryFailure.FailureMemory")
        source = source.replace("Import ListNotations.",
                                "From EntryNative Require Import EntrySource.\nImport ListNotations.", 1)
    return source


def proof_modules(extra_roots=()):
    """Compile the maintained, explicitly imported dependency graph in one source environment."""
    roots = [("EntryProcess", name) for name in MODULES]
    roots += [("EntryNamespace", path.stem) for path in sorted(DIRECTORY.glob("Namespace*.v"))]
    roots += [("EntryNative", name) for name in
              ("NativeHandoffImage", "NativeHandoffConnection", "NativeHandoffUseful", "NativeHandoffInputWitness",
               "NativeHandoffTrace", "NativeHandoffNonvacuity")]
    roots += [("EntryReporting", name) for name in REPORTING_ADAPTER.ROOTS]
    roots += list(extra_roots)
    ordered = []
    active = set()
    finished = set()

    def visit(prefix, module):
        if (prefix, module) == ("EntryNative", "EntrySource"):
            return
        node = (prefix, module)
        if node in finished:
            return
        if node in active:
            raise ValueError("cyclic maintained proof dependency: " + ".".join(node))
        active.add(node)
        path = proof_origin(prefix, module)
        if not path.is_file():
            raise ValueError("missing maintained proof dependency: " + ".".join(node))
        for dependency_prefix, imports in re.findall(
                r"From\s+(EntryNative|EntryProcess|EntryNamespace|EntryFailure|EntryReporting)\s+Require\s+Import\s+([^.]*)\.",
                proof_text(prefix, module)):
            for dependency in imports.split():
                visit(dependency_prefix, dependency)
        for imports in re.findall(r"Require\s+Import\s+(.*?)(?:\.(?=\s|$))", proof_text(prefix, module), re.S):
            for qualified in imports.split():
                if re.fullmatch(r"(?:EntryNative|EntryProcess|EntryNamespace|EntryFailure|EntryReporting)\.\w+", qualified):
                    visit(*qualified.split("."))
        active.remove(node)
        finished.add(node)
        ordered.append(node)

    for root in roots:
        visit(*root)
    return ordered


def declaration_names(modules):
    return [prefix + "." + module + "." + name for prefix, module in modules
            for name in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)\b',
                                   proof_text(prefix, module), re.M)]


def native_sources():
    """Follow the production translation unit's maintained quoted includes exactly."""
    pending = [ROOT / "linux/workspace.c"]
    found = set()
    while pending:
        path = pending.pop()
        if path in found:
            continue
        found.add(path)
        for name in re.findall(r'^\s*#\s*include\s*"([^"\n]+)"', path.read_text(), re.M):
            candidates = [path.parent / name, ROOT / "native" / name, ROOT / "linux" / name]
            include = next((candidate.resolve() for candidate in candidates if candidate.is_file()), None)
            if include is None or not include.is_relative_to(ROOT):
                raise ValueError("unresolved or external maintained header: " + name)
            pending.append(include)
    return found


def sources():
    paths = native_sources()
    paths.update(proof_origin(prefix, name) for prefix, name in proof_modules())
    paths.update(DIRECTORY.rglob("*.lean"))
    paths.update((ROOT / "launch").glob("*.lean"))
    paths.update((ROOT / "launch/LeanCageEntry").glob("*.lean"))
    paths.update(ROOT / name for name in (
        "verification/launch/process.py", "verification/launch/failure.py", "verification/launch/NativeArguments.v",
        "linux/process_primitives.c", "linux/entry_handles.c", "linux/entry_decimal.c",
        "launch/lean-toolchain", "launch/lake-manifest.json", "launch/lakefile.lean",
        "m4/bridge/profile.py", "m4/bridge/toolchain-lock.json", "m4/bridge/strict-importer.patch",
        "verification/reporting/connection.py", "verification/reporting/entry.py", "verification/reporting/source.py",
        ".tools/m4/bridge/source/Slice.v", "assurance/m4-frames-evidence.json", "assurance/reporting-source.json.gz",
        "assurance/entry-arguments.json.gz",
        "assurance/reporting-connection.json.gz", "docs/functional-spec/FS-entry.md",
        "docs/architecture/AR-entry.md"))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def flags(checker=False):
    return PROFILE.flags(checker=checker) + [
        "-Q", str(ROOT / ".tools/launch/arguments"), "",
        "-Q", str(WORK), "EntryProcess", "-Q", str(SOURCE), "EntryNative",
        "-Q", str(NAMESPACE), "EntryNamespace",
        "-Q", str(FAILURE), "EntryFailure",
        "-Q", str(REPORTING), "EntryReporting",
        "-Q", str(ROOT / ".tools/reporting/rebase/main/proofs"), "LeanCageMain",
        "-Q", str(ROOT / ".tools/reporting/rebase/main/number"), "LeanCageMainNumber"]


def predecessors():
    accepted = json.loads(gzip.decompress((ROOT / "assurance/reporting-source.json.gz").read_bytes()))
    frontend = ROOT / ".tools/m4/CompCert/clightgen"
    expected = accepted["dependency_sha256"][str(frontend.relative_to(ROOT))]
    if sha(frontend) != expected:
        raise ValueError("source frontend differs from accepted source proof profile")
    inherited = {name: digest for name, digest in accepted["dependency_sha256"].items()
                 if name.startswith(".tools/m4/bridge/") and name.endswith(".vo")}
    inherited.update({".tools/reporting/rebase/" + name: digest
                      for name, digest in accepted["cache_sha256"].items()
                      if name.startswith("main/number/") or name == "main/proofs/Main.vo"})
    for name, digest in inherited.items():
        if sha(ROOT / name) != digest:
            raise ValueError("reused accepted proof artifact differs: " + name)
    arguments = json.loads(gzip.decompress((ROOT / "assurance/entry-arguments.json.gz").read_bytes()))
    for name, digest in arguments["artifacts"].items():
        path = ROOT / ".tools/launch/arguments" / name
        if not path.is_file() or sha(path) != digest:
            raise ValueError("reused argument proof artifact differs: " + str(path.relative_to(ROOT)))
        inherited[str(path.relative_to(ROOT))] = digest
    # These are the actual definitions imported by the reused byte decoder;
    # adding another Lake build root does not change their accepted evidence.
    for name in ("verification/launch/ArgumentsImport.v", "verification/launch/ArgumentConnection.v",
                 "verification/launch/ArgumentValues.v", "verification/launch/WorkerConnection.lean",
                 "launch/LeanCageEntry/Arguments.lean"):
        if sha(ROOT / name) != arguments["source_sha256"][name]:
            raise ValueError("reused argument computation/proof definition differs: " + name)
    return frontend, inherited


def compile_file(path, *, timeout=120):
    try:
        run = PROFILE.run(["rocq", "c", "-q", *flags(), str(path)], cwd=WORK, timeout=timeout)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        path.with_suffix(".log").write_text(output)
        raise
    path.with_suffix(".log").write_text(run.stdout)


def prepare_audit(modules, names):
    """Keep every exact query, partitioning independent pairs/triples across four leaves."""
    imports = ["From " + prefix + " Require Import " + name + "." for prefix, name in modules]
    parts = []
    for part in range(4):
        query = imports + ["Set Printing Depth 10000."]
        for index in range(part, len(names), 4):
            name = names[index]
            query += [f'Redirect "process-type-{index}" Check {name}.',
                      f'Redirect "process-assumptions-{index}" Print Assumptions {name}.']
        query += ["Set Printing All.", "Set Printing Depth 1000000.", "Set Printing Width 1000000."]
        for index in range(part, len(INTERFACES), 4):
            name = INTERFACES[index]
            query += [f'Redirect "process-interface-type-{index}" Check {name}.',
                      f'Redirect "process-interface-definition-{index}" Print {name}.',
                      f'Redirect "process-interface-assumptions-{index}" Print Assumptions {name}.']
        target = WORK / f"ProcessAudit{part}.v"
        target.write_text("\n".join(query) + "\n")
        parts.append(target)
    audit = WORK / "ProcessAudit.v"
    audit.write_text("\n".join("From EntryProcess Require Import " + part.stem + "."
                               for part in parts) + "\n")
    return audit, parts


def build_audit(modules, names):
    audit, parts = prepare_audit(modules, names)
    with ThreadPoolExecutor(max_workers=4) as executor:
        jobs = [executor.submit(compile_file, part, timeout=1800) for part in parts]
        for job in jobs:
            job.result()
    compile_file(audit)
    return audit, parts


def prepare_source(frontend):
    SOURCE.mkdir(parents=True, exist_ok=True)
    frozen = {str(path.relative_to(ROOT)): sha(path) for path in sorted(native_sources())}
    command = [str(frontend), "-normalize", "-fstruct-passing", "-I", "native", "-I", "linux",
               "-o", str((SOURCE / "EntrySource.v").relative_to(ROOT)), "linux/workspace.c"]
    PROFILE.run(command, cwd=ROOT, profile=False, timeout=60)
    compile_file(SOURCE / "EntrySource.v")
    if frozen != {str(path.relative_to(ROOT)): sha(path) for path in sorted(native_sources())}:
        raise ValueError("native inputs changed while preparing source")
    return command


def build():
    before = sources()
    WORK.mkdir(parents=True, exist_ok=True)
    NAMESPACE.mkdir(parents=True, exist_ok=True)
    FAILURE.mkdir(parents=True, exist_ok=True)
    REPORTING.mkdir(parents=True, exist_ok=True)
    PROFILE.verify_tools()
    frontend, inherited = predecessors()
    command = prepare_source(frontend)
    reporting_mapping = REPORTING_ADAPTER.validate_source(SOURCE / "EntrySource.v")
    subprocess.run(["lake", "-d", "launch", "build", "CallerPhysical", "MetadataWitness"], cwd=ROOT, check=True)
    export = WORK / "process-control.ndjson"
    with export.open("w") as out:
        subprocess.run(["lake", "-d", "launch", "env",
                        str(PROFILE.WORK / "lean4export/.lake/build/bin/lean4export"),
                        "MetadataWitness", "--", "LeanCage.Entry.NonSubstitutingRequest",
                        "LeanCage.Entry.ReleaseAccepted", "LeanCage.Entry.CallerRequestsAllowed",
                        "LeanCage.Entry.CallerLineageAllowed", "LeanCage.Entry.TracerOptionsAllowed",
                        "LeanCage.Entry.SourceSupervisor", "LeanCage.Entry.SourceSupervisorUse",
                        "LeanCage.Entry.CallerLabelsAllowed",
                        "LeanCage.Entry.CallerPhysical.Tick", "LeanCage.Entry.CallerPhysical.Journal",
                        "LeanCage.Entry.CallerPhysical.At", "LeanCage.Entry.CallerPhysical.born",
                        "LeanCage.Entry.CallerPhysical.taskKey", "LeanCage.Entry.CallerPhysical.Tick.source",
                        "LeanCage.Entry.CallerPhysical.Tick.primitive",
                        "LeanCage.Entry.CallerPhysical.PrimitiveLabel.family",
                        "LeanCage.Entry.CallerPhysical.PrimitiveLabel.code",
                        "LeanCage.Entry.CallerPhysical.PrimitiveLabel.kernel",
                        "LeanCage.Entry.CallerPhysical.NoPlacementFrom",
                        "LeanCage.Entry.CallerPhysical.TickBinding",
                        "LeanCage.Entry.CallerPhysical.NoPlacementBefore",
                        "LeanCage.Entry.CallerPhysical.PlacementRecording",
                        "LeanCage.Entry.CallerPhysical.CgroupAbsent",
                        "LeanCage.Entry.CallerPhysical.WriteOutsideCgroup",
                        "LeanCage.Entry.CallerPhysical.WriteSourceOrExternal",
                        "LeanCage.Entry.CallerPhysical.ParentLiveBefore",
                        "LeanCage.Entry.CallerPhysical.LocalEntryCode",
                        "LeanCage.Entry.CallerWitness.SupervisorSlice",
                        "LeanCage.Entry.CallerWitness.DescriptorObjectsFrom", "LeanCage.Entry.CallerWitness.DescriptorEffect", "LeanCage.Entry.CallerWitness.FlagsOutside",
                        "LeanCage.Entry.CallerWitness.DescriptorCapabilityEffect",
                        "LeanCage.Entry.SourceScopeInputs", "LeanCage.Entry.SourceScopeProducer",
                        "LeanCage.Entry.CallerWitness.FDData.Frame",
                        "LeanCage.Entry.CallerWitness.FDData.Frame.code",
                        "LeanCage.Entry.CallerWitness.FDData.Frame.before",
                        "LeanCage.Entry.CallerWitness.FDData.Frame.after",
                        "LeanCage.Entry.CallerWitness.FDData.Frame.read",
                        "LeanCage.Entry.CallerWitness.FDData.objects", "LeanCage.Entry.CallerWitness.FDData.flags",
                        "LeanCage.Entry.CallerWitness.FDData.tick", "LeanCage.Entry.CallerWitness.FDData.ticks",
                        "LeanCage.Entry.CallerWitness.FDData.signalFrames", "LeanCage.Entry.CallerWitness.FDData.traceFrames",
                        "LeanCage.Entry.CallerWitness.FDData.inspectionFrames", "LeanCage.Entry.CallerWitness.FDData.tailFrames",
                        "LeanCage.Entry.CallerWitness.FDData.pack", "LeanCage.Entry.CallerWitness.FDData.snapshots",
                        "LeanCage.Entry.CallerWitness.FDData.execFrame",
                        "LeanCage.Entry.CallerWitness.usefulWorkerPrefix", "LeanCage.Entry.CallerWitness.usefulWorkerTail",
                        "LeanCage.Entry.CallerWitness.usefulEntryTicks"],
                       cwd=ROOT, stdout=out, check=True)
    FOUNDATIONS.export_records(export)
    witness_export = WORK / "caller-witness-code.ndjson"
    with witness_export.open("w") as out:
        subprocess.run(["lake", "-d", "launch", "env",
                        str(PROFILE.WORK / "lean4export/.lake/build/bin/lean4export"),
                        "MetadataWitness", "--", "LeanCage.Entry.CallerWitness.objects",
                        "LeanCage.Entry.CallerWitness.cloexec", "LeanCage.Entry.CallerWitness.argumentBytes",
                        "LeanCage.Entry.CallerWitness.ordinaryRead", "LeanCage.Entry.CallerWitness.ordinaryWrite"],
                       cwd=ROOT, stdout=out, check=True)
    FOUNDATIONS.export_records(witness_export)
    modules = proof_modules()
    directories = {"EntryProcess": WORK, "EntryNative": SOURCE, "EntryNamespace": NAMESPACE,
                   "EntryFailure": FAILURE, "EntryReporting": REPORTING}
    for prefix, name in modules:
        target = directories[prefix] / (name + ".v")
        target.write_text(proof_text(prefix, name))
        compile_file(target)
    names = declaration_names(modules)
    audit, audit_parts = build_audit(modules, names)
    declarations = []
    for index, name in enumerate(names):
        assumptions = (WORK / f"process-assumptions-{index}.out").read_text().strip()
        axioms, uip = FOUNDATIONS.foundations(assumptions)
        declarations.append(dict(name=name,
                                 type=(WORK / f"process-type-{index}.out").read_text().strip(),
                                 assumptions=assumptions, assumption_names=axioms, definitional_uip=uip))
    interfaces = []
    for index, name in enumerate(INTERFACES):
        assumptions = (WORK / f"process-interface-assumptions-{index}.out").read_text().strip()
        axioms, uip = FOUNDATIONS.foundations(assumptions)
        interfaces.append(dict(name=name,
                               type=(WORK / f"process-interface-type-{index}.out").read_text().strip(),
                               definition=(WORK / f"process-interface-definition-{index}.out").read_text().strip(),
                               assumptions=assumptions, assumption_names=axioms, definitional_uip=uip))
    checked = PROFILE.run(["rocq", "check", "-silent", *flags(checker=True),
                           *[prefix + "." + name for prefix, name in modules]], cwd=WORK, timeout=300)
    (WORK / "kernel-check.log").write_text(checked.stdout)
    if before != sources():
        raise ValueError("process proof inputs changed during checking")
    files = [SOURCE / "EntrySource.v", SOURCE / "EntrySource.vo", export, witness_export]
    files += [part.with_suffix(suffix) for part in [*audit_parts, audit] for suffix in (".v", ".vo")]
    files += [directories[prefix] / (name + suffix) for prefix, name in modules for suffix in (".v", ".vo")]
    artifacts = {str(path.relative_to(WORK)): sha(path) for path in files}
    record = dict(schema="leancage-entry-process-source-v1", complete_admission=False,
                  scope="Prepared-root actual source fork, private channel, child handoff and owned "
                        "placement/options/resume source producer, connected to the ordinary Lean "
                        "SourceScopeProducer through the same runtime, capability, queue and journal "
                        "history. This source component composes with the worker body and public "
                        "consumer in entry-claims.json; policy preparation, later lifetime and "
                        "public observation producers retain their assigned contracts.",
                  source_sha256=before, frontend_sha256=sha(frontend), frontend_command=command,
                  reporting_source_mapping=reporting_mapping,
                  inherited_cache_sha256=inherited, declarations=declarations, interfaces=interfaces, artifacts=artifacts,
                  export_fingerprints=FOUNDATIONS.export_fingerprints(export),
                  witness_export_fingerprints=FOUNDATIONS.export_fingerprints(witness_export),
                  toolchain=PROFILE.lock())
    (WORK / "proposal.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--propose", action="store_true")
    parser.add_argument("--prepare-source", action="store_true")
    args = parser.parse_args()
    PROFILE.verify_tools()
    frontend, _ = predecessors()
    if args.prepare_source:
        prepare_source(frontend)
        print("Actual production source prepared; no admission acceptance claim is made.")
        return
    expected = None if args.propose else json.loads(gzip.decompress(RECORD.read_bytes()))
    if expected is not None and expected["source_sha256"] != sources():
        raise ValueError("reviewed process source inputs differ")
    if expected is not None and all((WORK / name).is_file() and sha(WORK / name) == digest
                                    for name, digest in expected["artifacts"].items()):
        print("Source process components checked: matching kernel-checked artifacts reused.")
    elif args.propose:
        build()
        print("Process source proposal written: " + str(WORK / "proposal.json"))
    elif build() != expected:
        raise ValueError("process source/type/foundation replay differs from reviewed evidence")
    else:
        print("Source process component replay passed; full admission composition is checked separately.")


if __name__ == "__main__":
    main()
