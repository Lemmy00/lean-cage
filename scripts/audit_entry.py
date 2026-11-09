#!/usr/bin/env python3
"""Audit the actual executable entry definitions, theorem types and assumptions."""
# §AR-entry.acceptance: Freeze exact statements and assumptions.
# Proposals never replace reviewed expectations.
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "launch"
WORK = ROOT / ".tools/launch"
MANIFEST = ROOT / "assurance/entry-claims.json"
BODY_RECORD = ROOT / "assurance/entry-body-claims.json.gz"
BODY_SHA256 = "4da0f8961e86a94d750eb1024049740f22023ca92baf932b0364cd958ac1ffb7"
LOGICAL = {"propext", "Classical.choice", "Quot.sound"}
SCOPE = ("Guest admission from the maintained prepared-root launch statement through the "
         "actual local fork, native handoff and fresh Lean worker, under the enumerated "
         "Linux/runtime contracts; policy/workspace preparation, lifetime and public "
         "observation producers retain their separately assigned application obligations.")
INPUT_PRODUCERS = {
    "AR-application-verification.authority": [
        "Actual namespace_init preparation and error guards reach namespace_tail 9 with canonical locals",
        "Caller policy bytes bind the leased UID, root, argv and immutable argument storage",
        "Ordinary input/capture/cgroup/report objects have their observed identities and descriptor modes",
        "Owned VM ancestors' actual source issues no debugger or private-descriptor acquisition operation",
        "The named cgroup and namespace objects denote the requested run",
    ],
    "AR-application-verification.lifetime": [
        "Owned supervision and cancellation establish later exit, population and cleanup observations",
    ],
    "AR-application-verification.composition": [
        "Public fields and artifacts consume authenticated observations of this request",
    ],
}
APPLICATION_INTERFACE = {
    "source_factory": "EntryNamespace.NamespaceScopeFactory.actual_prepared_source_scope_from_raw",
    "source_receipt": "EntryNamespace.NamespaceScopeFactory.SourceScopeProduction",
    "source_projection": "EntryNamespace.NamespaceScopeFactory.source_scope_produced",
    "strict_predicate": "EntryProcess.ProcessImport.LeanCage_Entry_SourceScopeProducer",
    "consumer": "LeanCage.Entry.production_source_workspace",
    "useful_consumer": "LeanCage.Entry.CallerWitness.useful_public_source_workspace",
    "acceptance_factory": "EntryProcess.ProcessEntryAcceptance.actual_entry_acceptance",
    "acceptance_receipt": "EntryProcess.ProcessEntryAcceptance.EntryAcceptance",
    "tick_bridge": "EntryProcess.ProcessEntryTickBridge.entry_runtime_ticks_ordinary",
}

# These are inspected in their real import environment as well as the complete
# theorem inventory. A wrapper with a familiar name does not bind its callees.
DEFINITIONS = (
    "LeanCage.Entry.Worker.run", "LeanCage.Entry.Worker.startup",
    "LeanCage.Entry.Worker.inspect", "LeanCage.Entry.Worker.parse",
    "LeanCage.Entry.Worker.enabled", "LeanCage.Entry.Startup.interpret",
    "LeanCage.Entry.Startup.admission", "LeanCage.Entry.admission",
    "LeanCage.Entry.Script.interpret", "LeanCage.Entry.execute",
    "LeanCage.Entry.runCommands", "LeanCage.Entry.finishSetup",
    "LeanCage.Entry.setup", "LeanCage.Entry.handshake",
    "LeanCage.Entry.terminate", "LeanCage.Entry.execRequest",
    "LeanCage.Entry.Expected.accepts", "LeanCage.Entry.Linux.call",
    "LeanCage.Entry.Linux.primitive", "LeanCage.Entry.Op.code",
    "LeanCageM3.Metadata.bounded", "LeanCageM3.Metadata.loop",
    "LeanCageM3.Metadata.finish", "LeanCageM3.Metadata.inspect",
    "LeanCageM3.Metadata.Program.interpret", "LeanCageM3.Metadata.call",
    "LeanCageM3.Metadata.primitive", "LeanCage.Entry.Restricted",
    "LeanCage.Entry.ImageRestricted", "LeanCage.Entry.PreparedSources", "LeanCage.Entry.ImageStdio",
    "LeanCage.Entry.PhysicalHandoff.loadedHandles",
    "LeanCage.Entry.ArgumentMeaning.nativeValues", "LeanCage.Entry.CallerNative",
    "LeanCage.Entry.CallerMetadata", "LeanCage.Entry.CallerRequestsAllowed",
    "LeanCage.Entry.CallerLineageAllowed", "LeanCage.Entry.TracerOptionsAllowed",
    "LeanCage.Entry.TracerControl.nonSubstituting",
    "LeanCage.Entry.CallerPhysical.SourceUse", "LeanCage.Entry.CallerPhysical.Good",
    "LeanCage.Entry.CallerPhysical.ContextSafe",
    "LeanCage.Entry.CallerPhysical.control", "LeanCage.Entry.CallerPhysical.born",
    "LeanCage.Entry.CallerPhysical.TickAt", "LeanCage.Entry.CallerPhysical.At",
    "LeanCage.Entry.CallerPhysical.NativeTable", "LeanCage.Entry.CallerPhysical.TickBinding",
    "LeanCage.Entry.CallerPhysical.NoPlacementFrom", "LeanCage.Entry.CallerPhysical.NoPlacementBefore",
    "LeanCage.Entry.CallerPhysical.PlacementRecording", "LeanCage.Entry.CallerPhysical.CgroupAbsent",
    "LeanCage.Entry.CallerPhysical.WriteOutsideCgroup",
    "LeanCage.Entry.CallerPhysical.WriteSourceOrExternal",
    "LeanCage.Entry.CallerPhysical.ParentLiveBefore",
    "LeanCage.Entry.CallerPhysical.LocalEntryCode",
    "LeanCage.Entry.SourceScopeProducer",
    "LeanCage.Entry.CallerPhysical.SupervisorAt", "LeanCage.Entry.CallerPhysical.SocketQuietAt",
    "LeanCage.Entry.CallerPhysical.StackObservation",
    "LeanCage.Entry.CallerPhysical.Point.advance", "main",
    "LeanCage.Entry.CallerWitness.usefulLineage", "LeanCage.Entry.CallerWitness.usefulSourceLabels",
    "LeanCage.Entry.CallerWitness.usefulEntryTicks", "LeanCage.Entry.CallerWitness.usefulWorkerPrefix",
    "LeanCage.Entry.CallerWitness.usefulWorkerTail", "LeanCage.Entry.CallerWitness.runtime",
    "LeanCage.Entry.CallerWitness.metadataRuntime", "LeanCage.Entry.CallerWitness.recordedImage",
    "LeanCage.Entry.CallerWitness.recordedNative", "LeanCage.Entry.CallerWitness.recordedMetadata",
    "LeanCage.Entry.CallerWitness.primitiveNative", "LeanCage.Entry.CallerWitness.primitiveMetadata",
    "LeanCage.Entry.CallerWitness.FDData.tick", "LeanCage.Entry.CallerWitness.FDData.ticks",
    "LeanCage.Entry.CallerWitness.FDData.sample", "LeanCage.Entry.CallerWitness.FDData.Supported",
    "LeanCage.Entry.CallerWitness.FDData.lookup", "LeanCage.Entry.CallerWitness.FDData.pack",
    "LeanCage.Entry.CallerWitness.FDData.atD", "LeanCage.Entry.CallerWitness.FDData.execFrame",
)

# A constructor's full type exposes every runtime law and recording obligation.
# These have no executable definition body; do not confuse them with the worker.
CONTRACT_CONSTRUCTORS = (
    "LeanCage.Entry.PrimitiveContract.mk", "LeanCage.Entry.OriginContract.mk",
    "LeanCage.Entry.ExecContract.mk", "LeanCage.Entry.CallerLineageContract.mk",
    "LeanCage.Entry.MetadataFrame.PrimitiveContract.mk", "LeanCage.Entry.MetadataOriginContract.mk",
    "LeanCage.Entry.CallerPhysical.SupervisorContract.mk",
    "LeanCage.Entry.CallerPhysical.NativeContract.mk",
    "LeanCage.Entry.CallerPhysical.MetadataContract.mk",
    "LeanCage.Entry.CallerPhysical.SupervisorRecording.mk",
    "LeanCage.Entry.CallerPhysical.NativeRecording.mk",
    "LeanCage.Entry.CallerPhysical.NativeSocket.mk",
    "LeanCage.Entry.CallerPhysical.MetadataRecording.mk",
    "LeanCage.Entry.CallerPhysical.ImageContract.mk",
    "LeanCage.Entry.CallerPhysical.Tick.mk",
    "LeanCage.Entry.CallerPhysical.PrimitiveLabel.mk",
    "LeanCage.Entry.SourceScopeInputs.mk",
)

BODY_QUERY = r'''
elab "#audit_body " name:ident : command => do
  let info ← getConstInfo name.getId
  let some expression := info.value? | throwError "Missing definition body: {name.getId}"
  let body ← liftTermElabM <| withOptions
    (fun options => options.setBool `pp.fullNames true |>.setBool `pp.universes true) do
      return (← Meta.ppExpr expression).pretty
  logInfo m!"LEANCAGE_BODY {(Json.mkObj [("name", toJson name.getId.toString),
    ("body", toJson body)]).compress}"
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def predecessor():
    raw = gzip.decompress(BODY_RECORD.read_bytes())
    if hashlib.sha256(raw).hexdigest() != BODY_SHA256:
        raise ValueError("preserved original entry-body statement record differs")
    return dict(path=str(BODY_RECORD.relative_to(ROOT)), sha256=sha(BODY_RECORD),
                revision="be541b134bd339fb053f07c491e04ec995d564f8", original_sha256=BODY_SHA256)


def modules():
    proof_root = ROOT / "verification/launch"
    result = {str(p.relative_to(proof_root).with_suffix("")).replace("/", "."): p
              for p in proof_root.rglob("*.lean") if ".lake" not in p.parts}
    result.update({str(p.relative_to(PACKAGE).with_suffix("")).replace("/", "."): p
                   for p in PACKAGE.rglob("*.lean") if ".lake" not in p.parts and p.name != "lakefile.lean"})
    return dict(sorted(result.items()))


def sources():
    paths = list(modules().values())
    paths += sorted((ROOT / "verification/launch").glob("*.v"))
    paths += [ROOT / name for name in (
        "scripts/audit_entry.py", "scripts/check_entry.sh", "scripts/m3_axiom_query.lean", "launch/lakefile.lean",
        "verification/launch/native.py", "verification/launch/process.py",
        "verification/launch/arguments.py", "verification/launch/failure.py",
        "verification/reporting/entry.py",
        "launch/lake-manifest.json", "launch/lean-toolchain", "linux/entry_primitives.c",
        "linux/entry_handoff.h", "linux/entry_decimal.c", "linux/entry_decimal.h",
        "linux/entry_handles.c", "linux/process_primitives.c", "linux/process_primitives.h",
        "linux/metadata_primitives.c", "docs/functional-spec/FS-entry.md", "docs/architecture/AR-entry.md",
        "docs/functional-spec/FS-metadata.md", "docs/architecture/AR-metadata.md",
        "docs/decisions/architectural/DA-metadata-handles.md",
        "docs/functional-spec/FS-assurance.md", "docs/functional-spec/FS-linux-product.md",
        "docs/architecture/AR-application-verification.md",
        "docs/decisions/architectural/DA-entry-worker.md", "docs/requirements/REQ-proof-integrity.md",
        "assurance/filter-decoder.json", "assurance/m2-claims.json", "assurance/m3-claims.json",
        "assurance/entry-arguments.json.gz", "assurance/entry-process.json.gz",
        "assurance/entry-body-claims.json.gz")]
    spec = importlib.util.spec_from_file_location("entry_audit_source_inputs", ROOT / "verification/launch/process.py")
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    paths += sorted(native.native_sources())
    # Bind the actual transitive executable definitions, rather than only the worker's own sources.
    for directory in ("LeanCage", "lifecycle", "workspace"):
        paths += [p for p in (ROOT / directory).rglob("*.lean") if ".lake" not in p.parts]
    paths += [ROOT / name for name in ("LeanCage.lean", "lean-toolchain", "lakefile.lean", "lake-manifest.json")]
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))}


def query():
    shared = (ROOT / "scripts/m3_axiom_query.lean").read_text()
    declarations = "\nopen Lean Elab Command\n" + shared.split("open Lean Elab Command", 1)[1]
    # The executing definitions are part of the audit even when they are not theorems.
    rows, bodies = [], {}
    inherited = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                        cwd=PACKAGE, text=True).strip()
    # Dependencies also define a module named Main. Resolve this package's
    # compiled modules first, after Lake has set the dependency environment.
    checked_path = str(PACKAGE / ".lake/build/lib/lean") + ":" + inherited
    # Each executable owns a separate top-level main; inspect its actual import environment.
    for context, names, inspected in (
            ("production", [name for name in modules() if name != "EntryTestMain"], DEFINITIONS),
            ("test", ["EntryTestMain"], ["main"])):
        source = "import Lean\n" + "".join(f"import {name}\n" for name in names) + declarations + BODY_QUERY
        source += "".join(f"\n#audit_module {name}" for name in names)
        source += "".join(f"\n#audit_decl {name}\n#audit_body {name}" for name in inspected) + "\n"
        if context == "production":
            source += "".join(f"\n#audit_decl {name}" for name in CONTRACT_CONSTRUCTORS) + "\n"
        with tempfile.TemporaryDirectory(prefix="audit-", dir=WORK) as temporary:
            path = Path(temporary) / "Query.lean"
            path.write_text(source)
            run = subprocess.run(["lake", "env", "env", "LEAN_PATH=" + checked_path,
                                  "lean", str(path)], cwd=PACKAGE,
                                 capture_output=True, text=True, timeout=180)
            if run.returncode:
                raise ValueError("entry declaration query failed:\n" + run.stdout + run.stderr)
        for line in run.stdout.splitlines():
            if "LEANCAGE_AUDIT " in line:
                row = json.loads(line.split("LEANCAGE_AUDIT ", 1)[1])
                if "name" in row:
                    row["environment"] = context
                rows.append(row)
            if "LEANCAGE_BODY " in line:
                body = json.loads(line.split("LEANCAGE_BODY ", 1)[1])
                key = context, body["name"]
                if key in bodies:
                    raise ValueError("duplicate executable-definition body: " + body["name"])
                bodies[key] = body["body"]
    inventory = {row["module"]: sorted(row["declarations"]) for row in rows if "module" in row}
    declarations = sorted((row for row in rows if "name" in row), key=lambda row: (row["environment"], row["name"]))
    if set(inventory) != set(modules()) or len({(r["environment"], r["name"]) for r in declarations}) != len(declarations):
        raise ValueError("entry theorem/module inventory differs or contains duplicates")
    if {name for names in inventory.values() for name in names} != {
            r["name"] for r in declarations if r["is_theorem"]}:
        raise ValueError("entry theorem inventory is incomplete")
    for row in declarations:
        if not row["is_theorem"]:
            if row["name"] in CONTRACT_CONSTRUCTORS:
                row["kind"] = "contract_constructor"
            else:
                row["body"] = bodies.pop((row["environment"], row["name"]))
        row["axioms"] = sorted(row["axioms"])
        if set(row["axioms"]) - LOGICAL:
            raise ValueError("forbidden transitive axiom: " + row["name"])
    if bodies:
        raise ValueError("unmatched executable-definition body")
    return inventory, declarations


def application_interface(declarations):
    """Bind the final source producer, checked pure bridge and actual worker consumer."""
    spec = importlib.util.spec_from_file_location("entry_consumer_source", ROOT / "verification/launch/process.py")
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    record_path = ROOT / "assurance/entry-process.json.gz"
    record = json.loads(gzip.decompress(record_path.read_bytes()))
    if record["source_sha256"] != source.sources():
        raise ValueError("entry consumer requires matching reviewed source-producer inputs")
    indexed = {row["name"]: row for row in record["declarations"] + record["interfaces"]}
    proofs = {row["name"]: row for row in declarations if row["environment"] == "production"}
    consumer = proofs.get(APPLICATION_INTERFACE["consumer"])
    if consumer is None or not consumer["is_theorem"]:
        raise ValueError("the actual worker's public source consumer is missing")
    useful_consumer = proofs.get(APPLICATION_INTERFACE["useful_consumer"])
    if useful_consumer is None or not useful_consumer["is_theorem"]:
        raise ValueError("the same-source useful public consumer is missing")
    bound = dict(APPLICATION_INTERFACE)
    bound["source_record_sha256"] = sha(record_path)
    bound["consumer_type_sha256"] = hashlib.sha256(consumer["type"].encode()).hexdigest()
    bound["useful_consumer_type_sha256"] = hashlib.sha256(useful_consumer["type"].encode()).hexdigest()
    bound["source_type_sha256"] = {}
    for role in ("source_factory", "source_receipt", "source_projection", "strict_predicate",
                 "acceptance_factory", "acceptance_receipt", "tick_bridge"):
        name = APPLICATION_INTERFACE[role]
        if name not in indexed:
            raise ValueError("entry consumer source interface is missing: " + name)
        row = indexed[name]
        payload = {key: row[key] for key in ("type", "definition") if key in row}
        bound["source_type_sha256"][name] = hashlib.sha256(
            json.dumps(payload, sort_keys=True).encode()).hexdigest()
    return bound


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--propose", action="store_true", help="write an ignored proposal for statement review")
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    before = sources()
    expected = None if args.propose else json.loads(MANIFEST.read_text())
    if expected is not None and expected["source_sha256"] != before:
        raise ValueError("entry sources changed; review the changed statements before amending the manifest")
    subprocess.run(["lake", "build", "LeanCageEntry", "EntryVerification", "leancage-entry", "leancage-entry-test"],
                   cwd=PACKAGE, check=True)
    inventory, declarations = query()
    record = dict(schema="leancage-entry-admission-claims-v2", complete_admission=True, scope=SCOPE,
                  input_producers=INPUT_PRODUCERS,
                  application_interface=application_interface(declarations),
                  predecessor=predecessor(),
                  toolchain=(PACKAGE / "lean-toolchain").read_text().strip(),
                  modules=inventory, declarations=declarations, source_sha256=before)
    if sources() != before:
        raise ValueError("entry sources changed during the audit")
    if args.propose:
        path = WORK / "proposed-entry-claims.json"
        path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
        print("Entry statement proposal written for review: " + str(path))
        return
    if record != expected:
        raise ValueError("entry statements, module inventory or transitive assumptions differ")
    artifacts = {str(p.relative_to(ROOT)): sha(p) for p in (PACKAGE / ".lake/build").rglob("*")
                 if p.is_file() and p.suffix in {".olean", ".a"}}
    for name in ("leancage-entry", "leancage-entry-test"):
        p = PACKAGE / ".lake/build/bin" / name
        artifacts[str(p.relative_to(ROOT))] = sha(p)
    (WORK / "audit.json").write_text(json.dumps(dict(manifest_sha256=sha(MANIFEST),
        sources=before, checked_artifacts=artifacts), indent=2, sort_keys=True) + "\n")
    print("Entry executable-definition, statement and transitive-assumption audit passed.")


if __name__ == "__main__":
    main()
