#!/usr/bin/env python3
"""Strict shared data for the native gateway's individual kernel operations."""
# §AR-host-boundary.primitives: Keep the native event ABI independent of the full actor model.
import argparse
import json
import subprocess

import gateway


TARGETS = tuple("LeanCage.Host.NativeCode." + name for name in
                ("Operation", "Product", "Reply", "References", "Credentials", "SourceKey", "CallRow"))
TARGETS += ("LeanCage.Host.NativeChannels.Evidence",)
TARGETS += tuple("LeanCage.Host.ChannelCode." + name for name in
                 ("PairKind", "Invocation", "Invocation.WellFormed", "Invocation.storage",
                  "ReferenceAt", "PairUse", "PairUse.Consistent", "ReceiveUse", "ReceiveUse.Consistent"))


def reviewed_encryption_amendment(exported, pending, source, changed):
    preserved = gateway.WORK / "native-data-before-encryption"
    original_source = preserved / "NativeCode.lean"
    original_export = preserved / "native-code.ndjson"
    if gateway.sha(original_source) != "88e515025160235f831888f8d9bede7d045e9133212da796fdf233c7d45bca27":
        raise ValueError("encryption amendment source baseline does not match")
    if gateway.sha(exported) != "e88908d69abaa3b84017de6b614fb57128d52bc5ced5481be94456ff50ab82bd":
        raise ValueError("encryption amendment export baseline does not match")
    if gateway.sha(original_export) != gateway.sha(exported):
        raise ValueError("preserved native export differs from current baseline")
    addition = "  | setEncryptionPolicy (fd : Nat) (policy : List Nat)\n"
    anchor = "  | setInodeFlags (fd flags : Nat)\n"
    if source.read_text() != original_source.read_text().replace(anchor, anchor + addition):
        raise ValueError("encryption amendment contains another source change")
    prefix = "LeanCage.Host.NativeCode.VfsOperation"
    if not changed or any(not name.startswith(prefix) for name in changed):
        raise ValueError("encryption amendment changes another declaration group")
    previous = gateway.CONNECTION.export_fingerprints(exported)
    current = gateway.CONNECTION.export_fingerprints(pending)
    added = sorted(current.keys() - previous.keys())
    if any(not name.startswith(prefix) for name in added):
        raise ValueError("encryption amendment introduces another data interface")
    return dict(
        reason="Include the actual FS_IOC_SET_ENCRYPTION_POLICY transition on public directories",
        preserved=str(preserved.relative_to(gateway.ROOT)),
        before_source_sha256=gateway.sha(original_source), after_source_sha256=gateway.sha(source),
        before_export_sha256=gateway.sha(exported), after_export_sha256=gateway.sha(pending),
        changed=changed, added=added,
        review="Exact single constructor addition; all other existing declaration groups are unchanged",
    )


def reviewed_path_metadata_amendment(exported, pending, source, changed):
    preserved = gateway.WORK / "native-data-before-path-metadata"
    original_source = preserved / "NativeCode.lean"
    original_export = preserved / "native-code.ndjson"
    if gateway.sha(original_source) != "e6a2909463d01ae28e5778fd88add67fd1accff1f8e9f7faf8304af19001f789":
        raise ValueError("path metadata amendment source baseline does not match")
    if gateway.sha(exported) != "03f4644e8de8c5e160b6a21f37664412b6c9654f8f65b626e29a982a132065f5":
        raise ValueError("path metadata amendment export baseline does not match")
    if gateway.sha(original_export) != gateway.sha(exported):
        raise ValueError("preserved native export differs from current baseline")
    anchor = "  | removeAttribute (fd : Nat) (name : List Nat)\n"
    addition = ("  | fchmodAt (directory : Nat) (path : List Nat) (mode flags : Nat)\n"
                "  | fchownAt (directory : Nat) (path : List Nat) (owner group flags : Nat)\n")
    if source.read_text() != original_source.read_text().replace(anchor, anchor + addition):
        raise ValueError("path metadata amendment contains another source change")
    prefix = "LeanCage.Host.NativeCode.VfsOperation"
    if not changed or any(not name.startswith(prefix) for name in changed):
        raise ValueError("path metadata amendment changes another declaration group")
    previous = gateway.CONNECTION.export_fingerprints(exported)
    current = gateway.CONNECTION.export_fingerprints(pending)
    added = sorted(current.keys() - previous.keys())
    if added != [prefix + ".fchmodAt", prefix + ".fchownAt"]:
        raise ValueError("path metadata amendment adds another data interface")
    return dict(
        reason="Represent actual path chmod/chown operations without an invented open+FD sequence",
        preserved=str(preserved.relative_to(gateway.ROOT)),
        before_source_sha256=gateway.sha(original_source), after_source_sha256=gateway.sha(source),
        before_export_sha256=gateway.sha(exported), after_export_sha256=gateway.sha(pending),
        changed=changed, added=added,
        review="Exact two-constructor append; other data groups and existing constructor order unchanged",
    )


def reviewed_source_rows_extension(exported, pending, source, changed):
    preserved = gateway.WORK / "native-data-before-source-rows"
    original_source = preserved / "NativeCode.lean"
    original_export = preserved / "native-code.ndjson"
    if gateway.sha(original_source) != "347181920990c3deba0a464436791816eb818ac454c6793acb8ca9e7e124b10a":
        raise ValueError("source-row extension source baseline does not match")
    if gateway.sha(exported) != "0a4b2c81be2fc66146e6b8d8aa22c26a9144614ec3d965e79227eef91515652a":
        raise ValueError("source-row extension export baseline does not match")
    if gateway.sha(original_export) != gateway.sha(exported):
        raise ValueError("preserved native export differs from current baseline")
    addition = """-- §AR-host-boundary.interfaces.gateway: Source invocation and all primitive fields share one row.
structure SourceKey where
  process : Nat
  entryPosition : Nat
  actionsLifetime : Nat
  attributesLifetime : Nat

structure CallRow where
  process : Nat
  caller : Credentials
  beforeReferences : References
  afterReferences : References
  operation : Operation
  reply : Option Reply
  product : Product

"""
    anchor = "end LeanCage.Host.NativeCode\n"
    if source.read_text() != original_source.read_text().replace(anchor, addition + anchor):
        raise ValueError("source-row extension contains another source change")
    if changed:
        raise ValueError("source-row extension modifies existing declarations")
    previous = gateway.CONNECTION.export_fingerprints(exported)
    current = gateway.CONNECTION.export_fingerprints(pending)
    added = sorted(current.keys() - previous.keys())
    prefixes = ("LeanCage.Host.NativeCode.SourceKey", "LeanCage.Host.NativeCode.CallRow")
    if not added or any(not name.startswith(prefixes) for name in added):
        raise ValueError("source-row extension adds another declaration group")
    return dict(
        reason="Share exact invocation identity and one complete native row across C/source and actor consumers",
        preserved=str(preserved.relative_to(gateway.ROOT)),
        before_source_sha256=gateway.sha(original_source), after_source_sha256=gateway.sha(source),
        before_export_sha256=gateway.sha(exported), after_export_sha256=gateway.sha(pending),
        changed=changed, added=added,
        review="Exact two-record addition; every existing Native94 declaration fingerprint is unchanged",
    )


def reviewed_channels_extension(exported, pending, source, changed):
    preserved = gateway.WORK / "native-data-before-channels"
    before_source = preserved / "NativeCode.lean"
    before_export = preserved / "native-code.ndjson"
    channels = gateway.HERE / "NativeChannelCode.lean"
    if gateway.sha(before_source) != "2e29ec519029d540f7c436efa146e3d91e726ae804e63528e711555392d5410a":
        raise ValueError("native channel source baseline does not match")
    if gateway.sha(before_export) != "03ab2ffa243f5b6ca2da8a7dd3956647170effbe71db0ed9b25f9402da241ebb":
        raise ValueError("native channel export baseline does not match")
    if source.read_bytes() != before_source.read_bytes() or gateway.sha(exported) != gateway.sha(before_export):
        raise ValueError("native channel extension changes its Native100 baseline")
    if gateway.sha(channels) != "637b88ad846ea679c1176976e78f2169950dac69e2d6df50b6bbce9aed5eef1c":
        raise ValueError("native channel extension differs from the reviewed pure interface")
    if changed:
        raise ValueError("native channel extension changes existing declarations")
    previous = gateway.CONNECTION.export_fingerprints(exported)
    current = gateway.CONNECTION.export_fingerprints(pending)
    added = sorted(current.keys() - previous.keys())
    allowed = ("LeanCage.Host.NativeChannels.", "LeanCage.Host.NativeCode.References.",
               "LeanCage.Host.NativeCode.Handle.", "And", "Eq", "Ne", "Not", "False",
               "OfNat", "instOfNatNat", "Option.casesOn", "PUnit", "Unit")
    if not added or any(not name.startswith(allowed) for name in added):
        raise ValueError("native channel extension adds unexpected dependencies: " + ", ".join(added))
    return dict(
        reason="Share actual full exec-reference channel observations with the source and engine consumers",
        preserved=str(preserved.relative_to(gateway.ROOT)),
        before_source_sha256=gateway.sha(before_source), after_source_sha256=gateway.sha(source),
        channel_source_sha256=gateway.sha(channels),
        before_export_sha256=gateway.sha(exported), after_export_sha256=gateway.sha(pending),
        changed=changed, added=added,
        review="Native100 source and all existing declaration fingerprints unchanged; pure object/close-exec observations added",
    )


def reviewed_invocations_extension(exported, pending, source, changed):
    preserved = gateway.WORK / "native-data-before-invocations"
    before_source = preserved / "NativeCode.lean"
    before_export = preserved / "native-code.ndjson"
    invocations = gateway.HERE / "GatewayChannelCode.lean"
    if gateway.sha(before_source) != "2e29ec519029d540f7c436efa146e3d91e726ae804e63528e711555392d5410a":
        raise ValueError("source invocation extension native baseline does not match")
    if gateway.sha(before_export) != "f6bb9b8b88cd7e99d6438a3b8fba82a4eb6688e3d5825073f3a04f66a57f16d2":
        raise ValueError("source invocation extension export baseline does not match")
    if source.read_bytes() != before_source.read_bytes() or gateway.sha(exported) != gateway.sha(before_export):
        raise ValueError("source invocation extension changes its Native127 baseline")
    if gateway.sha(invocations) != "602fa489467a021bca0c757e439cab3e01e5aa82037dee2fd02f38938ca952b8":
        raise ValueError("source invocation extension differs from the reviewed pure interface")
    if changed:
        raise ValueError("source invocation extension changes existing declarations")
    previous = gateway.CONNECTION.export_fingerprints(exported)
    current = gateway.CONNECTION.export_fingerprints(pending)
    added = sorted(current.keys() - previous.keys())
    prefixes = ("LeanCage.Host.ChannelCode.", "LeanCage.Host.NativeCode.CallRow.",
                "LeanCage.Host.NativeCode.SourceKey.", "LeanCage.Host.NativeCode.Handle.",
                "Exists", "LE", "LT", "Nat.le", "Nat.lt", "Or", "instLENat", "instLTNat")
    if not added or any(not name.startswith(prefixes) for name in added):
        raise ValueError("source invocation extension adds unexpected dependencies: " + ", ".join(added))
    return dict(
        reason="Bind source allocation lifetimes and exact pair/read rows without a private-role assumption",
        preserved=str(preserved.relative_to(gateway.ROOT)),
        before_source_sha256=gateway.sha(before_source), after_source_sha256=gateway.sha(source),
        invocation_source_sha256=gateway.sha(invocations),
        before_export_sha256=gateway.sha(exported), after_export_sha256=gateway.sha(pending),
        changed=changed, added=added,
        review="Native127 bytes preserved and all127 fingerprints unchanged; raw consistency supplies no channel authority",
    )


def prepare(amend_encryption_policy=False, amend_path_metadata=False, extend_source_rows=False, extend_channels=False,
            extend_invocations=False):
    if sum((amend_encryption_policy, amend_path_metadata, extend_source_rows, extend_channels, extend_invocations)) > 1:
        raise ValueError("select one explicit native interface amendment")
    source = gateway.HERE / "NativeCode.lean"
    before = gateway.sha(source)
    channels = gateway.HERE / "NativeChannelCode.lean"
    channels_before = gateway.sha(channels)
    invocations = gateway.HERE / "GatewayChannelCode.lean"
    invocations_before = gateway.sha(invocations)
    subprocess.run(["lake", "build", "GatewayChannelCode"], cwd=gateway.ROOT / "host", check=True)
    exporter = gateway.PROFILE.WORK / "lean4export/.lake/build/bin/lean4export"
    pending = gateway.WORK / "native-code.pending.ndjson"
    exported = gateway.WORK / "native-code.ndjson"
    with pending.open("w") as output:
        subprocess.run(["lake", "env", str(exporter), "GatewayChannelCode", "--", *TARGETS],
                       cwd=gateway.ROOT / "host", stdout=output, check=True)
    records = gateway.CONNECTION.export_records(pending)
    fingerprints = gateway.CONNECTION.export_fingerprints(pending)
    amendment = None
    if exported.is_file():
        previous = gateway.CONNECTION.export_fingerprints(exported)
        changed = [name for name, value in previous.items() if fingerprints.get(name) != value]
        added = fingerprints.keys() - previous.keys()
        if extend_invocations:
            amendment = reviewed_invocations_extension(exported, pending, source, changed)
        elif extend_channels:
            amendment = reviewed_channels_extension(exported, pending, source, changed)
        elif extend_source_rows:
            amendment = reviewed_source_rows_extension(exported, pending, source, changed)
        elif changed and amend_encryption_policy:
            amendment = reviewed_encryption_amendment(exported, pending, source, changed)
        elif changed and amend_path_metadata:
            amendment = reviewed_path_metadata_amendment(exported, pending, source, changed)
        elif changed:
            raise ValueError("native event proof interface changed: " + ", ".join(changed))
        elif added:
            raise ValueError("native event proof interface adds unreviewed declarations: " + ", ".join(sorted(added)))
    elif amend_encryption_policy or amend_path_metadata or extend_source_rows or extend_channels or extend_invocations:
        raise ValueError("native amendment requires its preserved export baseline")
    if (gateway.sha(source) != before or gateway.sha(channels) != channels_before or
            gateway.sha(invocations) != invocations_before):
        raise ValueError("native event source changed during export")
    pending.replace(exported)
    gateway.compile_file("GatewayNativeImport")
    if amendment is not None:
        amendment["strict_import"] = "checked without importer relaxation"
        amendment_name = ("native-invocations-extension.json" if extend_invocations else
                          "native-channels-extension.json" if extend_channels else
                          "native-source-rows-extension.json" if extend_source_rows else
                          "native-path-metadata-amendment.json" if amend_path_metadata else
                          "native-encryption-amendment.json")
        (gateway.WORK / amendment_name).write_text(
            json.dumps(amendment, indent=2, sort_keys=True) + "\n")
    (gateway.WORK / "native-export.json").write_text(json.dumps(dict(
        targets=TARGETS, source_sha256=before, export_sha256=gateway.sha(exported),
        inputs={str(source.relative_to(gateway.ROOT)): before,
                str(channels.relative_to(gateway.ROOT)): channels_before,
                str(invocations.relative_to(gateway.ROOT)): invocations_before},
        declarations=sum(len(names) for _, names in records), fingerprints=fingerprints,
        amendment=amendment,
    ), indent=2, sort_keys=True) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--amend-encryption-policy", action="store_true",
                        help="apply only the preserved and reviewed encryption-policy enum addition")
    parser.add_argument("--amend-path-metadata", action="store_true",
                        help="apply only the preserved path chmod/chown constructor append")
    parser.add_argument("--extend-source-rows", action="store_true",
                        help="add only reviewed source-key/full-row records, preserving Native94")
    parser.add_argument("--extend-channels", action="store_true",
                        help="add reviewed pure channel observers, preserving all Native100 declarations")
    parser.add_argument("--extend-invocations", action="store_true",
                        help="add reviewed actual source/pair/read data, preserving all Native127 declarations")
    parser.add_argument("modules", nargs="*")
    arguments = parser.parse_args()
    if arguments.prepare:
        prepare(arguments.amend_encryption_policy, arguments.amend_path_metadata, arguments.extend_source_rows,
                arguments.extend_channels, arguments.extend_invocations)
    elif (arguments.amend_encryption_policy or arguments.amend_path_metadata or arguments.extend_source_rows or
          arguments.extend_channels or arguments.extend_invocations):
        parser.error("native amendments require --prepare")
    for module in arguments.modules:
        gateway.compile_file(module)


if __name__ == "__main__":
    main()
