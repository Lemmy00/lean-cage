#!/usr/bin/env python3
"""Strictly connect the native descriptor view to the shared Lean engine view."""
# §AR-host-boundary.interfaces: Keep the descriptor bridge separate from the frozen byte codec.
import argparse
import json
import subprocess

import gateway


TARGETS = (
    "LeanCage.Host.NativeSpawn.Descriptor",
    "LeanCage.Host.NativeSpawn.ChannelEvidence",
)


def prepare():
    subprocess.run(["lake", "build", "GatewaySpawnChannels"], cwd=gateway.ROOT / "host", check=True)
    exporter = gateway.PROFILE.WORK / "lean4export/.lake/build/bin/lean4export"
    pending = gateway.WORK / "spawn-code.pending.ndjson"
    exported = gateway.WORK / "spawn-code.ndjson"
    with pending.open("w") as output:
        subprocess.run(["lake", "env", str(exporter), "GatewaySpawnChannels", "--", *TARGETS],
                       cwd=gateway.ROOT / "host", stdout=output, check=True)
    records = gateway.CONNECTION.export_records(pending)
    fingerprints = gateway.CONNECTION.export_fingerprints(pending)
    if exported.is_file():
        previous = gateway.CONNECTION.export_fingerprints(exported)
        changed = [name for name, fingerprint in previous.items() if fingerprints.get(name) != fingerprint]
        if changed:
            raise ValueError("native descriptor proof interface changed: " + ", ".join(changed))
    pending.replace(exported)
    (gateway.WORK / "spawn-export.json").write_text(json.dumps(dict(
        targets=TARGETS, export_sha256=gateway.sha(exported),
        declarations=sum(len(names) for _, names in records), fingerprints=fingerprints,
    ), indent=2, sort_keys=True) + "\n")
    gateway.compile_file("GatewaySpawnImport")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("modules", nargs="*")
    arguments = parser.parse_args()
    if arguments.prepare:
        prepare()
    for module in arguments.modules:
        gateway.compile_file(module)


if __name__ == "__main__":
    main()
