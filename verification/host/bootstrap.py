#!/usr/bin/env python3
"""Check the native module's path computation against shared executable bytes."""
# §AR-host-boundary.interfaces: Use an independent strict dataset for bootstrap path construction.
import argparse
import json
import subprocess

import gateway


TARGETS = tuple("LeanCage.Host.BootstrapCode." + name for name in
                ("suffix", "executable", "results", "Layout", "supported", "layout"))


def prepare():
    subprocess.run(["lake", "build", "GatewayBootstrapCode"], cwd=gateway.ROOT / "host", check=True)
    exporter = gateway.PROFILE.WORK / "lean4export/.lake/build/bin/lean4export"
    pending = gateway.WORK / "bootstrap-code.pending.ndjson"
    exported = gateway.WORK / "bootstrap-code.ndjson"
    with pending.open("w") as output:
        subprocess.run(["lake", "env", str(exporter), "GatewayBootstrapCode", "--", *TARGETS],
                       cwd=gateway.ROOT / "host", stdout=output, check=True)
    records = gateway.CONNECTION.export_records(pending)
    fingerprints = gateway.CONNECTION.export_fingerprints(pending)
    if exported.is_file():
        previous = gateway.CONNECTION.export_fingerprints(exported)
        changed = [name for name, fingerprint in previous.items() if fingerprints.get(name) != fingerprint]
        if changed:
            raise ValueError("bootstrap path proof interface changed: " + ", ".join(changed))
    pending.replace(exported)
    gateway.compile_file("GatewayBootstrapImport")
    (gateway.WORK / "bootstrap-export.json").write_text(json.dumps(dict(
        targets=TARGETS, export_sha256=gateway.sha(exported),
        declarations=sum(len(names) for _, names in records), fingerprints=fingerprints,
    ), indent=2, sort_keys=True) + "\n")


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
