#!/usr/bin/env python3
"""Inspect the actual host declarations and compare their reviewed types, bodies and axioms."""
# §AR-host-boundary.acceptance: A source fingerprint never substitutes for the checked proposition.
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "assurance/host-claims.json"
LOGICAL = {"Classical.choice", "Quot.sound", "propext"}
INTERFACES = [
    "LeanCage.Host.Filesystem.Request", "LeanCage.Host.Filesystem.Op.code",
    "LeanCage.Host.Filesystem.call", "LeanCage.Host.Effect.interpret",
    "LeanCage.Host.Program.interpret", "LeanCage.Host.Entrypoint.run", "main",
    "LeanCage.Host.Packet.Observation", "LeanCage.Host.Entrypoint.Response",
    "LeanCage.Host.ApplicationProofs.Preparation", "LeanCage.Host.ExecutionProofs.Execution",
    "LeanCage.Host.ReceiveProofs.Complete", "LeanCage.Host.RequestGuarantee.CompleteRun",
    "LeanCage.Host.CallerProofs.AcceptedRun", "LeanCage.Host.Validation.EngineIdentity",
    "LeanCage.Host.Kernel.World", "LeanCage.Host.Kernel.Contract",
    "LeanCage.Host.Kernel.PhysicalPrefix", "LeanCage.Host.Kernel.PrefixTargets",
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def roots():
    text = (ROOT / "host/lakefile.lean").read_text()
    matched = re.search(r"lean_lib HostVerification where.*?roots\s*:=\s*#\[(.*?)\]", text, re.S)
    if matched is None:
        raise ValueError("missing maintained host verification library roots")
    return re.findall(r"`([A-Za-z][A-Za-z0-9_.]*)", matched.group(1))


def source_path(module):
    relative = Path(*module.split(".")).with_suffix(".lean")
    candidates = [ROOT / "host" / relative, ROOT / "verification/host" / relative]
    found = [path for path in candidates if path.is_file()]
    if len(found) > 1:
        raise ValueError("ambiguous host module: " + module)
    return found[0] if found else None


def modules(selected):
    found, pending = {}, list(selected)
    while pending:
        module = pending.pop()
        if module in found:
            continue
        path = source_path(module)
        if path is None:
            continue
        found[module] = path
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                pending += line.removeprefix("import ").split()
    if set(selected) - found.keys():
        raise ValueError("missing actual host proof source")
    return dict(sorted(found.items()))


def source_bindings(imported):
    paths = set(imported.values())
    paths |= {ROOT / name for name in (
        "host/lakefile.lean", "host/lake-manifest.json", "host/lean-toolchain",
        "linux/host_primitives.c", "linux/host_python.c", "linux/host_python_primitives.c",
        "linux/host_python_primitives.h", "scripts/audit_host.py",
        "scripts/host_axiom_query.lean")}
    return {str(path.relative_to(ROOT)): sha(path.read_bytes()) for path in sorted(paths)}


def query(selected, imported):
    helper = (ROOT / "scripts/host_axiom_query.lean").read_text().removeprefix("import Lean\n")
    source = "import Lean\n" + "".join("import " + name + "\n" for name in selected)
    source += "set_option maxRecDepth 1000000\nset_option pp.maxSteps 10000000\n" + helper
    source += "\n" + "".join("#host_audit_module " + name + "\n" for name in imported)
    source += "".join("#host_audit_decl " + name + "\n" for name in INTERFACES)
    directory = ROOT / ".tools/host"
    directory.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="declaration-query-", dir=directory) as temporary:
        path = Path(temporary) / "Query.lean"
        path.write_text(source)
        completed = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "host",
                                   capture_output=True, text=True, timeout=600)
    (directory / "declaration-query.lean").write_text(source)
    (directory / "declaration-query.log").write_text(completed.stdout + completed.stderr)
    if completed.returncode:
        raise ValueError("host declaration query failed; inspect .tools/host/declaration-query.log")
    rows = [json.loads(line.split("HOST_AUDIT ", 1)[1])
            for line in completed.stdout.splitlines() if "HOST_AUDIT " in line]
    inventories = {row["module"]: sorted(row["declarations"]) for row in rows if "module" in row}
    if set(inventories) != set(imported):
        raise ValueError("host declaration inventory omitted an imported module")
    interface_inventories = {row["module_interfaces"]: sorted(row["interfaces"])
                             for row in rows if "module_interfaces" in row}
    if set(interface_inventories) != set(imported):
        raise ValueError("host interface inventory omitted an imported module")
    interface_names = set(INTERFACES) | set().union(*(set(names) for names in interface_inventories.values()))
    constructors = {row["interface"]: row["constructors"] for row in rows if "interface" in row}
    if constructors.keys() != interface_names:
        raise ValueError("interface constructor inventory is incomplete")
    declarations, interfaces = {}, {}
    for row in rows:
        if "interface_parent" in row:
            parent = row["interface_parent"]
            row = dict(row["declaration"], interface_parent=parent)
        if "name" not in row:
            continue
        type_graph = row.pop("kernel_type")
        body = row.pop("kernel_body")
        for graph in (type_graph, body):
            if graph is not None and any(node[0] in ("free", "meta") for node in graph["nodes"]):
                raise ValueError("nonclosed kernel declaration: " + row["name"])
        row["kernel_type_sha256"] = sha(json.dumps(type_graph, sort_keys=True, separators=(",", ":")).encode())
        row["kernel_body_sha256"] = sha(json.dumps(body, sort_keys=True, separators=(",", ":")).encode()) if body is not None else None
        if row["name"] in interface_names or "interface_parent" in row:
            interfaces[row["name"]] = row
        if row["theorem"]:
            if set(row["axioms"]) - LOGICAL or row["kernel_body_sha256"] is None:
                raise ValueError("unreviewed theorem foundation or missing proof: " + row["name"])
            declarations[row["name"]] = row
    named = set().union(*(set(names) for names in inventories.values()))
    expected_interfaces = interface_names | set().union(*(set(names) for names in constructors.values()))
    if named != declarations.keys() or expected_interfaces != interfaces.keys():
        raise ValueError("declaration/interface query is incomplete")
    return {"modules": inventories, "interface_modules": interface_inventories, "declarations": declarations,
            "interfaces": interfaces, "interface_constructors": constructors}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--propose", action="store_true", help="write an unaccepted review proposal")
    args = parser.parse_args()
    selected = roots()
    imported = modules(selected)
    before = source_bindings(imported)
    # Main is an executable module; build it explicitly before checking its imported source.
    subprocess.run(["lake", "build", "leancage-host"], cwd=ROOT / "host", check=True)
    subprocess.run(["lake", "build", "HostVerification"], cwd=ROOT / "host", check=True)
    checked = query(selected, imported)
    if source_bindings(imported) != before:
        raise ValueError("host sources changed during declaration checking")
    current = {"schema": "leancage-host-claims-v1", "toolchain": (ROOT / "host/lean-toolchain").read_text().strip(),
               "source_sha256": before, **checked}
    if args.propose:
        destination = ROOT / ".tools/host/claims-proposal.json"
        destination.write_text(json.dumps(current, indent=2, sort_keys=True) + "\n")
        print("Host declaration proposal written for full statement review; integrated acceptance is separate.")
        return
    expected = json.loads(MANIFEST.read_bytes())
    if expected != current:
        raise ValueError("host declarations, sources or assumptions differ from the reviewed claim record")
    print("Host declarations match the reviewed complete types, proof bodies, module inventory and axioms.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        raise SystemExit("Host audit failed: " + str(error))
