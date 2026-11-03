# Running LeanCage

Build and run caller-supplied offline Python and shell tasks from the project root.
Execution uses the designated disposable Linux VM under [§FS-linux-product.operation](functional-spec/FS-linux-product.md#operation-run-a-callers-workload-through-one-supported-interface).
The host validates policies and owns the VM process.

## Build the supported bundle

On Linux x86-64 with the Ubuntu 24.04 bootstrap prerequisites (elan, Python 3,
Bash, Git, curl, tar, GNU coreutils, C compiler, Linux headers and static libc
development files), run:

```sh
./scripts/build.sh
./leancage bundle
```

The build uses checksum-pinned local QEMU/SeaBIOS packages, Linux 6.18.59, the
locked Python 3.13.18/Dash runtime and existing Lean 4.35.0 dependency pins.
Missing tools/runtime are prepared inside `.tools/`; prepared checkouts reuse
matching assets. No global installation or host kernel change is performed.
`--no-prepare` requires the pinned VM assets to be present already.

The result is `.tools/product/bundle/`. Its `manifest.json` identifies the actual
controller, native helper, VM init, filter, runtime initramfs, kernel/configuration,
emulator/firmware closure, proof records and trusted components. `bundle/bin/leancage`
is the staged entry point. `./leancage --bundle PATH ...` selects another bundle.
The manifest hash is its bundle identity; modified components are rejected.
This is a local VM product bundle. General-host deployment is a separate profile.

## Run the caller examples

The example policies are ordinary supported policies. Their private input files
include the programs, numbers and a message. The host freezes files/stdin before
boot, fills null digest fields with the snapshot identities and validates the
assembled policy with the shipped Lean controller. A supplied digest must match.

```sh
./leancage check examples/workspace/python-policy.json \
  --workspace examples/workspace/input --stdin examples/workspace/stdin.txt
./leancage run examples/workspace/python-policy.json \
  --workspace examples/workspace/input --stdin examples/workspace/stdin.txt
./leancage run examples/workspace/shell-policy.json \
  --workspace examples/workspace/input --stdin examples/workspace/stdin.txt
```

Python sums `10, 20, 12`, uses stdin and exports `summary.json` containing
`{"stdin": "caller stdin", "sum": 42}`. Shell reads the message and stdin, then
exports `answer.txt` containing `caller workspace / caller stdin`. Both return
separately bounded stdout/stderr. Edit argv and limits in a policy copy to run
another supported task. The first argv entry remains `/bin/sh` or
`/usr/local/bin/python3`; [§FS-workspace.policy](functional-spec/FS-workspace.md#policy-bounded-typed-request) gives the exact bounds.

Inputs support regular files and directories; links and special files fail before
boot. The policy/profile versions, runtime digest and confinement rules are unchanged.

Each command prints one JSON envelope with a fresh `request_id`, `bundle_id`,
actual VM report, transport/publication status and artifact identities. The VM's
private `run_id` is local to that fresh VM; use `request_id` for host retrieval.
`check` never enters the workload. `run` propagates the observed controller outcome:
for example guest exit 0, cancellation 124 or storage/transport failure 126.
An output limit requests cancellation and cleanup.

The returned `output` directory contains:

- `result.json`: the host envelope binding the request to its bundle and artifacts.
- `policy.json`: the exact frozen policy sent to the VM.
- `vm-report.json`: the original controller report, retaining known observations
  even if a later channel or storage operation failed.
- `stored-report.json`: the report retrieved with the in-VM `report` command
  when its publication succeeded.
- `stdout`, `stderr`, `export/`: validated captures and regular-file exports
  after a complete transport. Incomplete transports mark these unavailable.
- `boot.log`: diagnostics with no control/result authority.

Retrieve and verify a run with its printed identity or directory:

```sh
./leancage report REQUEST_ID
./leancage report /absolute/path/to/returned/output
```

The default host store is `.tools/product/runs/`. `--results PATH` selects another
store; put it before the command. `run --output PATH` publishes to a new directory
without replacing a target. Retrieval verifies capture/export hashes and the
request/bundle binding. Preserve identified bundles when retaining runs across updates.

Press Ctrl-C or send SIGTERM to request cancellation. The helper cancels and
cleans up owned descendants, then the host reaps the VM. `--timeout SECONDS` bounds
the VM lifetime. Lost/malformed channels and VM death produce an incomplete result;
already observed entry/cleanup facts survive. `vm_cleanup: complete` means the
owned VM was reaped. The nested report's `cleanup` describes helper observations.
Neither is inferred merely from requesting cancellation. [§AR-workspace-vm](architecture/AR-workspace-vm.md#ar-workspace-vm-own-the-caller-request-disposable-vm-and-returned-artifacts) defines
the protocol, bounds and ownership.

## Reusable libraries

The CLI and Python integrations use the same API:

```python
from pathlib import Path
from leancage import Workspace

workspace = Workspace()
result = workspace.run(
    Path("examples/workspace/python-policy.json"),
    workspace=Path("examples/workspace/input"),
    stdin=Path("examples/workspace/stdin.txt"),
)
assert result.status == "complete" and result.report["entry"] == "yes"
print(result.stdout.decode())
print(result.files["summary.json"].decode())
assert workspace.report(result.request_id)["request_id"] == result.request_id
```

Run integrations from the root with `PYTHONPATH=python`, or use the staged
`bundle/python` library with an explicit bundle path. `Workspace.check`,
`Workspace.run`, `Workspace.report` and `Cancellation.cancel` form the shared API.

The Lean library is `library/LeanCageWorkspace.lean`, built by the root recipe.
`import LeanCageWorkspace` exposes `LeanCage.Workspace.Policy`, `Result`,
`decodePolicy`, `decodeResult`, `filterBytes`, `check` and `run`. These aliases
use the existing executable definitions, with audited definition equations.
The compatibility map is [§AR-workspace-vm.migration](architecture/AR-workspace-vm.md#migration-preserve-proof-identities-while-moving-maintained-components) and
`assurance/product-layout.json`; there are no parallel implementation copies.

## Validation and assurance

```sh
./scripts/check_product.sh
./scripts/check_m4_all.sh
python3 tests/product/acceptance.py
```

The product gate runs the foundation once, the core/library type/axiom audit,
pure transport/snapshot/publication tests and native init compilation. CI uses
that same gate. The reporting aggregate reuses matching source/compiler artifacts
and checks the preserved VM/capture evidence. Product acceptance boots the actual
bundle for caller Python/shell requests, denial, bounded output, cancellation,
descendant cleanup, VM/host storage failure and channel/VM loss. It writes
`assurance/product-vm-evidence.json`; returned test outputs remain under
`.tools/product/acceptance/BUNDLE_ID/`.

`assurance/product-core.json` records full theorem types, foundations, source
bindings and actual consumers. The bundle enumerates native/host adapters
separately from the checked policy/filter/result core. Conditional reporting/compiler
receipts retain their original premises. Linux/compiler/runtime/FFI and VM/hardware
trust is explicit under [§FS-linux-product.trust](functional-spec/FS-linux-product.md#trust-platform-assumptions-for-the-initial-product); M5/M6 strengthen that assurance.

For the preserved fixed-workload regression, use
`python3 scripts/run_m3_vm.py --development`. Its 60 cases, three in-VM API checks
and six death/cancellation boundaries are distinct from the caller suite.
Earlier M1/M2 regression recipes remain in the development guide.
