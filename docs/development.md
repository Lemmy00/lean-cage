# Development

Start with the [roadmap](roadmap.md), [agent rules](../AGENTS.md), and the contract
for the assigned task. The preserved M1 boundary is [§AR-m1-launch](architecture/AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration) (M1), using
the source/launch contract in [§AR-filter-slice.contracts](architecture/AR-filter-slice.md#contracts-lean-declarations-and-downstream-ownership).
M2 is complete for the stated lifecycle profile under [§AR-lifecycle](architecture/AR-lifecycle.md#ar-lifecycle-m2-controller-native-helper-and-evidence).
M3 implementation follows [§FS-workspace](functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) and [§AR-workspace](architecture/AR-workspace.md#ar-workspace-m3-authority-model-linux-realization-and-evidence-plan) in
[§RM-roadmap.m3.packages](roadmap.md#m3packages-build-the-profile-in-reviewable-slices) order.
The workflow is specified in [§AR-tooling](architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local).
The current bounded assignment is [§RM-roadmap.m4.next](roadmap.md#m4next-current-m4-continuation)
and [M4-CONTINUE.md](../M4-CONTINUE.md); the historical M4.1 contract remains at
[§RM-roadmap.m4.entry](roadmap.md#m4entry-next-assignment--m41-native-semantics-feasibility). Keep validated
milestone work integrated on `main`; temporary branches are for isolation during
active work, not separate long-lived milestone histories.

The parent repair's independent review and aggregate outcome are recorded in
`assurance/m4-parent-validation.json`. Its maintained gate is
`python3 m4/parent/check.py`. Early Lean/Linux connection attempts have a separate
replay, `python3 m4/routes/check.py`, under [§AR-m4-routes.evidence](architecture/AR-m4-routes.md#evidence-replay-and-claim-boundary).
Prepare its isolated inspection checkout as described in `m4/routes/README.md`;
this changes no maintained toolchain or VM pin. Reproducing an expected failed
connection is not a security proof or M4 completion.

## Setup and checks

Use Linux x86-64 with Bash, Git, curl, tar, GNU coreutils, Python 3, elan, a C
compiler, and Linux headers available. The Grund wrapper also supports aarch64;
the M1 native binding deliberately supports only x86-64. No root access, Docker, host kernel changes, or global Grund
installation is needed. The first run needs network access to fetch pinned tools
and dependencies.

```sh
./scripts/check.sh
```

This validates Grund configuration and managed guidance, checks ordinary and full
citation scope and formatting, builds the library and audits declaration/type/
axiom/source evidence, runs Python integration tests, and checks the reference
filter, decoder, and launch traces with pure Lean fixtures. It compiles the native
driver and checks archived VM evidence against current source hashes; it does
not boot the VM or execute a guest on the host. The
[CI workflow](../.github/workflows/check.yml) invokes the same command on GitHub;
adding the workflow locally does not mean a hosted run has already passed.

The exact proof/tool pins are in [§AR-tooling.pins](architecture/AR-tooling.md#pins-foundation-dependencies-and-references). Lake locks the transitive
Plausible revision in `lake-manifest.json`. Keep the manifest in version control.
`LeanCage.lean` imports Velvet, the contract modules, the executable decoder and
its proofs, the launch model, and decoder-linked launch proofs. The separately
recorded model properties are not sandbox isolation
theorem. Preserve the gate in [§AR-verification.audit](architecture/AR-verification.md#audit-statements-axioms-and-nonvacuity) when adding results.

## Navigate the plan and specifications

Always use the local wrapper, including for commands shown as `grund` in generated
guidance. It runs from the repository root and downloads its own checksum-pinned
release if missing.

```sh
./scripts/grund.sh RM-roadmap.next --full
./scripts/grund.sh FS-filter-loading --toc
./scripts/grund.sh FS-filter-loading.input
./scripts/grund.sh refs FS-filter-loading --summary
./scripts/grund.sh list --kind FS,AR
```

The canonical homes are goals and motivation in `docs/`, functional specs in
`docs/functional-spec/`, requirements in `docs/requirements/`, architecture in
`docs/architecture/`, and accepted decisions under `docs/decisions/`.
Keep the plan in `docs/roadmap.md` and claim status in [§FS-assurance.status](functional-spec/FS-assurance.md#status-initial-claim-register) instead
of creating competing copies in task notes.

## Make a change

1. Inspect the working tree and read the applicable contract and its callers.
2. State the intended behavior/theorem and assumptions. Update the contract and
   decision record when needed; do not weaken the claim to fit an easy proof.
3. Implement the smallest assigned slice and cite its specific contract. Add
   meaningful tests for its risks and failure paths. Run OS experiments in the
   isolated environment required by [§AR-linux.platform](architecture/AR-linux.md#platform-isolated-integration-profile).
4. Audit theorem statements, hypotheses, and transitive axioms. Record the actual
   implementation/artifact correspondence and open gaps under [§FS-assurance](functional-spec/FS-assurance.md#fs-assurance-bind-every-advertised-guarantee-to-auditable-evidence).
5. Format, validate, and review the diff. Report checks and limitations separately.

Lean citations use standalone line comments, for example:

```lean
-- §FS-filter-loading.input: Reject inputs outside the supported instruction bounds.
```

After editing documentation or citation IDs:

```sh
./scripts/grund.sh fmt --write
./scripts/check.sh
```

After editing `grund.toml`, also run `./scripts/grund.sh init` before those checks.
Keep custom agent rules outside the managed block. Retain section locks produced
by Grund; do not hand-edit them or drop citations to hide stale references.

## Evidence and handoff

The documentation tests exercise discovery of a valid Lean citation, failure on a
dangling citation, and dependency-directory exclusion in temporary fixtures. They
test the project configuration against the real Grund binary, not the truth of the
specification. Build before running Python integration tests, which now also
query actual Lean proof environments and test audit rejection paths.
The M1.1 fixture check can also be run after `lake build` with
`lake env lean tests/integration/FilterContract.lean`; its 14 guards exercise
allowed, denied, architecture-mismatch, x32, and unsigned-threshold cases.
`lake env lean tests/integration/FilterDecoder.lean` adds 21 guard commands,
including every truncated prefix and all 18360 single-byte substitutions.
`python3 scripts/audit_axioms.py` builds and audits the actual project theorem
inventory against `assurance/filter-decoder.json`. On expected statement/source
changes, review the actual types/axioms and source identities before explicitly
updating that manifest; the normal check never regenerates expectations. The
local report is `.tools/assurance/filter-decoder-report.json`. See
[§FS-assurance.decoder](functional-spec/FS-assurance.md#decoder-m12-decoder-claim-record) and [§FS-assurance.launch](functional-spec/FS-assurance.md#launch-m13-launch-order-claim-record) for exact proof scope. The historical manifest
filename now covers all M1 declarations, sources and VM evidence. Preserve the
independent 18-claim baseline in `assurance/m1.2-decoder-claims.json` when extending
the audit. The complete original decoder theorem types and axiom sets are unchanged.
`lake env lean tests/integration/Launch.lean` exercises the launch transitions,
terminal failures, and actual decoder/entry verdicts.
Later runtime tests belong under `tests/e2e/`; component-boundary
tests belong under `tests/integration/` and cite architecture contracts.

## Replay the M1 Linux VM

The recorded bootstrap host is Ubuntu 24.04 x86-64 with `apt-get`, `dpkg-deb`,
`make`, a native C toolchain/static libc development files, `bc`, `tar`, and
Python 3 available. Exact guest kernel/QEMU/bootstrap package pins and checksums
are in `tests/vm/bootstrap-pins.json`; the script fails rather than upgrading
them if those versions are unavailable. It extracts packages locally without
host installation or root. Linux, QEMU, their firmware and tools retain upstream
licenses and are not vendored into maintained source.

```sh
python3 scripts/run_m1_vm.py --prepare
python3 scripts/run_m1_vm.py --check-evidence
```

Preparation downloads verified inputs to `.tools/m1vm`, extracts a fresh kernel
tree, copies the reviewed full `tests/vm/linux-6.18.59.config`, and builds with two
low-priority jobs. The main choices are summarized in `tests/vm/kernel.fragment`;
changes require explicit resolved-configuration review. No shared host kernel
setting changes. QEMU uses TCG software emulation, one vCPU, 2048 MiB, no NIC,
disk or host mount, an ephemeral RAM filesystem and a 180-second timeout.
The trusted static guest runs only there as UID/GID 65534. Do not execute the
native fixture or PID-1 init on the shared host.

For later replays, `python3 scripts/run_m1_vm.py` rebuilds the driver/fixtures and
uses the existing pinned kernel/tools. Actual observations and artifact/source
hashes replace `assurance/m1-vm-evidence.json` and `assurance/m1-vm-transcript.log`.
Review those changes before updating reviewed assurance fingerprints; neither
the VM runner nor the handoff gate auto-approves a new theorem manifest.
`--check-evidence` checks only archived source/transcript/structured evidence.
The full gate uses that mode so ordinary checks need no downloaded VM image.
Source drift requires a VM replay; a new compiler output is not certified by
checking the old transcript. See [§FS-assurance.demo](functional-spec/FS-assurance.md#demo-m14-isolated-linux-test-record) for all 13 outcomes and
the native/Linux/hardware assumptions.

Use [§REQ-proof-integrity](requirements/REQ-proof-integrity.md#req-proof-integrity-never-substitute-a-weaker-claim-for-an-unfinished-proof) and [§FS-assurance.evidence](functional-spec/FS-assurance.md#evidence-required-claim-record) for the proof review. A future
agent handoff includes task scope, touched contracts/files, checks, proof statements,
assumptions, and remaining obligations. Claim only evidence actually obtained.

## M2 proof package and capable VM

[§AR-lifecycle](architecture/AR-lifecycle.md#ar-lifecycle-m2-controller-native-helper-and-evidence) defines the fresh-helper execution design and the complete M1
premise/source/effect maps. The dependent `m2/` Lake package uses the unchanged
root pins; its own manifest/toolchain files are committed. Main's actual decoder
emits only the fixed plan, then invokes the static helper in the designated VM.
There is no shared-host root helper installation or setuid deployment.

```sh
(cd m2 && lake build LeanCageM2 leancage-m2)
(cd m2 && lake env lean tests/integration/Lifecycle.lean)
python3 scripts/audit_m2.py
python3 -m unittest discover -s m2/tests/integration -p 'test_*.py' -v
```

The full top-level `./scripts/check.sh` includes these checks and a compile-only
static helper check. It requires the native static libc development files as well
as the C compiler and Linux headers. It does not launch guest workloads on the
host. The M2 proof auditor checks complete types/transitive axioms, every M2
module including Main, all 445 original M1 theorem statements/axioms, exact source
and test/evidence fingerprints, and `.olean` identities. The original full M1
manifest is retained in `assurance/m1-reviewed-baseline.json`; the current M1
manifest has only reviewed shared-source fingerprint updates.

```sh
python3 scripts/run_m2_vm.py --prepare
python3 scripts/run_m2_vm.py --check-evidence
python3 scripts/run_m2_vm.py --check-artifacts
```

M2 preparation extracts checksum-pinned tools locally and builds a fresh kernel
from the original pinned Linux archive using `tests/m2/linux-6.18.59.config` in
`.tools/m2vm`, with two low-priority jobs. It leaves `.tools/m1vm` and the M1 source,
configuration and raw evidence alone. The M2 initramfs enables positive controls
for namespace, Unix/IPv4, SysV IPC and cgroup CPU/memory/pids features. Guest
workloads use UID/GID 65534; the controller/helper/init are trusted root inside
the VM. All kernel and native results remain conditional on the explicit Linux,
compiler/runtime, administrative and hardware assumptions in [§FS-assurance.lifecycle](functional-spec/FS-assurance.md#lifecycle-m2-lifecycle-and-filter-semantics-claim-record).

Replay without `--prepare` rebuilds the guest image using the existing recorded
kernel. `--check-evidence` checks archived source/schema/transcript identities;
`--check-artifacts` additionally compares the available recorded native binaries,
kernel/configuration, image, emulator and runtime identities. A new compile is not
certified by an old transcript. After a deliberate source change, rerun the VM,
review the actual full theorem types/axioms and artifact record, then update
`assurance/m2-claims.json` explicitly; no ordinary check regenerates expectations.
See [the handoff review](reviews/M2-handoff.md) for per-package acceptance and M4
obligations. M3 must supply actual workspace/runtime/network/IPC/resource policy.

Archived validation works from another checkout without the original `.tools/`
cache: recorded absolute paths describe the recording host and are checked for
one consistent layout. Current-artifact checking maps project-local paths to this
checkout and still requires recorded external compiler/runtime files. Both Lake
toolchain files are hashed, and the M2 pin must equal the preserved root pin.

## M3 workspace package and disposable VM

The versioned contract is [§FS-workspace](functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) and the implementation/effect map is
[§AR-workspace](architecture/AR-workspace.md#ar-workspace-m3-authority-model-linux-realization-and-evidence-plan). M3 has its own dependent Lake package, kernel configuration, runtime
artifact lock, helper, controller, fixtures and evidence. M1/M2 dependency pins,
theorem statements, native drivers and raw VM records are preserved.

```sh
(cd m3 && lake build LeanCageM3 leancage)
(cd m3 && lake env lean tests/integration/Workspace.lean)
python3 scripts/audit_m3.py
python3 -m unittest discover -s m3/tests/integration -p 'test_*.py' -v
```

The full gate includes these commands and compile-only native validation. The
actual declaration/type/axiom inventory is compared with `assurance/m3-claims.json`;
`.tools/assurance/m3-audit.json` records checked artifacts. The gate also compares
every generated filter byte and preserves the M2 theorem inventory. Expectations
are reviewed files, never automatically regenerated by normal checks.

```sh
python3 scripts/run_m3_vm.py --prepare
python3 scripts/run_m3_vm.py
python3 scripts/run_m3_vm.py --check-evidence
python3 scripts/run_m3_vm.py --check-artifacts
```

M3 preparation fetches checksum-pinned tools and four runtime layers into
`.tools/m3vm`, builds the separate kernel with two low-priority jobs, and stops.
The next command builds the helper/controller/image and replays all acceptance
cases in QEMU TCG with 2048 MiB, one virtual CPU, no NIC, persistent disk, host
mount or KVM. Only this VM runs shell/Python/native guest code. Layer/ELF inspection
on the host is passive; do not run the guest loader, `ldd` or helper there.

Successful replay writes `assurance/m3-vm-evidence.json`, its raw transcript and
complete image inventory. Source hashes must be unchanged across replay. The
archived mode works after a checkout move without the original tool cache; current
artifact checking additionally requires the recorded binaries. `--development`
replays exploratory changes without replacing accepted evidence. Failed replay
keeps its diagnostic transcript under `.tools/m3vm` and does not publish a passing
record. Review source/artifact changes before updating the proof manifest.

Inside the designated VM the reusable interface is:

```sh
/leancage check /api-policy.json
/leancage run /api-policy.json
/leancage report RUN_ID
```

`check` performs real preparation and cleanup without guest execution; `run`
executes the same helper and stores the report under `/m3-results/RUN_ID`;
`report` returns that stored JSON. These VM paths are examples, not host commands.
Use `profiles/m3/example-policy.json` for the exact request shape. Input snapshots
and output/export artifacts use the bounded formats in [§FS-workspace.filesystem](functional-spec/FS-workspace.md#filesystem-snapshots-aliases-and-lifetime).
The library exposes policy decoding, typed reports and invocation through
`LeanCageM3.API`; pure `validate-policy` and `emit-filter` maintenance commands can
run on the host because they never execute a workload.

The profile is a conditional model result plus native VM test evidence. Review
[the M3 handoff](reviews/M3-handoff.md) for full propositions, native mappings,
limits and the open M4/M5 work. A reported unknown is never a zero-cost success,
and an exit/cancellation does not imply completed resource release.
