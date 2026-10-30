# Development

Start with the [roadmap](roadmap.md), [agent rules](../AGENTS.md), and the contract
for the assigned task. The current boundary is [§AR-m1-launch](architecture/AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration) (M1), using
the source/launch contract in [§AR-filter-slice.contracts](architecture/AR-filter-slice.md#contracts-lean-declarations-and-downstream-ownership).
The next milestone is M2; [§RM-roadmap.next](roadmap.md#next-m1-work-packages-and-next-scope) requires selecting a bounded work package.
The workflow is specified in [§AR-tooling](architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local).

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
