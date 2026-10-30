# Development

Start with the [roadmap](roadmap.md), [agent rules](../AGENTS.md), and the contract
for the assigned task. The current boundary is [§RM-roadmap.m0](roadmap.md#m0-specification-and-development-foundation); the first future
implementation task is [§RM-roadmap.next](roadmap.md#next-ready-work-for-a-future-m1-assignment). The workflow is specified in [§AR-tooling](architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local).

## Setup and checks

Use GNU/Linux with Bash, Git, curl, tar, GNU coreutils, Python 3, and elan available.
The local wrapper supports x86_64 and aarch64; only x86_64 has been exercised for
this foundation. No root access, Docker, host kernel changes, or global Grund
installation is needed. The first run needs network access to fetch pinned tools
and dependencies.

```sh
./scripts/check.sh
```

This validates Grund configuration and managed guidance, checks ordinary and full
citation scope, checks formatting, runs the documentation integration tests, and
builds the Lean library. It does not execute an untrusted native guest. The
[CI workflow](../.github/workflows/check.yml) invokes the same command on GitHub;
adding the workflow locally does not mean a hosted run has already passed.

The exact proof/tool pins are in [§AR-tooling.pins](architecture/AR-tooling.md#pins-foundation-dependencies-and-references). Lake locks the transitive
Plausible revision in `lake-manifest.json`. Keep the manifest in version control.
The M0 `LeanCage.lean` only imports Velvet; a successful build is not a sandbox
theorem. Follow [§AR-verification.audit](architecture/AR-verification.md#audit-statements-axioms-and-nonvacuity) as soon as security declarations exist.

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
specification. Later runtime tests belong under `tests/e2e/`; component-boundary
tests belong under `tests/integration/` and cite architecture contracts.

Use [§REQ-proof-integrity](requirements/REQ-proof-integrity.md#req-proof-integrity-never-substitute-a-weaker-claim-for-an-unfinished-proof) and [§FS-assurance.evidence](functional-spec/FS-assurance.md#evidence-required-claim-record) for the proof review. A future
agent handoff includes task scope, touched contracts/files, checks, proof statements,
assumptions, and remaining obligations. Claim only evidence actually obtained.
