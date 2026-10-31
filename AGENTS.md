# LeanCage — agent instructions

## Start here

Read [README](README.md), [§RM-roadmap](docs/roadmap.md#rm-roadmap-leancage-specification-and-staged-verification-plan), the assigned specification points, and
[§REQ-proof-integrity](docs/requirements/REQ-proof-integrity.md#req-proof-integrity-never-substitute-a-weaker-claim-for-an-unfinished-proof) before changing code. M1.1 fixes the source and launch contract
boundary in [§AR-filter-slice.contracts](docs/architecture/AR-filter-slice.md#contracts-lean-declarations-and-downstream-ownership); M1.2 supplies the decoder, proofs, and
audit in [§AR-filter-decoder](docs/architecture/AR-filter-decoder.md#ar-filter-decoder-byte-decoder-proofs-and-executable-evidence-audit). M1.3–M1.5 add launch proofs, the VM-only native driver,
and reviewed evidence under [§AR-m1-launch](docs/architecture/AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration). M2 extends that baseline with [§AR-lifecycle](docs/architecture/AR-lifecycle.md#ar-lifecycle-m2-controller-native-helper-and-evidence).
M3 follows the contract [§FS-workspace](docs/functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) and architecture [§AR-workspace](docs/architecture/AR-workspace.md#ar-workspace-m3-authority-model-linux-realization-and-evidence-plan) in the
package order [§RM-roadmap.m3.packages](docs/roadmap.md#m3packages-build-the-profile-in-reviewable-slices);
read the [M2 handoff review](docs/reviews/M2-handoff.md) first. Follow the assigned M3 packages in dependency order; do not treat later M4/M5
correspondence and hardware work as completed by the M3 implementation.

All `grund` commands in the managed instructions below mean the repository-local
`./scripts/grund.sh` wrapper, run from the project root. Never substitute the older
Grund checkout elsewhere on the machine. See [development guide](docs/development.md)
and [§AR-tooling](docs/architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local) for the actual workflow.

## Specification and implementation

- Update the most-specific contract before or alongside a behavior/design change.
  Record consequential choices in the appropriate decision document. Keep spec
  behavior independent of a convenient implementation.
- Cite the relevant spec/architecture point beside code, proofs, and tests. In
  Lean use standalone `--` comments; the custom Grund profile does not promise
  complete Lean parsing. Keep stable IDs and inspect `refs` before renaming them.
- Preserve established contracts or version changes explicitly. Reject unsupported
  policy/platform features and fail closed on setup errors. Include useful allowed
  executions as well as denial cases.
- Model actual machine widths, bytes, ABI, error paths, inherited handles, aliases,
  concurrency, and adversarial interference when the assigned slice involves them.
  Exposing an obligation is better than hiding it in an informal comment.
- Reuse portable state/effect/observation interfaces under [§AR-core](docs/architecture/AR-core.md#ar-core-separate-portable-security-contracts-from-platform-mechanisms). Keep Linux
  bindings and their assumptions explicit under [§AR-linux](docs/architecture/AR-linux.md#ar-linux-connect-a-lean-launcher-to-real-linux-enforcement). Do not introduce a
  broad abstraction or policy format without a concrete milestone need.

## Proof and claim integrity

- Apply [§REQ-proof-integrity.kernel](docs/requirements/REQ-proof-integrity.md#kernel-kernel-checked-evidence) and [§REQ-proof-integrity.statement](docs/requirements/REQ-proof-integrity.md#statement-review-the-proposition). Review full
  theorem types, hypotheses, quantifiers, and transitive axioms. No `sorry`, `admit`,
  undocumented axioms, or compiler-trust shortcuts may support a security claim.
- Prove the specified property. Do not assume the conclusion, remove hostile
  transitions, use inconsistent premises, or weaken the statement to get a proof.
  Show nonvacuity and distinguish partial correctness from termination.
- Add a declaration/assumption/evidence record under [§FS-assurance.evidence](docs/functional-spec/FS-assurance.md#evidence-required-claim-record) for
  every security result. Preserve and extend the executable declaration/type/axiom
  gate in [§AR-filter-decoder.audit](docs/architecture/AR-filter-decoder.md#audit-declaration-type-and-axiom-gate) and its reviewed manifest; never refresh
  expectations merely to suppress a failure. The decoder proofs do not prove isolation.
- Keep model proofs, tests, source mappings, and deployed guarantees distinct.
  Hand translation and differential tests do not certify the original Bubblewrap
  binary. Kernel/compiler/runtime/FFI and hardware gaps remain visible obligations.
- Preserve the hardware-channel destination in [§FS-observations.hardware](docs/functional-spec/FS-observations.md#hardware-software-observable-channels). Never
  market an early functional proof as end-to-end production security.

## Workspace and collaboration

- Keep Grund and experimental tooling local to this repository. Preserve pinned
  dependencies and `lake-manifest.json`; explain and review deliberate pin changes.
  Do not modify global agent/editor settings or unrelated projects.
- Run hostile workload and OS experiments only in a designated disposable VM/test
  environment with recorded configuration. Do not change the shared host kernel,
  stop unrelated processes, or disturb active runs.
- Inspect the working tree first. Preserve others' edits and keep changes scoped.
  If collaboration is assigned, define owned files and shared interfaces before
  parallel edits. This preparation does not itself authorize spawning agents,
  sending tasks, publishing releases, or deploying workloads.
- Track source provenance and licensing. Preserve notices for copied/adapted code;
  the root Apache 2.0 license does not override upstream obligations. seLe4n is a
  later separate track, not a dependency to vendor during M0/M1.

## Handoff gate

Run `./scripts/check.sh` and the focused checks required by the changed behavior.
For documentation edits run `./scripts/grund.sh fmt --write` first; for config
changes run `./scripts/grund.sh init` first. Keep generated guidance and any
section locks consistent; edit project-specific rules outside the managed block.

Report the affected spec IDs, concrete changes, exact validation results, theorem
and artifact evidence where applicable, and remaining assumptions/obligations.
Update [§FS-assurance.status](docs/functional-spec/FS-assurance.md#status-initial-claim-register) and the roadmap only to the level the evidence supports.
Do not mark an unimplemented or unchecked milestone complete.

<!-- BEGIN GRUND MANAGED BLOCK -->
## Grounding with grund (block v39)

This project uses [`grund`](https://github.com/agent-grounds/grund): every spec, goal, decision, and end-to-end test has a stable ID `<KIND>-<slug>[.<section>]` (`KIND ∈ {GRUND, GOAL, FS, REQ, AR, DF, DA, RM}`), cited with the marker `§` — e.g. `<§>FS-user-login.3.1`, where the ID is a shape illustration rather than a real one in this repo, which is what the `<§>` escape says. Type `$$` in a grund-aware editor and it becomes `§`. Bare ID-shaped tokens are ignored — config version 2 recognizes only `§`-prefixed citations, with no opt-out.

### Grounding from a citation

A `§<ID>` is a pointer to a fact, not a file path. Resolve it with `grund` and climb only as far as needed:

- `grund <ID>` — the lead (heading-less, cut at the first child section). The cheap first read for a bare `§<ID>` citation.
- `grund <ID> --toc` — the lead plus the nested section map. Use to choose which subsection to fetch next.
- `grund <ID> --full` — the entire body. Escalate to this when narrower reads aren't enough.
- `grund <ID> --brief` — heading + first paragraph only.
- `grund refs <ID>` — every site that cites the ID; add `--summary` for one line per file. Run before renaming or moving a declaration.
  After the rename or move, edit the declaration and affected authored citation IDs, then run `grund fmt --write` from the config/project root or workspace root. When cross-reference emission applies, it re-derives generated Markdown link destinations and anchors; the root-scoped run also updates eligible section locks. Run `grund check` and `grund fmt --check`, then commit the lock changes. Locks are keyed by ID, so a file move alone does not rename one. fmt does not replace authored IDs, repair arbitrary URLs, or silently approve a protected section move; fix citations or leave a pointer for that move first. See [Maintaining declarations](https://github.com/agent-grounds/grund/blob/main/docs/user-facing/structure.md#maintaining-declarations).
- `grund list` / `grund list --kind FS,REQ` — discover IDs if you get lost
- `grund list --unused` — the declarations nothing cites yet, in one call
- `grund list --size=words --top 10` — find heavy leads and move detail into citable child points before reading them in full
- `grund list --glob '<KIND>-*' --total` — count the coordinates a pattern selects; `grund show --batch --glob '<KIND>-*' --toc --format json` then reads each one's section map in the same scan, from `.result.sections[]` (`path`, `title`, `depth`). `*` matches within one component, `**` any number of whole components, and `{a,b}` either alternative. More recipes: [Querying grund](https://github.com/agent-grounds/grund/blob/main/docs/user-facing/querying.md).

### Project map

- [GRUND](docs/grund.md): Why: project motivation
- [GOAL](docs/goals.md): Where: project direction and outcomes
- [FS](docs/functional-spec): What: behavior, requirements, and constraints
- [REQ](docs/requirements): Hard requirements: what the project must never break
- [AR](docs/architecture): How: high-level implementation, structure, and design
- [DF](docs/decisions/functional): Product behavior decisions and tradeoffs
- [DA](docs/decisions/architectural): Architecture decisions and tradeoffs
- [tests/e2e/](tests/e2e): User scenarios: behavioral test evidence
- [tests/integration/](tests/integration): Integration tests: evidence at component boundaries
- [RM](docs/roadmap.md): Planned milestones and sequencing

### Declarations and citations

Declarations are heading lines `# <ID>: …` in markdown. In a code doc-comment (Rustdoc, Javadoc, JSDoc, Python docstring, Go `//`, …) drop the `#` — write `/// <ID>: …` directly. Named sections are enabled: use explicit complete paths (`## goals: Goals`, `### goals.performance: Performance`, `### goals.3: Ordered child`) so `§<ID>.goals.performance` resolves; handles are letter-first lowercase names, and `name.number` and `number.name` are both legal; a cited address with a name under a number is recorded in the section lock. Heading depth must match each path component (an error). Purely numbered headings remain citable. In a declaration body, Markdown or doc-comment, a heading may instead write only the component it adds and take the rest from the heading one level up: `### .1: Username` under `## format: Formatting` declares `§<ID>.format.1`, the one coordinate it is cited and reported by. After citing such a heading, run `grund fmt --write` so the section lock records it, and commit the lock. Every non-declaration heading inside a Markdown declaration body must carry a numbered or enabled named section path; file titles, headings that close the body, fenced examples, non-ATX text, and source doc-comments stay exempt, while bold labels remain the non-citable alternative. One doc-comment may declare multiple IDs (e.g. an `AR-` and an `FS-` on the same class) — each gets its own body. An inline source declaration is reachable from the configured kind home via a one-line stub: `# <ID>: [<path>](<path>)`.

### Rules

- **Spec first.** For behavior or design changes, write or update the most-specific spec point before code.
- **Cite as you write.** Place `§<ID>` at the point a claim or behavior is made — on the doc-comment for a whole behavior, inline beside the clause it enforces.
- **Marker = live citation.** A `§`-prefixed token resolves and is checked wherever it appears — including inside Markdown backticks. To mention an ID without citing it, write `<§><ID>`, omit the marker, or use a fenced code block.
- **Inline citation style.** Inline notes: ≤ 1 line preferred, hard cap 3 lines; ≤ 100 columns. A note is one comment block: a blank line splits it, an empty comment line does not. Doc-comments (`///`, `//!`, `/** */`, a docstring, a Go, Ruby, shell, SQL or Lisp comment right above a definition) are documentation, not notes: they are never measured, so cite in-sentence there.
- **Always cite the most-specific point.**

### Citation directions

`must`/`never` are `grund check` errors; `should`/`avoid` are suggestions (`grund check --suggestions`). Every file under tests/e2e/ and tests/integration/ must cite one.

- Each **GOAL** declaration must cite GRUND or GOAL.
- Each **FS** declaration must cite GOAL or FS; never cite AR.
- Each **REQ** declaration must cite GRUND or GOAL; never cite AR.
- Each **AR** declaration must cite FS or GOAL.
- Each **DF** declaration must cite FS or GOAL.
- Each **DA** declaration must cite AR and FS.
- Each file in **tests/e2e/** must cite FS; never cite AR.
- Each file in **tests/integration/** must cite AR.
- Each source file outside the Project map (**code**) that cites anything should cite FS or AR.
Anything not listed above is allowed.

### Clickable citations

On repository web surfaces, link `§<ID>` to the PR branch in PR bodies, the reviewed commit in reviews, an exact commit for permalinks, and the default branch otherwise; fall back to plain when unsure. In local conversations, follow `§<ID>` with its declaration location as plain `path:line` text; fall back to the bare citation when unsure. If a user-level grund block states a local-conversation rendering, follow that instead: that machine knows what its surface can open.
<!-- END GRUND MANAGED BLOCK -->
