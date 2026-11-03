# M4 continuation assignment after independent checkpoint review

Read this assignment before choosing the next implementation package. It records
the continuation from `80d4bbe5db1e0d1cc75f250df0fa32baa7738d04`, reviewed on
2026-11-01, under [§RM-roadmap.m4.packages](docs/roadmap.md#m4packages-correspondence-work-after-the-reviewed-m3-baseline) and [§REQ-proof-integrity.statement](docs/requirements/REQ-proof-integrity.md#statement-review-the-proposition).
The [independent review](docs/reviews/M4-independent-review.md) records findings,
validation and limitations. The [original handoff](docs/reviews/M4-checkpoint-handoff.md)
and its frozen candidate remain unchanged.

The destination remains reusable, end-to-end verification for actual native
Linux execution. M4 must connect the maintained controller/helper, their compiled
artifacts, runtime and relevant pinned Linux implementation to the advertised
properties of the named M3 profile. Generality grows by extending those explicit
interfaces and proofs. Tests, hashes, or additional local lemmas cannot replace
a missing connection. Hardware-channel confidentiality remains M5.

## Delivery rules for the next checkpoint

Apply this workflow at the running agent's next stable checkpoint. Continue its
work in place. Read current acceptance records and [§RM-roadmap.m4.next](docs/roadmap.md#m4next-current-m4-continuation)
before selecting an assignment. The original contract is preserved in the linked
checkpoint review; accepted work must not be restarted for a new review cycle.

For each assignment, write one short delivery contract: the behavior or theorem
that will work, the live implementation it describes, the existing consumer that
will use it, and the command that checks that integration. State the relevant
inputs and outputs explicitly. If a row below is too large for one assignment,
split at an actual producer/consumer interface and name the integrated result.
Keep one such delivery contract active per worker.

Supporting translations, lemmas, witnesses and tests belong within that work.
An assignment finishes when the result is integrated and its acceptance check
passes. A failed experiment requires a diagnosed cause and a changed approach
within the same assignment. Time-box uncertain route selection before building
more work on it; investigate alternatives rather than repeatedly replaying the
same failure. Estimates for the next delivery must come from that investigation,
not from how quickly an earlier milestone finished.

Report the actual result and its consumer, or the concrete action underway to
reach it. Keep detailed assumptions and obligation mappings in their existing
records. Do not repeat unchanged caveats or count supporting proof declarations
as delivered features. Follow [§AR-tooling.checks](docs/architecture/AR-tooling.md#checks-one-development-gate) for validation and review.

## Accepted input for continuation

The repaired parent/numeric/initialization contract is accepted in
`assurance/m4-parent-validation.json`, following the
[repair review](docs/reviews/M4-parent-independent-review.md). Reuse it under
[§AR-m4-parent.history](docs/architecture/AR-m4-parent.md#history-selected-execution-history)
and [§AR-m4-parent.inputs](docs/architecture/AR-m4-parent.md#inputs-owned-input-representation).
The original six repair requirements remain in the independent checkpoint review;
they are completed prerequisite work, not the next agent's assignment.
Preserve the original candidate and its archived evidence.

Read the current roadmap and the active worker's checkpoint before choosing the
next deliverable below. Keep current native code, toolchain pins and VM profiles
unless a concrete implementation need justifies an explicit change.

## Work sequence toward full M4

Each package must name its original ledger keys, exact producer and consumer
theorems, state/byte/trace relation, newly discharged edge, residual premises,
failure/interference coverage and replay command. A local proof is progress only
when its place in this chain is explicit. Do not use theorem counts as completion
percentages.

| Order | Deliverable | Acceptance boundary |
|---|---|---|
| Next controller delivery | Whole input-validation region | Connect actual entry/profile/argc/mode/preflight, numeric/parent and initialization regions; connect rejection through existing reporting/finish proofs. Expose the owned-argv input contract and name its runtime producer. |
| First uncertain dependency | Lean reporting proof connection | Produce an ordinary Lean theorem connecting the selected maintained helper reporting execution to the existing result decoder, with a checked relation to the semantics used by the source proof. The integrated reporting proof must consume it; importing another isolated datatype is supporting work. Identify the exact source/decoder declarations and acceptance command before implementation. |
| Before relying on compiled behavior | Compiler-semantics connection | Prove the relation between the custom byte-aware/loss machine and the semantics required by the chosen compiler theorem, and apply it to the reporting path. The executable reporting argument must consume this relation. Identify the exact compiler theorem and any needed extension before implementing dependent work. |
| After validation and its dependencies | Controller state/effect composition | Give one explicit relation from concrete helper memory/events to the M3 state and observations. Assign arming, setup, guest entry, supervision/cancellation and export/cleanup as successive integrated regions, each consumed by the next. Preserve unknown entry/cleanup, partial writes and publication failure. |
| Investigate early; integrate by effect | Pinned Linux reporting transport, then other effects | Deliver the producer for the reporting path's actual descriptors and bytes, including short I/O/EINTR/EOF, partial-copy errors, loss and interference, from the pinned kernel and runtime source. Compose it with the reporting proof. Assign subsequent snapshot, credential, filesystem, filter and resource effects separately, each with a named controller consumer and integration check. |
| After the constituent source/effect connections | Executable/runtime chain | Compose compiler, native/Lean runtimes, linking/loader and actual source-to-binary correspondence for the identified deployment artifacts. Reproducible identity accompanies the proof. |
| Final acceptance | Composed-profile verification | Deliver the composed advertised functional properties for the retained profile, with every required premise supplied by the applicable implementation connection. Replay and review the integrated result once, reusing unchanged component evidence. |

The bridge/compiler/Linux assignments require the integrated connections in the
table. Route experiments are work toward them. Record the evidence needed to
choose a route once, then pursue the implementation. Resolve a central dependency
before expanding work that relies on it. Any split must keep its consumer and
acceptance check visible in the active delivery contract.

## Original obligation coverage

The authoritative ledger remains `assurance/m4-obligations.json`; no entry is
closed by this plan. The following is a planning map, not closure evidence.

| Original keys | Required connecting work |
|---|---|
| `M4-controller`, `M4-m3-policy` | Lean request/plan bytes and physical argv provenance; complete helper/controller ordering; memory/ABI/runtime relation. Local parser and initialization proofs are reusable inputs. |
| `M4-supervisor`, `M4-m3-identities` | Parent/PID/handle provenance, reparenting/reuse, pidfd/death arming, ptrace/wait, cancellation and descendant extinction. An observed matching parent does not establish persistent identity. |
| `M4-m3-results` | Actual event/output byte provenance, concurrent ordering, public result assembly, authorized export and failed publication; compose the existing local framing proofs. |
| `M4-snapshot` | Executable/input copying, integer bounds, memfd seals, immutable checked bytes and `execveat`. |
| `M4-bootstrap` | Signals, inherited descriptors, duplication/closure and fork/clone bootstrap. |
| `M4-credentials` | Groups/capabilities/UID/GID/no-new-privileges transitions and inheritance against kernel code. |
| `M4-namespaces`, `M4-m3-filesystem` | Namespace/mount/pivot/VFS/descriptor effects, object aliases, concurrent mutation and filesystem authority. |
| `M4-filter`, `M4-m3-filter` | Emitted bytes and ABI through pinned kernel BPF interpreter/JIT behavior and filter inheritance. |
| `M4-m3-resources` | Cgroup/tmpfs attachment, accounting, limits/overshoot, scheduling assumptions and kill/extinction. |
| `M4-artifacts`, `M4-m3-artifacts`, `M4-m3-loader` | Frontend/compiler/runtime/linker/ELF/interpreter/import chain plus deployed helper, controller, runtime and kernel identities. |

## Replay, documentation and handoff

Use focused checks during implementation. When the affected scope requires the
complete implemented chain, run this aggregate once on the final relevant inputs:

```sh
./scripts/check_m4_all.sh
```

This includes foundation checks, M4.1, the source/bridge/controller chain, the
frozen parent candidate, receipt-integrity regressions and M3 artifact identities.
It runs no hostile workloads on the host and performs no fresh VM replay. Hosted
foundation CI alone does not run this M4 chain. Tool/bootstrap instructions remain
in the individual package READMEs. Run checks sequentially because they share
ignored build/report directories. Future packages must extend the aggregate gate.
Reuse a recorded pass for matching inputs; do not run its constituent gates again
just to produce another handoff. Documentation-only changes follow the lighter
checks in [§AR-tooling.checks](docs/architecture/AR-tooling.md#checks-one-development-gate).

Navigation now points to the current roadmap assignment. The preserved checkpoint
and later documentation/dependency amendments retain the historical inputs.
Workflow edits prepared during an active run must be integrated at its next stable
checkpoint, with an explicit amendment for affected documentation identities.
Preserve theorem statements, assumptions and compiled artifacts; check the
fingerprint-only diff without rebuilding unchanged proofs. The planned product
consolidation in [§AR-product.organization](docs/architecture/AR-product.md#organization-organize-the-maintained-product-by-responsibility) removes this operational-document coupling.

Use scoped commits on `main` after validation, preserving concurrent changes.
Work package by package toward full M4. Report a package as complete only after its
contract and gate are satisfied; continue through the remaining dependency plan
when assigned full M4. A research blocker must include concrete evidence and a
revised route, not a weaker security claim. M5 hardware confidentiality remains
separate even after M4's functional correspondence is complete.
