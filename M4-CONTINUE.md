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

## Current position and first assignment

M4.1 feasibility is recorded. M4.2 has substantial reporting/framing and imported
computation proofs; translation faithfulness remains open. M4.3 has accepted local
input-validation and initialization results through `2db87b4`. The parent/numeric
composition at `80d4bbe` is a checked candidate, **not an accepted extension**.
M4.4–M4.6 and all sixteen original correspondence obligations remain open.

The next implementation agent's objective is to continue this dependency plan
toward full M4, beginning with a bounded package and preserving reviewable commits.
The first package is **repair and independently accept the composed numeric,
parent and initialization contract**. Finish at its existing post-policy-bounds
continuation. Do not extend setup while its public interface is still incomplete.
Read AGENTS.md, README.md, the proof-integrity requirement, both linked reviews,
[§AR-m4-controller.initialization](docs/architecture/AR-m4-controller.md#initialization-actual-flag-and-pointer-initialization) and [§AR-m4-controller.composition](docs/architecture/AR-m4-controller.md#composition-remaining-controller-obligations).

1. Expose the actual execution history. For every execution reaching the
   accepted initialization frontier, prove that its selected prefix contains the
   parent observation used for admission and that its signed value equals the
   parsed positive parent value. Preceding failures must make no observation;
   mismatch must retain the actual differing observation. Describe loss and
   waiting at their real boundaries. An existential admitted state independent
   of this trace, or one successful matching run, is insufficient.
2. Export the input-memory representation alongside allocated runs. Return the
   owned strings, selected argv entries and numeric mappings establishing that
   the supplied bytes inhabit the very initial memory used by the run. Reuse the
   allocation facts already constructed internally. Keep physical process argv
   provenance separate and preserve permitted aliases in universal contracts.
3. Add complete-composition allocated examples: useful acceptance; numeric
   rejection at early and late positions with earlier stores retained; invalid,
   zero, overflowing and out-of-range parent values; mismatching observations;
   export/digest/executable/argument/bounds rejection in the actual order; and
   loss before and after each meaningful write/observation region. Assert the
   exact first rejection and memory state, not only that some run exists.
4. Add compiled negative controls changing the real parent guard, narrowing or
   comparison, with an unchanged positive control. Add regressions for missing
   statements, altered foundations/artifacts/exports, fabricated history, lost
   input representation and receipt tampering. Harden Rocq declaration inventory
   against unsupported qualified/attributed commands and proof-valued definitions:
   enumerate the checked environment or reject unsupported syntax explicitly.
5. Remove or justify `parent_getppid`, the unused `export` contract parameter,
   and the self-chosen cost in `allocated_parent_decision`. Preserve the separate
   independently derived source bound. No waiting/loss result implies a time
   bound or unconditional termination.
6. Review complete statements and transitive foundations, then promote through a
   specific architecture/decision/claim record and a maintained gate. Preserve
   the original candidate and initialization snapshots; do not rewrite them into
   acceptance evidence. Record explicit documentation/dependency amendments and
   prove that preserved statements, assumptions and compiled artifacts agree.

Suggested ownership: a new maintained parent package under `m4/parent/`, its
checker/tests, additive `assurance/m4-parent-*` records, and parent-specific
architecture/decision/review documents. Coordinate shared navigation/assurance
edits. Keep `m4/parent-checkpoint/` as the frozen review input. Keep native code,
toolchain pins and VM profiles unchanged unless a separately reviewed need arises.

## Work sequence toward full M4

Each package must name its original ledger keys, exact producer and consumer
theorems, state/byte/trace relation, newly discharged edge, residual premises,
failure/interference coverage and replay command. A local proof is progress only
when its place in this chain is explicit. Do not use theorem counts as completion
percentages.

| Order | Deliverable | Acceptance boundary |
|---|---|---|
| 1 | Parent composition repair and promotion | The six requirements above, with universal failures preserved and useful allocated witnesses. |
| 2 | Whole input-validation region | Connect actual entry/profile/argc/mode/preflight, numeric/parent and initialization regions; connect rejection through existing reporting/finish proofs. Expose the owned-argv input contract and its still-open runtime producer. |
| Early, alongside 1–2 | Lean proof-connection feasibility | State and check the relation between the original Lean computational closure and the imported representation. Establish a concrete checked-certificate or semantics route to the ordinary Lean security theorem required by [§REQ-proof-integrity.kernel](docs/requirements/REQ-proof-integrity.md#kernel-kernel-checked-evidence). Typed translated terms alone do not close this edge. |
| Early, alongside 1–2 | Compiler-semantics compatibility | Relate the custom byte-aware/loss machine to the semantics required by the chosen compiler theorem, or prove the necessary compiler-pass extension. Keep frontend, headers, libc, linking and loader obligations explicit. Do not inherit stock CompCert correctness by name. |
| 3 | Controller state/effect composition | Give one explicit relation from concrete helper memory/events to the M3 state and observations. Extend through arming, resource/namespace setup, guest entry, supervision, cancellation, export and cleanup. Preserve unknown entry/cleanup, partial writes and publication failure. |
| Early feasibility, then 4 | Pinned Linux effects | Start with one complete reporting-channel path: endpoint ownership, bytes, short I/O/EINTR/EOF, loss, descriptors and concurrency. Connect the local effect contract to relevant pinned kernel source and dependencies. Continue with identities/arming, snapshotting, credentials, namespaces/VFS, filters, cgroups and teardown. |
| 5 | Executable/runtime chain | Compose compiler, native/Lean runtimes, linking/loader and actual source-to-binary correspondence for the identified deployment artifacts. Reproducible identity accompanies the proof. |
| 6 | Independent composed-profile review | Compose the advertised functional properties, replay independently, and discharge all sixteen original obligations and newly introduced connecting obligations for the retained profile. An open edge stays an explicit blocker to full M4 completion; a narrower result must be named separately. |

The early bridge/compiler/Linux tasks must produce a precise theorem interface
and an actual checked connection attempt. If a route fails, retain the attempted
goal and reproducible blocker, compare a concrete replacement, and revise the
route explicitly. Do not keep expanding dependent source proofs while treating
an unresolved central connection as routine future paperwork.

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

On the prepared local toolchains, replay the complete implemented chain with:

```sh
./scripts/check_m4_all.sh
```

This includes foundation checks, M4.1, the source/bridge/controller chain, the
frozen parent candidate, receipt-integrity regressions and M3 artifact identities.
It runs no hostile workloads on the host and performs no fresh VM replay. Hosted
foundation CI alone does not run this M4 chain. Tool/bootstrap instructions remain
in the individual package READMEs. Run checks sequentially because they share
ignored build/report directories. Future packages must extend the aggregate gate.

The original README, AGENTS, development guide and roadmap entry still point to
M4.1; some assurance/index summaries lag the accepted local work. They are bound
into frozen evidence, including the candidate snapshot. This additive assignment
supplies the current task without rewriting those historical fingerprints during
independent review. During promotion, make a dedicated navigation amendment:
add `RM-roadmap.m4.next`, retain `m4.entry` as the historical acceptance contract,
correct the current status/index links, and record each changed documentation
identity. Replay the frozen candidate at its preserved revision and the promoted
package against the explicitly amended current inputs. Do not silently refresh
the old candidate snapshot to accommodate navigation changes.

Use scoped commits on `main` after validation, preserving concurrent changes.
Work package by package toward full M4. Report a package as complete only after its
contract and gate are satisfied; continue through the remaining dependency plan
when assigned full M4. A research blocker must include concrete evidence and a
revised route, not a weaker security claim. M5 hardware confidentiality remains
separate even after M4's functional correspondence is complete.
