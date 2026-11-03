# DA-m4-routes: Expose failed central connections before expanding setup

Under [§AR-m4-routes.lean](../../architecture/AR-m4-routes.md#lean-checked-semantics-route-and-its-current-blocker) and [§AR-m4-routes.linux](../../architecture/AR-m4-routes.md#linux-pinned-reporting-channel-source-attempt), the native behavior required
by [§FS-assurance.native](../../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence) needs both an ordinary Lean semantics connection
and pinned Linux effect producers. Record actual strict-import and kernel-source
translation attempts separately from successful local source proofs.

Keep the experimental Clight port in an isolated directory at an explicit
inspection revision. It is not a maintained dependency or an alternative
compiler-correctness theorem. Preserve its license and documented semantic gaps.
Do not change existing pins or relax kernel checking to import it. Repair and
review the recursor translation before attempting full semantics equivalence.

Retain the unchanged configured Linux input and its frontend rejection. Do not
erase unsupported types, atomics, fault paths or concurrency to manufacture a
successful import. Require a checked source-refinement route and a complete
reporting-channel producer, including partial-copy failure effects. These open
edges prevent full M4 completion; the bounded parent package has its own review
and acceptance gate. Hardware-channel confidentiality remains M5.

## representations: Check the recursive representation producer

The reporting closure chain in
[§AR-m4-routes.reporting.chain](../../architecture/AR-m4-routes.md#reportingchain-required-producer-to-consumer-chain)
requires the native protocol and disclosure property of
[§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport).
Its semantics bridge must preserve the actual source representations.

### representations.recursors: Check the exported principles and every reduction

The old importer generated an outer induction principle for a nested type. The
actual exported Lean principle has a second list motive and list cases. Use
guarded dependent recursors for the actual nested and mutual types, check their
entire exported types, then kernel-check all exported constructor reductions.
An opaque helper with the right type must fail the reduction check. An unresolved
deferred recursor must fail the completion check.

Keep the accepted importer and dependency pins intact. Apply the derived patch
to a separate local copy, retain its upstream license, and recheck the resulting
compiled modules with the ordinary Rocq kernel. This bounded tool handles the
specified type representations; unsupported forms and string literals fail.

### representations.relation: Use both inverse laws and named constructor equations

Prove a total bijection between the actual imported `CC.Ty` and pinned
`Ctypes.type`, as required by
[§AR-m4-routes.reporting.types](../../architecture/AR-m4-routes.md#reportingtypes-relate-the-actual-type-representations).
Also expose equations preserving each named constructor and field. Inverse laws
alone would permit a permutation of signed and unsigned tags. Preserve the
unbounded integer and natural representations, positive identifiers, optional
fields and nested function-argument lists without adding validity premises.

### representations.boundary: Keep the original closure target

These are representation results in Rocq. They do not establish the original
Lean computational translation, expression evaluation, memory, `Clight.step2`,
Linux effects, compiler/runtime realization or a sandbox property. The original
sixteen obligations retain their existing meaning and status. Continue through
the producer chain; this package is not M4 completion.
