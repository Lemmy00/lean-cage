# AR-m4-effects: Byte-aware native effects and asynchronous loss

This package advances the revised route in [§AR-m4-native.revision](AR-m4-native.md#revision-byte-aware-effects-and-loss-before-the-lean-bridge) for
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) and the evidence requirements in [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record).
It does not complete M4.2 or the Linux/executable correspondence program.
[§DA-m4-effects](../decisions/architectural/DA-m4-effects.md#da-m4-effects-separate-byte-aware-effects-from-compcert-compiler-traces) records the event-semantics and compiler-boundary decision.

## memory: Local byte and errno contracts

Use the pinned CompCert memory and integer definitions without modifying upstream
sources. A request supplies a signed 32-bit descriptor, an owned byte region of
at most 160 bytes, and a distinct writable, aligned 32-bit errno cell. Bounds
exclude pointer wrap; the cell may share a block only when its four bytes are
disjoint from the entire request. An initialized readable region is required for
write; read requires writable permission for its entire requested region.

An effect records the actual transferred bytes, direction, descriptor, and any
errno update. Positive counts are the byte-list length and cannot exceed the
request. Read stores exactly that prefix; write loads exactly that prefix. An
error returns signed -1 and stores an arbitrary signed 32-bit errno, including
EINTR. A zero return is explicit (EOF for read). Successful/zero calls may preserve
errno or change it; no success errno is fabricated. No effect supplies an entry,
containment, cleanup or publication receipt. Local read/write contracts are not
proofs of Linux or libc behavior.

## machine: Source steps, blocked calls and loss

The new transition system delegates every non-external source step to the actual
Clight `step2`. It replaces external call boundaries with the byte-aware relation
for exactly the maintained read/write signatures and an explicit stable
`__errno_location` operation. Unsupported externals have no return transition;
this is an incomplete semantics boundary, not proof that their C paths are safe.
Neither stock external calls nor `Sbuiltin` may bypass the replacement relation;
delegated internal steps have empty traces. Unsupported builtins are also explicit
missing semantics.

A blocked external call can wait and later return, or lose the process. Every
live Clight state, including returned states, can lose the process. Loss during
a write/read may retain any bounded transferred prefix and its memory effects;
the source never resumes. Loss before and after a completed transfer are also
represented. Dead states cannot resume. Arbitrary finite interruption and wait
prefixes make no termination claim.

The transition relation is deliberately separate from CompCert `extcall_sem` and
its `match_traces`. Its events include bytes, so equal complete reply events
determine the returned value and memory. No CompCert compiler correctness theorem
is applied to this extended semantics. Its relation to Linux, compiler traces,
and the entire maintained C slice remains a proof obligation.

## lean: Exact public-result and knowledge endpoints

Check additive Lean lemmas against the existing `LeanCageM3.decodeResult`,
`resultValid`, `observe` and `launchTrace` definitions. Keep private intermediate
ADMITTED/ENTERED events separate from final public frames. Guest bytes, cancelled
work and a lost report cannot manufacture entry or release; publication failure
does not erase already observed entry. These are endpoint model lemmas, not a
translation of Rocq terms or an established C-to-Lean bridge.

## gate: Additive evidence and completion boundary

Audit full types and transitive assumptions of every new theorem, replay with
`coqchk`, and inspect the actual generated AST at the read/write/errno boundaries.
Provide inhabited memory/error/short-transfer executions and loss before/during/
after transfer, plus stale-source and tamper failures. Keep tools/build products
project-local. Run `scripts/check_m4_connection.sh`, the preserved M4.1 gate and
the full repository gate. No hostile workload runs on the shared host.

The new evidence is additive. M1–M3 source, statements, manifests, pins and VM
records stay fixed. Whole selected-slice safety and simulation, checked C-to-Lean
translation, all sixteen M2/M3 Linux/native ledger entries, linking/loader/runtime
correspondence and deployment composition remain open until separately proved.
