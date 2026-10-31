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

## writeall: Universal source-loop connection

The local proof target is the complete maintained `write_all` function in
the regenerated Clight AST, using the existing byte-aware machine. For arbitrary
initialized owned input bytes (including an empty request), every finite execution
must emit a prefix of those bytes, preserve the input region, and return only
zero after the entire region was transferred or minus one after zero/non-EINTR
failure. Repeated EINTR and blocked writes need no progress assumption. Loss may
occur at every source boundary or during a partial transfer, including after the
last byte or after a return; it never fabricates a successful source return.

The proof must establish defined internal steps and enabled local external
contracts at all reachable live states, independently of the always-available
loss transition. Source evaluation includes the actual errno load, unsigned
pointer/count arithmetic, branch order and function return. Ownership is a
bounded initialized buffer separated from an aligned writable errno cell;
neither a successful trace nor the desired prefix property may be a premise.
Function-symbol resolution is explicit and checked against the generated program.

The checked source submilestone is recorded in [the write-loop review](../reviews/M4-writeall.md).
`write_all_prefix_safety`, `write_all_defined_prefix` and `write_all_return_exact`
quantify over every finite execution from the actual generated function call in
`Clight.globalenv Slice.prog`. The local invocation ends at `Kstop`; connecting
it to its callers is a composition obligation. The progress theorem requires a
real source/effect step or a return, excluding wait/loss as progress witnesses.
It does not promise that an external operation returns or that retries terminate.

The ownership range is 0–160 initialized bytes with no wrapped accessed address.
The existing effect contract permits an end offset equal to the pointer modulus;
the final, unused one-past pointer may then wrap only after the count becomes zero.
No subsequent write uses that pointer. No stronger ownership assumption was
introduced to avoid this edge case. Constructive source executions cover arbitrary
bounded input, empty success, short writes, any finite EINTR retry count, zero and
non-EINTR failures, arbitrary waits and loss during any nonempty input prefix,
including the full input before a source return.

This is a named sub-result of M4.2. It neither replaces the whole selected-slice
target nor closes framing, terminal receive, the C-to-Lean bridge or any Linux,
libc, compiler and runtime obligation. Record only the propositions actually
checked, with constructive allowed/error/interruption witnesses.

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
The write-loop extension preserves every previous Rocq/Lean declaration against
`assurance/m4-writeall-baseline-claims.json`, checks that every authored Rocq module
is inventoried, and binds the new proof artifacts and receipts in
`assurance/m4-writeall-evidence.json`. Ordinary checks cannot refresh expectations.
