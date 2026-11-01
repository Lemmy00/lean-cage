# AR-m4-controller: Source connections for controller inputs and ordering

This package advances the native correspondence required by [§FS-assurance.native](../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence)
for the typed requests in [§FS-workspace.policy](../functional-spec/FS-workspace.md#policy-bounded-typed-request). Each helper connection retains
its actual machine representation, memory access and failure behavior. Local
results do not establish the complete controller or Linux enforcement.

## decimal: Native unsigned decimal fields

Connect the unchanged `number` function in `native/leancage_m3.c` to parsing a
nonempty sequence of ASCII decimal digits into an unsigned 64-bit value. Accept
leading zeros and the value 18446744073709551615. Reject empty input, non-digits,
signs, whitespace and overflow. Prove the source overflow check equivalent to
the mathematical bound, including its short-circuit evaluation order. Do not
replace its initial signed-char read with an unsigned read without proving the
relationship; subsequent loop reads are unsigned.

The input is an owned, initialized, NUL-terminated byte sequence with no earlier
NUL and no pointer wrap. State output alignment, write permission and pointer
bounds explicitly. The output may overlap the input: the function performs all
reads before its sole successful output store. On failure it returns -1 and
leaves memory unchanged. On success it returns zero and stores the exact parsed
64-bit value. Preserve all other memory and permissions, subject to that store.

Construct actual source executions from those independent ownership premises.
Characterize every completed return and finite prefix, retain asynchronous loss
at every source boundary, and prove ordinary progress before the exact return.
Include allocated separate-buffer and overlapping-buffer witnesses, valid edge
values and malformed inputs. Preserve arbitrary caller continuations in the
constructive source connection. A local finite source path does not imply that
the enclosing application survives asynchronous loss or that Linux supplied the
input bytes.

The transition relation is sequential Clight with the established loss events.
It contains no concurrent memory-writer steps; establishing that this parser runs
without an interfering writer is a controller obligation. The final `Mint64`
assignment is one source transition. Source-boundary loss does not prove atomicity
of a deployed machine store.

## extraction: Independent controller slice and evidence

Extract the maintained function without altering its tokens or behavior. Record
the source range, exact text, preprocessed input, frontend arguments, ABI and
normalized Clight output. Keep the established reporting slice, compiled proof
identities and toolchain pins intact. The slice uses the same pinned CompCert
frontend and the isolated checker profile established by [§AR-m4-bridge.profile](AR-m4-bridge.md#profile-separate-replay-and-remaining-composition).
Its wrapper must state the LP64 types and unsigned maximum used by the source.

Audit complete theorem types, transitive foundations, source identities and
compiled artifacts. Retain kernel checks and useful execution witnesses under
[§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). Source extraction and frontend acceptance are
provenance evidence, not an end-to-end compilation proof.

## composition: Remaining controller obligations

Decimal syntax alone does not establish policy bounds, the Lean plan encoder,
argument provenance or the native main routine's validation and setup ordering.
Connect those boundaries separately before claiming whole-controller behavior.
Process supervision, cleanup, descriptor inheritance, native effects, the pinned
Linux kernel, executable/runtime correspondence and hardware channels remain
separate obligations. Preserve the original obligation ledger until its stated
claims are actually discharged.
