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

## plan: Live Lean plan fields and their decimal bytes

Connect the actual `LeanCageM3.planArgs` implementation to its complete argument
layout: mode, ten numeric limits, parent PID, export choice, both optional digest
texts and the unmodified guest argument suffix. State the one-position shift
when an executable name is prepended, without assuming that a proof of this pure
array operation certifies `IO.Process.spawn` or Linux's argument memory.

Prove the actual `toString`/UTF-8 representation of natural numbers contains only
ASCII digits, is nonempty, has the expected mathematical value, and has at most
twenty bytes for an unsigned 64-bit value. Valid policy limits must fit that
range; the fixed CPU period is a separate policy condition and is not one of the
ten serialized numeric arguments. The parent PID's encoding has the same decimal
contract, while its positivity, signed-PID range and kernel identity remain
native-controller checks.

Use a small, exact numeric byte interface whose accepted values are precisely
nonempty digit sequences within a supplied bound. Prove in Lean that the live
encoded fields satisfy it. Import its computational definition with the existing
strict profile, prove its exact relation to `number`, and compose that relation
with actual source executions, owned memory, successful stores and every-prefix
loss. An input equal to the encoded bytes is a representation premise, not a
claim that the OS has supplied those bytes.

Retain malformed and overflow examples as well as useful accepted plans. Keep
the imported terms, full proposition/foundation inventory and earlier compiled
identities auditable. The importer's translation faithfulness and logical-model
review remain open; a checked translated term alone does not discharge them.

## composition: Remaining controller obligations

Decimal syntax alone does not establish policy bounds, argument provenance or
the native main routine's validation and setup ordering. The plan connection in
[§AR-m4-controller.plan](AR-m4-controller.md#plan-live-lean-plan-fields-and-their-decimal-bytes) does not prove that the native main routine
calls the parsers in that order or establishes their ownership premises.
Its ten numeric stores occur sequentially: a later validation failure may retain
earlier stores. Do not replace this with an all-or-nothing initialization claim.
Connect those boundaries separately before claiming whole-controller behavior.
Process supervision, cleanup, descriptor inheritance, native effects, the pinned
Linux kernel, executable/runtime correspondence and hardware channels remain
separate obligations. Preserve the original obligation ledger until its stated
claims are actually discharged.
