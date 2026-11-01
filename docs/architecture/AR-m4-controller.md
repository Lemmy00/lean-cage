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

## main-inputs: Actual main-routine numeric initialization

Translate the unchanged complete native helper with the pinned frontend and
record every preprocessor/header input, ABI option and resulting function. This
is provenance for the selected source semantics, not a proof of all functions or
of the deployed binary. Preserve upstream notices and identify the host-header
environment separately from the pinned VM kernel.

Connect the ten numeric-field pointer initializers and their parsing loop to
their actual statements in `main`. Check the policy structure layout and the
actual global binding of `number`. A frontend-renamed local identifier must be
handled by replaying the existing parser proofs against the full-program AST,
with a kernel-checked function identity; textual resemblance is insufficient.

Start at the numeric initialization block with independently stated local,
global and argument-memory premises. Construct its real source path: read each
argument and field pointer, call the actual parser, retain each successful
store, and stop before the first failure-reporting call or after all ten fields.
On a later rejection, earlier stores remain. Do not assume an atomic plan
commit or the success of the reporting routine. Prove that loop indices and
pointer offsets fit their actual machine widths. Preserve all memory outside
the initialized field-pointer array and selected policy cells.

State the separation needed to preserve the argument table and input strings
across those stores. The standalone parser permits input/output overlap, but
composition must not silently reuse stale input bytes after a prior field
write. Retain source-boundary interruption and intermediate memories, useful
allocated executions, malformed fields and rejection after a successful prefix.
Connect the stored vector and stopping decision to the imported numeric byte
interface from [§AR-m4-controller.plan](AR-m4-controller.md#plan-live-lean-plan-fields-and-their-decimal-bytes), retaining its existing translation
faithfulness obligation and the separate physical argument-memory premises.

This local connection does not establish reachability from Linux process entry,
`check_profile`, the mode checks, parent identity, later policy bounds or setup
effects. Account for those separately before extending the controller claim.

## bounds: Actual policy-bound validation

Connect the unchanged `main` block that checks guest argument count, accumulated
argument bytes and all nineteen numeric limit conditions. Use the complete
helper translation from [§AR-m4-controller.main-inputs](AR-m4-controller.md#main-inputs-actual-main-routine-numeric-initialization). Prove the actual signed
argument subtraction, unsigned 64-bit comparisons, boolean casts and modulo
operations, including the long constant used for the CPU upper bound.

Start with an independently supplied argument count in the admitted signed range,
an unsigned accumulated byte count and readable policy cells. Preserve the
source's short-circuit order: once a condition rejects, later policy fields are
not read. Construct both successful and rejected source paths. Success ends
before the subsequent environment lookup; failure ends before its first report
call. This block changes temporary registers only, so every source prefix must
preserve the entire memory, including under loss. Establish a finite source-step
bound and defined progress up to the selected endpoint.

Relate the complete numeric predicate to the live Lean `limitsValid` contract and
its serialized fields. Keep the fixed CPU period separate because the native
argument vector omits it. Relate the argument-count and byte-total conditions to
the corresponding parts of `argvValid`; do not infer executable allowlisting,
per-string bounds, NUL exclusion or the preceding accumulation loop from those
two conditions. Any imported computational interface must retain the strict
translation and logical-model obligations from [§AR-m4-controller.plan](AR-m4-controller.md#plan-live-lean-plan-fields-and-their-decimal-bytes).

Include accepted boundary vectors and a rejected case for every condition, with
allocated readable policy memory. Compose the numeric stores with the readable
policy image without assuming the desired limit result. Reachability across the
intervening parent, digest, export and argument checks remains an explicit
obligation until those actual source regions are connected.

## arguments: Actual guest-argument length accumulation

Connect the unchanged complete-helper block that initializes `bytes`, iterates
from argument sixteen to `argc`, calls `strlen`, rejects an empty or overlong
string, and adds the accepted length plus its terminating NUL. Use the actual
signed index, pointer arithmetic and unsigned 64-bit addition. Derive absence of
arithmetic wrap from the signed argument-count bound and the per-string check;
the later total-byte rejection is not an available premise for this loop.

Start from independently owned argument-table cells and terminated byte strings,
with explicit pointer-span bounds. Allow aliases consistent with that memory.
The local `strlen` contract returns the unique owned string's byte length and
leaves memory unchanged. Extend the preceding effect machine conservatively:
retain its transitions, arbitrary waits at the library boundary, and loss at
every source and effect boundary. Do not use stock external execution as a
second path around the local contract. Its correspondence to deployed libc is
an open obligation.

Construct both accepted and first-rejected source paths from ownership alone.
Acceptance establishes the exact accumulated byte count; rejection stops before
the first `E2BIG` report call and retains the total of preceding valid strings.
Prove unchanged memory, defined progress for every live prefix before the chosen
endpoint, and the exact endpoint for every execution with that number of
non-wait steps. A finite bound on those steps does not bound library waiting or
establish survival. Compose the accepted block with
[§AR-m4-controller.bounds](AR-m4-controller.md#bounds-actual-policy-bound-validation), preserving the actual intervening source control.

Include allocated accepted and rejected strings, empty and 4096/4097-byte
boundaries, argument-table aliasing, and interruption witnesses. Relate the
computed total and per-string predicate to live `argvValid` without inferring
the separate executable allowlist, parent/export/digest validation, physical
Linux argument provenance, or reachability through all preceding main code.
Export the structurally recursive length predicate and NUL-inclusive total as a
strict computational interface. Prove its agreement with the actual imported
terms and source loop. Audit the live Lean string-to-length and array-fold
connections separately; the import does not certify physical UTF-8 storage or
the libc implementation.
This implements the argument part of [§FS-workspace.policy](../functional-spec/FS-workspace.md#policy-bounded-typed-request) while leaving the
whole-controller obligations explicit.

## digest: Actual lowercase digest-text validation

Connect the unchanged complete-helper `digest_text` function to exactly sixty-four
ASCII lowercase hexadecimal bytes. Start from an independently owned terminated
byte string, including malformed lengths and characters. Execute the actual
`strlen` call, unsigned loop index, signed-character loads, short-circuit tests
and first rejection. Preserve every repeated character read in the source;
high-bit bytes must reject under the actual signed-char ABI.

Use the conservative string-effect machine from
[§AR-m4-controller.arguments](AR-m4-controller.md#arguments-actual-guest-argument-length-accumulation), retaining arbitrary waiting and loss. Construct
actual function-entry-to-return paths with arbitrary caller continuations.
Prove unchanged memory, defined ordinary progress at live prefixes, and the exact
zero or one return. For an isolated function call, characterize every execution
and completed return, including loss after return; do not impose a prefix bound
as a premise of that whole-function result. State finite non-wait bounds without
asserting termination in the presence of waiting or loss.

Connect an exact, strictly imported byte predicate to that source behavior, with
separately checked Lean representation facts. Show that a successful `some` result
of the actual live `digestField` yields the checked digest suffix, and connect
that suffix to its UTF-8 bytes and existing plan positions. Preserve the original
live policy and its digest encoding. Do not infer validation of the enclosing JSON object,
physical argument memory, the special `none` spelling, the caller's conditional
checks, digest authentication, SHA-256 correctness or file contents from a
digest-text syntax result. These are separate parts of [§FS-workspace.policy](../functional-spec/FS-workspace.md#policy-bounded-typed-request) and
the controller composition. Include allocated accepted, malformed-length,
uppercase, boundary-character and high-byte executions, plus arbitrary-wait and
every-prefix loss witnesses. Retain the explicit sequential-memory and libc
correspondence obligations.

## strings: Actual caller string checks

Connect the main routine's mode, export-policy, digest-option and executable
checks to their exact byte conditions under [§FS-workspace.policy](../functional-spec/FS-workspace.md#policy-bounded-typed-request). Reuse the
unchanged complete-helper AST, its global layout and the string machine from
[§AR-m4-controller.arguments](AR-m4-controller.md#arguments-actual-guest-argument-length-accumulation). The digest options accept exactly `none` or the
syntax proved in [§AR-m4-controller.digest](AR-m4-controller.md#digest-actual-lowercase-digest-text-validation). Export names are exactly `discard`
and `regular-files`; executable names are exactly `/bin/sh` and
`/usr/local/bin/python3`. Mode accepts `M3PLAN1` or `M3CHECK1` only after the
actual minimum-argument-count guard. Preserve source short-circuiting and all
repeated pointer reads.

The local `strcmp` contract permits every negative or positive signed result
consistent with byte order, not just minus one or one. Derive boolean decisions
from the exact zero/equality relation. Retain arbitrary library waiting and
process loss, including at calls into the already checked digest recognizer.
Construct selected-region certificates from independent argument-table,
pointer-cell and C-string ownership. Every actual transition before the selected
boundary must be covered. An arbitrary execution either remains a bounded live
prefix or has crossed the proved accept/reject boundary; later source behavior
must not inherit the region's memory claim. Provide actual ordinary execution
witnesses and finite non-wait bounds without claiming termination under waiting
or loss. Derive literal bytes from the actual program's initial memory.

Accepted branches reach their real source continuation. Rejected branches reach
the actual `result_of` call with its setup-stage error arguments; this does not
claim completed report publication or exit. Keep preceding pointer stores,
whole-main entry, physical argument provenance, parent identity, later effects,
concurrent writer exclusion and libc correspondence explicit until separately
connected. Allocate both accepted and rejected witnesses, cover digest-option
short-circuit cases and arbitrary `strcmp` result magnitudes, and reject a
compiled mutation of an actual source constant. Preserve the complete digest
checkpoint and its earlier proof and artifact inventories.

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
