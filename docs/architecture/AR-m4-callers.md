# AR-m4-callers: Actual source call composition

This package advances the complete-source obligation in
[§AR-m4-native.contract](AR-m4-native.md#contract-intended-universal-simulation-and-ownership-obligations) and [§AR-m4-structures.access](AR-m4-structures.md#access-typed-local-and-field-accesses) for
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport). Existing helper proofs must compose with the actual
caller continuation, local environment and memory. A helper summary is not an
axiom and does not replace execution of its generated body.

## continuation: Delimited caller execution

Prove continuation replacement against the actual Clight transition relation and
the byte-aware extended machine. Preserve all local variables, temporary values,
actual call arguments, memory effects and emitted events. Replacement ends at the
callee's return boundary; subsequent caller steps require their own proof. Both
forward execution and classification of every possible step are required. Retain
all blocked calls, interruptions, partial transfers, failures and process loss.
Do not infer termination from a finite prefix or a successful witness.

## control: Source branching and helper paths

Typed call, conditional and local-return rules must certify actual evaluations,
casts, allocation/free and unique ordinary source successors. Compose the complete
byte-reader paths into callers. Bounded branching may use a decreasing bound on
nonwaiting steps, with a distinct return boundary and arbitrary self-waits; the
bound is not elapsed time. Construct all such certificates from independent
ownership and source conditions before claiming a routine complete.

## failure: Complete child-failure reporting

For the maintained `fail_child`, quantify arbitrary descriptor, stage and error
words and independently owned TLS and stable mode/name strings at their actual
source symbols. Allocate its real eight-byte local and execute both full `put32`
calls. Preserve all branches: `error_drop` sends nothing; `error_short` attempts
three bytes; other modes attempt eight bytes. The packet contains the stage and
error words in their actual little-endian representation. The observed transfer
trace, including a transfer interrupted by loss, is a prefix of the selected
packet. A write return, including failure or zero transfer, proceeds to the actual
`_exit(125)` call. Dropping a report also proceeds there. No successful-publication
or cleanup receipt follows from an exit attempt.

Show ordinary enabled progress for every live finite prefix and absence of a
return to the caller, without requiring blocked calls or repeated EINTR to
terminate. Retain process loss at every boundary and memory at that boundary.
The local buffer is not explicitly freed by this source before exit; do not
invent a free step or a Linux resource-reclamation guarantee. Construct useful
owned executions for successful, dropped, short and failed reporting, and keep
local input inhabitation separate from whole-program initialization.

## decoder: Decoder composition boundary

The complete decoder target owns all 160 readable initialized input bytes and a
separate aligned writable 144-byte output object, with stable source globals.
Header rejection precedes output construction. Later payload or tag rejection
can follow the full output assignment; record that actual mutation. Preserve all
source checks and accepted tag cases. A proof of a branch, helper or continuation
alone does not complete the decoder.

## evidence: Additive replay and claim boundary

Follow [§AR-m4-structures.evidence](AR-m4-structures.md#evidence-auditable-source-connection) and [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record). Preserve earlier
statements, foundations, compiled artifacts and raw receipts. Record caller
lemmas separately from complete routine theorems. The C-to-Lean bridge, full
slice composition, all original Linux/native obligations, compiler observation,
runtime and hardware correspondence remain open until separately checked.
