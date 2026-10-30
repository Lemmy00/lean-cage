# AR-filter-decoder: Byte decoder, proofs, and executable evidence audit

Implement [§FS-filter-loading.input.correctness](../functional-spec/FS-filter-loading.md#inputcorrectness-decoder-proof-boundary) while preserving the ABI, canonical
program, and deterministic errors from [§FS-filter-loading.input.errors](../functional-spec/FS-filter-loading.md#inputerrors-deterministic-rejection-and-decoder-interface). This is
the pure M1.2 decoder boundary; [§AR-m1-launch](AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration) extends launch/runtime evidence
separately. [§AR-filter-slice.source](AR-filter-slice.md#source-pinned-bubblewrap-path) remains the upstream source/provenance boundary.

## decoding: Checked reads and exact reconstruction

The decoder consumes an ABI descriptor and immutable `ByteArray`. Validate ABI,
empty input, the 32768-byte ceiling, divisibility by eight, and the nine-instruction
count before reading instruction fields. Establish the resulting 72-byte size
with arithmetic, then use proof-bounded byte indices. Reconstruct words from
unsigned bytes as natural-number sums followed by explicit `UInt16`/`UInt32`
conversion. Prove these sums fit before claiming conversion correctness.

Check decoded instructions in increasing index order against the fixed reference
program. Return the first mismatch; return its single program tag only when every
field matches. This introduces no FD reads, native pointers, OS effects, or policy
compiler. A program tag alone is not evidence that some supplied bytes passed.

## proofs: Independent statement and useful witnesses

Define the input predicate using the documented byte equations and canonical
instruction fields, rather than calling the decoder. Establish soundness and
completeness for all inputs, general machine-width reconstruction, checked byte
indices, accepted count/narrowing bounds, and the first-mismatch property.
Include a concrete accepted byte snapshot to make the success statement inhabited.
Ordinary Lean terms and the pinned kernel check every proof; tests supplement them.

## audit: Declaration, type, and axiom gate

The first proof slice must include an executable gate under [§AR-verification.audit](AR-verification.md#audit-statements-axioms-and-nonvacuity).
`assurance/filter-decoder.json` records named claims and the complete theorem
inventory of every project Lean source module, including generated support.
`scripts/audit_axioms.py` first checks source/dependency fingerprints, builds the
library, and runs `scripts/axiom_query.lean` commands in that compiled environment.
The historical manifest filename now covers M1 launch declarations as well.
`assurance/m1.2-decoder-claims.json` separately preserves the original 18 full
decoder types and axiom sets; the audit requires both records to agree with the
actual environment.
For each named declaration, inspect its actual declaration, full type, and transitive
axioms from the compiled Lean environment. Fail on missing or non-theorem claims,
type drift, unrecorded security declarations, or unapproved axioms, including
`sorryAx` and compiler-trust shortcuts. Explicitly review permitted foundational
logical axioms; there are no OS axioms in this pure decoder slice.

The accepted logical axiom names are hard-coded to `propext`, `Classical.choice`,
and `Quot.sound`; a manifest cannot authorize a different axiom. Each actual set
must also equal its reviewed manifest entry. Module discovery prevents a new
project module or theorem from silently escaping the inventory. Named security
claims must be nonempty, unique, and present as actual theorem declarations.
The 18 authored decoder results are distinguished from generated support; the
inventory size is not a security score.

Bind the checked claim list to source and dependency identities, and identify the
actual checked Lean artifacts in a local evidence report. A source or artifact
hash identifies what was checked; it does not certify native compilation. Record
the exact statements, validation commands, assumptions and absent deployment
fields under [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) before reporting the result as model-proved.
[§FS-assurance.decoder](../functional-spec/FS-assurance.md#decoder-m12-decoder-claim-record) is that record; `.tools/assurance/filter-decoder-report.json`
identifies this machine's checked Lean artifacts. Regenerate evidence only after
reviewing statement/source changes; the handoff gate never refreshes expectations
automatically to make a mismatch pass.

## checks: Malformed inputs and audit failures

Run pure decoder checks for the canonical bytes, all field categories and first
mismatch precedence, unsupported ABI descriptors, and malformed/boundary lengths.
Exercise the audit's rejection of bad evidence and forbidden assumptions using
disposable fixtures. Run `./scripts/check.sh` as the handoff gate. No guest or
seccomp installation runs on the shared host. M1.4 runtime tests are isolated
under [§AR-m1-launch.vm](AR-m1-launch.md#vm-disposable-linux-profile-and-evidence) and recorded separately in [§FS-assurance.demo](../functional-spec/FS-assurance.md#demo-m14-isolated-linux-test-record).
