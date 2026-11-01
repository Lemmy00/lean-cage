# Complete-helper numeric initialization: claim review

This package follows [§AR-m4-controller.main-inputs](../architecture/AR-m4-controller.md#main-inputs-actual-main-routine-numeric-initialization) and
[§DA-m4-controller.main-inputs](../decisions/architectural/DA-m4-controller.md#main-inputs-replay-against-the-complete-helper-translation) from plan checkpoint
`80a192b25485c3b0839203b7e044b7b5f3a9dca7`. It preserves the native helper,
launcher, dependency pins and earlier compiled identities. The review applies
[§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition) to the full propositions and their foundations.

The pinned frontend accepts the unchanged complete helper, producing 55 function
definitions. Its recorded host headers, preprocessor inputs and LP64 ABI describe
this translation environment. This is not a proof of all 55 functions, the VM
kernel, GCC output or a deployed executable. Upstream header and tool licensing
remains separate from the new Apache-2.0 proof sources.

The full helper renames the parser's local accumulator to avoid a structure-tag
collision. The gate retains the original parser body and all sixteen maintained
proof modules, adapting only their namespace and that identifier binding. The
kernel proves exact equality with the actual full-helper `f_number`, and all 83
preceding decimal propositions and transitive foundation records must match
modulo namespace. A compiled negative mutation changes a parser constant and
must fail this equality proof. No alpha-equivalence or parser correctness is
assumed at this boundary.

The new 107-declaration inventory checks the actual policy global and parser
binding, 96-byte structure layout, all field offsets, ten pointer initializers,
unsigned loop/index arithmetic and actual argument/field-pointer reads. The
source path contains the real calls, their returns, result tests and increments.
`numeric_region_source` constructs this path from independent memory and local
environment premises; neither an execution nor its desired outcome is a premise.

`numeric_values` is the exact successful prefix of the decimal results. On
success, all ten stores have occurred. On rejection, the earlier successful
stores remain and the rejected field performs no store. The endpoint is before
the first `result_of` call in that failure branch, or at the continuation after
the numeric loop. No reporting, final return or later validation effect is
assumed. `fields_first_rejection` identifies the first rejected input and the
complete preceding accepted prefix.

`numeric_region_memory` permits precisely a prefix of the actual field-pointer
initialization, followed by a prefix of the policy stores. Memory outside the
80-byte field array and first 80 policy bytes is preserved. In particular, the
export flag and argument pointer at policy offsets 80 and 88 are outside these
numeric stores. The argument table and input strings must be separate from both
write regions. Read-only input strings may alias each other; the standalone
parser's broader input/output-alias result is retained in its replayed inventory.

All actual finite executions whose event count is within the constructed path
retain the prefix invariant, and live prefixes before its end have a defined
next source step. A live execution of exactly that length reaches the constructed
endpoint. Loss can occur at every boundary, including the endpoint, preserving
the actual intermediate memory. These bounded statements do not restrict what
unproved code can do after the selected endpoint, assume survival, or certify a
deployed store's atomicity. The semantics remains sequential, without a
concurrent memory-writer transition.

Nonvacuity includes existence of the complete translated program's initial
memory, derived from checked initializer alignment and symbol references. The
allocation theorem then constructs a packed string block, the 80-byte local
field-pointer array and a 96-byte argument table, retaining every allocation and
store relation. Argument slots 2–11 are initialized for this selected block;
slots used by earlier or later code are not inferred. Local environments are
constructed for the block, not claimed reachable from the function-entry rule.

Sixteen allocated source witnesses include a vector meeting the ordinary numeric
policy bounds, leading zeros, UINT64_MAX, malformed/overflow fields, and empty
input at every field position. Three vectors finish the numeric block; thirteen
stop at rejection. The maximum-value vector is a numeric-parser case, not a
policy-bounds acceptance claim. These are kernel-constructed source executions,
not native workload measurements.

`numeric_region_imported_source` connects the stored vector and completion
decision to the strictly imported numeric byte interface from the plan package.
It retains explicit argument ownership and the importer's existing logical-model
and translation-faithfulness obligations. The live Lean layout/UTF-8 proofs
remain in the preceding 32-Rocq/88-Lean checkpoint; no new runtime-provenance
claim is inferred from that pure representation connection.

`python3 m4/main/check.py` checks every full theorem type and transitive foundation,
the exact full-function identity, all 83 adapted records, source/header/tool
identities, twelve integrity regressions, the compiled negative mutation and an
independent kernel replay. The manifest records the 107 new statements separately
from the 83 replayed statements and the function-identity theorem. Earlier claim
records, compiled artifacts and archived receipts remain unchanged; explicit
documentation amendments account for transitive source fingerprints.

Reachability through `check_profile` and the mode checks, physical Linux argument
memory, parent validation, later policy bounds, all remaining controller effects,
supervision and cleanup remain open. All sixteen original native/Linux ledger
entries, the executable/runtime chain and hardware-channel obligations remain
open. This advances the bounded M4.3 connection and does not complete M4.
