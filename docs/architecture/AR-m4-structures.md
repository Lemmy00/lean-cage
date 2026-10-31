# AR-m4-structures: Local storage and result construction in the maintained source

This package connects the local storage needed by [§AR-m4-native.contract](AR-m4-native.md#contract-intended-universal-simulation-and-ownership-obligations) and
[§AR-m4-library.source](AR-m4-library.md#source-source-connections-and-completion-boundary) to [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport). It uses the pinned generated AST,
actual Clight allocation/access/assignment/free transitions and the extended
library machine. It does not alter the maintained C or silently specialize its
inputs to the desired result.

## access: Typed local and field accesses

Derive expression and full-field location certificates from actual Clight
judgments. Prove both existence and uniqueness against every actual evaluation.
Support local/global variables, struct fields, array references, pointer
arithmetic, scalar loads, casts and complete-object copies required by the slice.
Retain machine widths, alignment, access modes and bitfield designations; do not
model a structure as an untyped byte array when source semantics imposes more.
Unsupported forms remain explicit, without a catch-all success rule.

## stores: Allocation, scalar stores, copying and freeing

Construct real local allocations and typed stores from independent permissions.
Separate freshly allocated locals from existing caller/global blocks. Scalar
stores preserve permissions and outside memory. Prove completed field loads from
actual stores and disjointness; transfer those loads through the source's actual
structure assignment. Preserve the complete copied memory-value sequence,
including padding and undefined padding bytes. Structure assignment follows
Clight's alignment and permitted identical/disjoint alias cases; the separate
initialized-byte libc copy contract does not replace it.

Local returns execute actual freeing of all local blocks. Preserve caller memory
outside the declared output range, while recording local allocation/free effects.
Loss retains the exact current memory, including partially initialized locals or
partially completed source work; no final-state substitution or atomic whole-
function assumption is allowed.

## result: Complete result constructor

For `result_of`, quantify arbitrary 32-bit kind, stage, detail and entry arguments,
and actual initialized source global run ID and UID values. Own a writable,
representable, nonwrapping 144-byte output structure aligned to eight bytes, without
requiring initialized output or constraining its previous contents. The actual
pinned ABI has size 144, alignment eight, scalar field offsets checked against the
generated composite environment, and a 32-byte digest starting at offset 108.
Do not equate this internal structure layout with the 160-byte wire frame.

Execute the complete generated function, including its hidden result pointer,
fresh compound local, two global loads, all scalar/digest stores, full structure
copy and local free. Every completed local return has the supplied four fields,
loaded run/UID and zero for all other declared fields and digest bytes. Padding
is copied as memory values without asserting initialized padding. Show defined
ordinary progress at every live nonterminal prefix and useful allocated input
witnesses. Caller-continuation paths must stop at the callee return boundary;
whole-frame caller composition remains a separate result.

## evidence: Auditable source connection

Follow [§AR-m4-library.evidence](AR-m4-library.md#evidence-replay-and-retained-obligations) and [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record). Record exact complete
statements, transitive foundations, owned nonvacuity and full source bindings.
Preserve earlier checked statements and artifacts. A generic access/store lemma
alone does not complete `result_of` or a frame routine. Keep all original Linux,
compiler/runtime, bridge, interference and hardware obligations open.
