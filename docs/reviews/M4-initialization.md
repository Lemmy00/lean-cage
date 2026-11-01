# Actual initialization stores: claim review

This package implements [§AR-m4-controller.initialization](../architecture/AR-m4-controller.md#initialization-actual-flag-and-pointer-initialization) and
[§DA-m4-controller.initialization](../decisions/architectural/DA-m4-controller.md#initialization-keep-sequential-stores-visible-during-composition) from caller-string checkpoint
`572df1e49c1009e5057c2f63cf5c308bfe0923a5`, applying
[§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). The complete native helper, frontend output,
header closure, live policy implementation and toolchain pins are unchanged.
The public theorem starts at the actual export check and ends at the actual
continuation after numeric bounds or the first rejecting source branch.
Mode validation followed by its preflight assignment is a separate region.

The five connected assignments write the four-byte preflight global, the
four-byte export flag at policy offset 80, both eight-byte digest globals,
and the eight-byte argument pointer at policy offset 88. The argument pointer
is the actual argv base plus sixteen pointer cells, or 128 bytes. The proofs
use actual expression evaluation, struct-field lookup, casts, repeated argument
loads and `Mem.store`; allocation witnesses alone do not establish these source
assignments. The exact stored flags agree with the reused strict imported
`bytesEq` computation and the real Lean launch arguments.

`initialization_source` assumes a signed argument count from 17 through INT_MAX,
a matching nonempty guest list, a valid table span, initialized selected cells,
owned C strings, the actual numeric policy image, writable output cells and the
applicable register/global bindings. It requires the argument table, tree/stdin
strings and guest strings to be separate from the output globals. Guest strings
may alias one another. The export string is consumed before writes and has no
additional separation premise. Numeric policy validity and successful string
validation are not assumed. Each source certificate is constructed internally.

The combined source region checks export policy, writes its flag and both digest
pointers, checks the digest pair, writes `policy.args`, checks the executable,
accumulates argument lengths and applies policy bounds. All conforming `strcmp`
return magnitudes remain possible. Every actual step in the unchanged local
machine is classified, including arbitrary waiting and terminal process loss.
The ordinary bound is `26*N + 4540` for N guest arguments. Before crossing the
boundary, a finite execution costs at most one more, including terminal loss;
waiting has zero non-wait cost. These are not wall-clock bounds or unconditional
termination guarantees.

The memory invariant is the explicit sequence of initial, export-flagged,
tree-pointer-written, stdin-pointer-written and argument-pointer-written
memories. An early export rejection uses the initial memory; digest rejection
uses the memory after the first three writes; later rejection uses memory after
the argument pointer write. Prospective `Mem.store` results exist to describe
possible later states even on a branch that stops earlier. Only the actual
endpoint and execution trace determine which stores occurred. No rollback is
claimed. The frame relation preserves every memory permission and bytes outside
the five designated write intervals, including numeric policy fields and
literal globals. The separate mode/preflight bound is 42 ordinary steps.

The public guarantee includes an ordinary path and a split for every finite
actual execution. It either remains inside the region, with the sequential
memory invariant, bounded non-wait cost and progress or the stated endpoint,
or decomposes into a proved endpoint prefix and an arbitrary later suffix.
No invariant is extended to that arbitrary suffix. Failure reaches the original
setup/EINVAL `result_of` call, not completed publication or process exit.

Nonvacuity starts from `Genv.init_mem` of the full program, writes the ten numeric
policy cells, allocates owned strings and initializes argument cells beginning
at index thirteen. The numeric stores and allocations witness the premises;
this package does not prove that preceding native code constructed them. Lower
argv cells and whole-main entry remain outside the witness. Thirty-five combined
cases include six acceptances and twenty-nine rejections, covering both export
modes, none/digest options, both executable names, UTF-8/high bytes, argument
length/count/total-byte boundaries, first-rejection ordering and all nineteen
numeric guard conditions. Ten reused mode inputs now execute through preflight
initialization when accepted: three accept and seven reject. A separate allocated
configuration family reaches each of its four successive memories and admits
immediate loss at each one. All examples are kernel-constructed source paths,
not VM measurements.

The maintained inventory contains 81 Rocq and two Lean full theorem records,
three imported computational declaration records and twenty compiled artifacts.
The exact 161-entry axiom-free caller-string export is reused, with the unchanged
strict importer and parent checkpoint replay. Complete theorem types and
transitive foundations are archived. Declaration counts include supporting
lemmas and are not counts of independent security claims.

Thirty-eight Rocq records are closed; fourteen use the preceding four logical
foundations, twenty-five use the preceding six logical/CompCert semantic
parameters, two use only definitional UIP for equality, and two use those six
entries plus equality UIP. The imported byte equality needs equality UIP; both
imported literal lists are closed. Both Lean records use the already declared
`propext`, `Classical.choice` and `Quot.sound`. No computational axiom or new
foundation is introduced. The strict import's logical model and translation
faithfulness retain their preceding open review obligations.

The gate rejects changed source comparison literals, an argv pointer offset
changed from sixteen to fifteen elements, and a false rollback assertion after
an actual preflight store. The rollback mutation first checks an unchanged
positive control. Twelve integrity regressions reject altered parent statements,
foundations, compiled identities, imported endpoints, export closures and
unchecked proof shortcuts. The preserved caller-string checkpoint retains its
own strict-import negative controls and two rejected historical import attempts.
All previous statements, compiled identities, native/header/tool pins and raw
receipts are preserved; only named documentation and transitive evidence hashes
receive explicit amendments.

Physical argv provenance, the preceding numeric/parent composition, main entry,
reporting after rejection, setup, supervision and cleanup remain open. The local
library contract and exclusion of concurrent writers are assumptions, not libc
or Linux proofs. Strict-import translation faithfulness, compiler/runtime/linker/
loader correspondence, deployment identity, independent composed review and
hardware channels remain separate obligations. Every original correspondence
ledger entry remains open. This package advances M4.3 and completes neither the
whole controller nor M4.
