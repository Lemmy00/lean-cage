# M4 source submilestone: complete result constructor and local storage

This author source/proposition review advances [§AR-m4-structures](../architecture/AR-m4-structures.md#ar-m4-structures-local-storage-and-result-construction-in-the-maintained-source) and
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) from `7bfcdd38b277d2891177c872bb2fd2bda8730cee`.
It follows [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not
the independent composed-profile review; M4.2–M4.6 remain incomplete.

## Exact source and memory result

`ResultSource.result_construction_source_path` follows the complete maintained
`f_result_of`: function entry and hidden result pointer, allocation of its compound
local, both source-global loads, fifty scalar/digest initialization stores,
complete-object assignment and local free. The path has 161 actual Clight steps
and accepts an arbitrary caller continuation, stopping before that caller resumes.

`ResultSafety.result_source_execution` constructs this path from independent
ownership: arbitrary 32-bit kind/stage/detail/entry arguments, actual initialized
global run ID and UID, and a writable aligned nonwrapping 144-byte output region.
Output initialization is unnecessary. The output may alias existing global memory;
the global reads occur before copying, while the fresh local cannot alias any
previously valid block. No successful store/path/desired output is a public input.

`result_return_exact` quantifies every completed local execution in the extended
library machine. The output has the four supplied arguments and loaded run/UID;
all other declared scalar fields and all 32 digest bytes are zero. It exposes the
exact 161-event source trace, unchanged caller memory outside the output and an
actual free of the fresh local. `result_freed_local_has_no_permission` excludes
all permissions in the freed local. `result_all_prefixes` preserves caller memory
outside the output for every finite run, with at most 162 events including loss.
`result_defined_prefix` requires an enabled ordinary source step or the exact
completed result. `result_loss_every_prefix` retains the actual interruption
memory at every source boundary. These bounds count model transitions, not time,
assembly instructions or scheduler progress.

`ResultLayout.result_abi_layout` checks size 144, alignment eight and every field
offset against the actual generated composite environment. The digest begins at
108. This internal structure is distinct from the 160-byte frame. Padding is
copied as actual memory values, without claiming that padding is initialized.
Clight performs the structure assignment in one source step; finer compiled-copy
interruption behavior is a compiler/observation refinement obligation.

## Reusable mechanisms and nonvacuity

`LocalAccess.v` derives actual expression/location evaluation and uniqueness,
including local/global/field accesses, scalar assignments, structure assignments,
function entry and return freeing. `ScalarMemory.v` constructs typed store chains
from independent permissions, preserves outside memory and permissions, derives
exact disjoint field loads, and transfers those loads through an actual complete
memory-value copy. These are proofs about actual Clight and CompCert memory, not
an unverified interpreter replacing the source semantics.

`ResultWitnesses.v` allocates actual cells for the generated run-ID/UID symbols,
stores arbitrary words, and allocates an uninitialized output. It constructs an
actual successful source execution for every combination of argument/global
words. Initial vacant memory and empty intervening allocations demonstrate local
input inhabitation; they do not establish whole-program initialization.

## Evidence and remaining work

The active audit contains 373 Rocq declarations and the unchanged 12 Lean endpoint
claims. All prior 323 full declarations/assumptions and all twenty-one compiled
artifacts are preserved. The six new modules are `LocalAccess`, `ScalarMemory`,
`ResultLayout`, `ResultSource`, `ResultSafety`, and `ResultWitnesses`; all 27 modules
are replayed with `coqchk`. Twenty-one gate regressions reject omitted modules,
truncation, source/type/foundation/artifact drift and invented obligation closure.
No admissions, custom axioms or trusted computation support these statements.
The previously reviewed six-entry foundation/semantic-parameter union is retained.

`assurance/m4-structures-baseline-claims.json` preserves the exact previous
manifest. `assurance/m4-structures-evidence.json` binds source identities, compiled
artifacts, full declarations, preservation audits and raw command receipts.
Only explicit documentation fingerprints and their transitive evidence manifests
are amended; old proof records, native/extracted/preprocessed source, generated
AST, tool pins and VM receipts remain unchanged. An initial isolated replay checked the same 373 declarations but rejected
compiled-artifact identity: Rocq artifacts embed the source checkout path. The
strict artifact expectations are preserved, and final validation uses the canonical
checkout after concurrent product documentation was committed as `605e89d`.
That documentation is retained; its architecture-index fingerprint is included
in the explicit amendment. The isolated rejection and rerun are archived.

Frame construction, acceptance and partial rejected-frame mutation, terminal
reception, failed publication and caller composition for the larger routines
remain open. So do the checked C/Rocq-to-Lean bridge, all sixteen original
native/Linux ledger entries, libc/Linux interference, compiler/runtime/linker/
loader correspondence, independent composed-profile review and M5 hardware
confidentiality. No fresh VM or shared-host workload is claimed.
