# M4 source submilestone: local library effects and fault selector

This author proposition review advances [§AR-m4-library](../architecture/AR-m4-library.md#ar-m4-library-local-library-effects-for-the-reporting-slice) and [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport)
from `d23fe8e37b89b721dc8b2e423b5edbbed3240ed8`. It follows [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record)
and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not the independent M4.6 review.

## Contracts and exact source result

`Library.v` supplies initialized, nonwrapping byte spans, finite NUL-terminated
strings, comparison equality and owned copying. Comparison results cover every
signed magnitude of the correct order. Copy ownership requires disjoint ranges,
allows uninitialized/unaligned destinations, and derives store existence. Loss
permits arbitrary finite byte-store orders, including repetitions and non-prefix
subsets. All partial copies preserve the source, permissions and outside memory.
`ProcessEffects.v` gives close zero/minus-one returns with optional success errno
and required error errno, exact TLS updates and outside preservation. Exit has no
source return and supplies no observed Linux cleanup/extinction receipt.

`LibraryMachine.v` injects every prior machine transition and adds only the five
exact maintained signatures. The new external events cannot occur at internal
source states or bypass unsupported builtins. Every ready boundary has an enabled
ordinary return/exit; arbitrary finite waits and loss remain possible. A completed
copy returns its destination; interrupted copies terminate with current memory.
These are explicit local semantics, not proofs of the libc/Linux implementations.

`LibraryPreservation.v` projects every relevant extended execution back to the
old source machine. This transfers universal writer/reader/write-loop safety,
rather than inferring it from a successful-run embedding. The deterministic and
store-path projection lemmas also cover the earlier errno/codec paths. All thirteen
old compiled artifacts and all 227 prior full declarations are preserved.

`Fault.v` connects the complete generated `f_fault`, including entry, the global
mode-pointer load, actual `strcmp` call and return continuation, and its final
equality test. Independent input ownership gives two actual terminated strings
and the actual initialized global mode pointer. Every completed local return is
one exactly for equal string contents, zero otherwise, with unchanged memory.
Every finite prefix preserves memory; every live nonterminal prefix enables an
ordinary source/comparison step. No output condition or successful trace is an
input premise. Useful paths take ten non-wait steps; every prefix has at most
eleven non-wait events including loss. These are model counts, not time bounds.

`LibraryWitnesses.v` builds an owned global cell at the actual source `_mode`
symbol and fresh string storage from independent permissions. Arbitrary nonzero
string pairs of combined length at most 158 are inhabited; the universal routine
has no 158-byte restriction. Equal and unequal examples have arbitrary finite
waits. The initially vacant memory is a valid CompCert memory with the chosen
next block, followed by actual allocation/stores. This proves owned local input
nonvacuity, not initialization of the full generated program. The copy witness
writes indices 2 then 0 of a three-byte destination, keeping non-prefix loss visible.

## Audit and retained boundaries

The active inventory is 323 Rocq declarations and the unchanged 12 Lean endpoint
claims, replaying 21 modules with `coqchk`. The eight new modules are `Library`,
`ProcessEffects`, `LibraryMachine`, `LibraryPreservation`, `LibraryControl`,
`GlobalReads`, `Fault`, and `LibraryWitnesses`. Nineteen evidence-gate regressions
cover inventory omissions, source/type/foundation/artifact drift, truncation,
preserved claims and invented obligation closure. The foundation/semantic-parameter
union stays at the six previously reviewed Rocq entries. No admissions, custom
axioms or trusted computation replace proofs. The generic control certificate is
constructed from actual source steps and ownership, not assumed by a public result.

`assurance/m4-library-baseline-claims.json` is byte-identical to the preceding
manifest. `assurance/m4-library-evidence.json` binds complete source/artifact
identities and raw validation logs. Earlier preservation maps change only to
propagate explicitly recorded documentation fingerprints; earlier declarations,
compiled artifacts, source/AST/tool pins and archived receipts are unchanged.
The full repository, maintained-source/connection, archived VM, formatting and
diff checks are recorded there. No fresh native workload experiment is claimed.

Frame construction/acceptance, partial rejected-frame mutation, terminal receiver
and failed publication still need source composition. Allocation, field accesses,
struct copies and caller behavior in those larger functions remain open. The
checked C/Rocq-to-Lean bridge, all sixteen original native/Linux obligations,
compiler/runtime/linker/loader correspondence, independent profile review and M5
hardware confidentiality remain open. This checkpoint does not complete M4.2–M4.6.
