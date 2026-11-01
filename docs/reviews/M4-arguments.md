# Actual guest-argument loop: claim review

This package follows [§AR-m4-controller.arguments](../architecture/AR-m4-controller.md#arguments-actual-guest-argument-length-accumulation) and [§DA-m4-controller.arguments](../decisions/architectural/DA-m4-controller.md#arguments-preserve-waits-while-connecting-length-accumulation)
from policy-bound checkpoint `a6f236ff9981b6306ff49f8168d9d9e1550f81ef`. It preserves
the native helper, live Lean policy, full frontend/header input identities,
pinned tools and all prior theorem and compiled-artifact records. This review
applies [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition) to the complete statements and their
transitive foundations.

The selected source starts at `bytes = 0`, initializes the signed index to
sixteen, executes the actual loop and reaches the subsequent policy-bound
block. The exact complete-helper AST, 4096-byte condition and first E2BIG report
call are checked by structure theorems. A compiled mutation changes the expected
4096-byte limit to 4095 and must be rejected. No replacement source listing is
trusted instead of the original frontend output.

The premises of `argument_region_source` are independent input ownership: a
signed argument count from 17 to INT_MAX, the corresponding list length, a
nonwrapping pointer-table span, readable table entries and terminated strings,
the actual initial argv/argc temporaries, and no local shadowing of `strlen`.
No valid-size or successful-run premise occurs. String pointers may alias when
the stated memory ownership is consistent. The actual signed pointer/index
arithmetic, unsigned length comparison and mixed-width addition are evaluated
in Clight. Empty strings and lengths above 4096 reject before addition.

The accumulator invariant is derived before invoking the later total-byte
check. At index i, previously accepted strings contribute at most
4097 * (i - 16). Even the signed argc maximum leaves that total below UINT64_MAX.
The per-string bound also makes each length-plus-NUL addition exact. The scan
model records the first bad index and the preceding accepted total. Acceptance
produces the exact sum of byte lengths plus one NUL for every argument.

`StringMachine` wraps the existing library machine and preserves every earlier
transition. Its sole new return effect supplies the unique owned C-string's
length without changing memory. The actual full-program `strlen` signature is
checked. At that boundary, every possible step is the exact length return, a
waiting self-loop, or terminal loss. Internal source steps still project to the
original machine, stock builtin execution stays excluded, and dead states cannot
resume. This is an explicit local libc contract, not a proof of deployed libc.

Finite path certificates are constructed from actual source steps and that
contract, and classify every transition of the extended machine. They are proof
outputs, not assumed execution inputs. `argument_region_execution` includes an
actual no-wait execution, unchanged memory for every actual prefix within its
non-wait count, ordinary progress at every earlier live prefix, the exact live
endpoint at that count, and interruption at every boundary including the last.
Waiting may be arbitrarily long. The separate first-call theorem constructs
arbitrary waiting followed by loss at a `strlen` boundary reached through the
actual initialization and first table read. No theorem assumes survival or
claims a wall-clock bound.

The argument block uses at most 26 * N + 13 non-wait steps. Acceptance ends at
the actual following bounds sequence; length rejection ends before its first
`result_of` call. `argument_bounds_source` composes that actual sequence with the
previously checked bounds block, using the computed total and preserved policy
memory. Its bound is 26 * N + 154. The same finite-path theorems give its bounded
prefix memory, progress and loss properties. Later reporting, environment lookup,
setup and supervision are outside these selected endpoints.

Nonvacuity begins with the complete translated program's constructible initial
memory. Fresh allocations and actual scalar pointer stores construct argv cells
and terminated strings while preserving previous readable memory. The composed
witnesses first populate the actual policy global using the prior scalar-store
construction. Twelve input cases contain nine successful and three rejected
length scans. Empty, valid-then-empty, 4096/4097-byte, 64/65-argument, exactly
16384/16385 total-byte, UTF-8 and raw high-byte cases are explicit. The composed
bounds block accepts seven and rejects five. A further allocated witness stores
the same shell-string pointer in two argument cells. Every selected source case
also has every-prefix loss witnesses.

Several examples deliberately isolate this selected block: a one-byte command
or raw non-UTF-8 byte does not assert that earlier executable or transport checks
would admit it. The temporary environments are constructed at the selected
source boundary. These are kernel-constructed source paths, not VM measurements
or whole-main entry-reachability evidence.

The Lean `guestSizes` projection equals the actual UTF-8 byte-list lengths of the
live argument suffix. Its recursive NUL-inclusive sum equals the live array fold,
and `argvValid` implies the recursive per-string predicate. The small exported
interface returns that predicate and reference sum over a list of natural lengths.
Its 151 declaration entries contain no exported axioms and pass the unchanged
strict importer. Rocq proofs interpret the actual imported computation and
connect its acceptance bit to the source scan. On acceptance its total is the
source total. On rejection the reference sum over all arguments is not substituted
for the source's retained prefix total. Physical UTF-8 argv storage and NUL
ownership remain explicit premises; importing lengths does not certify them.

The imported terms retain the previously reviewed definitional-UIP model and
translation-faithfulness obligation. Full transitive foundations are recorded
for all 114 Rocq and 23 Lean theorem records and the imported endpoint. The gate
`python3 m4/arguments/check.py` checks nineteen compiled identities, the complete
export inventory, twelve integrity regressions, both compiled negative checks
and independent kernel replay. The bounds checkpoint is immutable; only named
documentation and transitive evidence fingerprints are amended in active older
manifests. Earlier propositions, compiled artifacts, tool pins and raw receipts
remain preserved.

All sixteen original native/Linux obligations remain open. The sequential source
model excludes concurrent memory writers; that stability needs a whole-controller
and Linux argument. Parent, digest, export and executable checks, entry
reachability, reporting after rejection, setup/supervision/cleanup, libc and
Linux effects, compiler/runtime/linker/loader correspondence, independent composed
review and hardware channels remain unfinished. This advances M4.3 and does not
complete M4.
