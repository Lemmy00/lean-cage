# Actual caller string checks: claim review

This package follows [§AR-m4-controller.strings](../architecture/AR-m4-controller.md#strings-actual-caller-string-checks) and [§DA-m4-controller.strings](../decisions/architectural/DA-m4-controller.md#strings-preserve-library-nondeterminism-through-caller-regions) from
complete digest checkpoint `7f94dcaa517a6609144c99f4c94a7f2cd4d1083e`. It applies
[§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition) to the actual mode, export, digest-option and
executable checks in the unchanged complete-helper frontend output. It advances
M4.3 while preserving the preceding native, header, tool, theorem and artifact
identities.

The public source theorems assume independently owned argument-table cells,
global pointer cells, initialized C strings, and the applicable register values.
They construct the certificate internally. They do not assume valid input,
successful execution, a desired return or an execution-prefix bound. Signed
32-bit `argc` is modeled explicitly; the source rejects every count below
seventeen. The imported natural-number interface covers nonnegative counts in
the signed range. Negative-count rejection remains a native-source result.

The mode bytes are exactly `M3PLAN1` or `M3CHECK1`; export is exactly `discard` or
`regular-files`; executable is exactly `/bin/sh` or `/usr/local/bin/python3`.
Each digest option is exactly `none` or sixty-four lowercase hexadecimal bytes.
The checks retain actual repeated pointer reads, casts and short-circuit order.
The complete prior `digest_text` source theorem is invoked with the actual
caller continuation. A bad tree option rejects without any premise about the
stdin pointer, its string ownership or its local shadowing. A short argument
count rejects without an argument-pointer, string or library-global premise.

The original local `strcmp` semantics remains unchanged. It permits every
signed result consistent with byte order. The proofs use zero/equality and
signed-to-boolean cast lemmas instead of reducing results to minus one or one.
Each branching certificate node proves ordinary progress and classifies every
actual next transition, including arbitrary library waiting and terminal loss.
All seven literal strings are derived from the real program's initialized
memory and symbol table, rather than supplied only as abstract literal premises.

`region_guarantee` combines a constructive ordinary execution with a theorem
about every finite actual execution. An execution either remains inside the
region, with preserved memory, bounded non-wait cost and live progress or the
boundary result, or it decomposes into a proved prefix reaching that result and
an arbitrary subsequent execution. No memory or progress claim is extended to
that arbitrary suffix. This distinction is necessary because later source code
writes policy cells and publishes reports.

Success reaches the next actual main statement. Failure reaches the actual
`result_of` call with setup result 1, stage 1, EINVAL 22 and entry flag 0. It does
not prove that the error report is subsequently published or that main exits.
Ordinary source bounds are 31 steps for mode, 26 for export, 4,300 for the digest
pair and 34 for executable checking. Short-count and tree-only rejection bounds
are 8 and 2,120. Before crossing the boundary, arbitrary finite execution cost
is at most one larger, permitting terminal loss. Waiting contributes no cost;
these are not wall-clock or unconditional termination claims.

The executable check is composed with actual argument-length accumulation and
numeric policy bounds. For `N` guest arguments, its bound is `26*N + 188`.
Executable rejection stops at its own reporting call; otherwise the endpoint
is the previous argument/bounds result, including the retained prefix total on
argument rejection. Independent ownership and the actual policy image remain
premises. This composition does not establish whole-main reachability.

Nonvacuity constructs memory from `Genv.init_mem` of the full program, allocates
C strings and selected pointer-table cells, and derives all literal ownership.
For executable checking it stores the real `policy.args` field at offset 88.
For digest checking it stores both actual global pointer cells. These memory
stores are constructive witnesses, not yet proofs of the preceding caller
statements. Only the selected table cells are initialized; full physical argv
provenance is not inferred.

Thirty-six cases reach their actual acceptance/rejection boundary: mode has ten
cases (three accepted), export seven (two accepted), executable seven (two
accepted), and digest pairs twelve (four accepted). They include count extremes,
empty and high-byte strings, wrong case, wrong path, trailing bytes, both digest
alternatives and invalid length/character positions. Four additional allocated
executions reach the first real mode comparison and return 2, INT_MAX, -7 or
INT_MIN. A separate allocated witness reaches that call through exactly eight
source steps, waits an arbitrary number of times, and loses the process. The
cases are kernel-constructed executions, not VM measurements.

The strict imported root is the exact computational byte predicate. Its Rocq
interpretation agrees with all four native checks, including the pair of digest
options, and the public imported-source theorems give the same universal region
results. Every byte list has a constructive imported representation. Lean
connects the predicate to actual `nativeArgs` positions 1, 13, 14, 15 and 16;
mode and executable results use the real `argvValid` condition. Digest options
use successful results of the actual private digest-field parser, including
`none`, and have at most 64 UTF-8 bytes with no NUL. Complete JSON parsing and
physical native memory remain outside these propositions.

Two earlier strict-import attempts failed because generated sparse matchers
brought unsupported elimination checking into the closure. Adding structural
recursion alone did not resolve it. Exhaustive constructor patterns for both
list comparison and the selector produce the final normalized computation;
ordinary Lean equivalence proofs and all importer checks remain enabled.
`assurance/m4-validation-import-experiments.json.gz` preserves both rejected
sources, exact exports, import files and diagnostic reproductions.

The audited inventory contains 135 Rocq and 39 Lean full theorem records, one
imported endpoint, twenty compiled artifacts and 161 computational export
entries. The Lean records include generated equations and simplifier helpers;
these counts are not counts of independent security claims. No computational
axiom occurs in the export. All full theorem types and transitive foundation
names are retained without abbreviated proof arguments.

Of the Rocq records, 45 have no foundations, 49 use the existing six logical and
external-semantics entries, and 23 use the existing four logical entries.
Thirteen use only the four reviewed definitional-UIP instances; one equality
lemma uses only the `eq` instance; four imported-source theorems use both the
six entries and all four instances. The imported endpoint uses those four UIP
instances. Of the Lean records, twenty have no axioms, nine use `propext`,
`Classical.choice` and `Quot.sound`, nine use `propext` and `Quot.sound`, and one
uses only `propext`. No new foundation or compiler-trust shortcut is introduced.
Kernel acceptance does not establish the importer's translation faithfulness.

The gate uses `python3 m4/validation/check.py`. Twelve integrity regressions reject
missing/weakened propositions, altered foundations/artifacts, computational
axioms and unreviewed export dependencies. Three compiled negative checks reject
disabled import guards, changing the expected minimum count to sixteen, and
changing the expected Python literal to `python4`. The literal test first
compiles an unchanged positive control and then fails at the actual initial
memory load. The immutable digest checkpoint and every earlier proposition,
compiled artifact, pin and original receipt remain preserved. Only explicit
documentation and transitive fingerprint amendments affect active older manifests.

All sixteen original ledger obligations remain open. Main entry, physical argv,
parent identity, the preceding flag/pointer stores, report publication, setup,
supervision, cleanup, local libc implementation, concurrent-writer exclusion,
translation faithfulness, Linux effects, compiler/runtime/linker/loader artifacts,
independent composed review and hardware channels are still unfinished. This
package does not complete the controller or M4.
