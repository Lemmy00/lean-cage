# M4 source submilestone: the maintained write loop

This review records [§AR-m4-effects.writeall](../architecture/AR-m4-effects.md#writeall-universal-source-loop-connection) under [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport),
[§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). Work starts from
`6510041` on `main`. The completed deliverable is a universal local source proof
for the maintained `write_all`. M4.2 as a whole and M4.3–M4.6 remain incomplete.
This is an author proof-statement/source review, not an independent security review.

## What is now proved

The earlier effect package stopped at local I/O contracts and source call-site
equations. The new proof starts at a call of the actual `Slice.f_write_all` in
`Clight.globalenv Slice.prog`, with its real argument binding and body, and ends
at the local `Kstop` continuation. `source_write_all_body` checks the complete
body equation; `actual_program_symbols` resolves write/errno against that exact
generated program. The original maintained C, extraction, preprocessed C and AST
are unchanged and still checked by the original M4.1 gate.

| Result | Exact declaration and scope |
|---|---|
| Universal prefix and memory safety | `WriteAll.write_all_prefix_safety`: for every finite execution, including loss, emitted bytes are an exact input prefix and the whole initialized input/TLS ownership remains valid. No successful execution is assumed. |
| Defined execution | `WriteAll.write_all_defined_prefix`: every reachable live state is a function return or has an enabled ordinary source/I/O/errno step. Wait and loss are explicitly excluded as progress witnesses, so an always-enabled loss edge cannot conceal an undefined C operation. |
| Exact returned result | `WriteAll.write_all_return_exact`: every source return is zero with all input bytes transferred, or signed minus one after a zero/non-EINTR reply with a strict prefix transferred. It quantifies over the actual return value and all finite effect histories. |
| Terminal loss | `WriteAll.write_all_loss_is_terminal`: a dead state has no successor. The universal prefix theorem includes partial transfer without a return and loss after full transfer or a source return. |
| Useful executions | `WriteAll.write_all_success_exists` and `WriteWitnesses.*` construct allocated arbitrary bounded bytes, empty/full success, a proper short write followed by completion, arbitrary finite EINTR retries then success, zero/error returns, and any finite wait prefix followed by partial loss. The loss witness permits the full input to have transferred without any returned write reply. |

The proof covers arbitrary descriptor bits, byte values, permitted errno changes,
short transfers, and all source boundaries. The independent ownership premises
are the original 0–160-byte initialized buffer, representable addresses, aligned
writable errno cell, and disjoint buffer/errno regions. Same-block separated
regions are permitted. The original end-at-pointer-modulus boundary is retained:
only the unused pointer after the final transfer can wrap, with remaining count
zero and no subsequent access through that pointer.

`ClightSteps.v` supplies proof certificates for actual Clight expression/statement
steps and proves both their existence and uniqueness against every corresponding
Clight transition. `WriteMemory.v` proves exact prefix/suffix loads and preservation.
`WriteAll.v` composes finite internal paths and external boundaries into an invariant
preserved by every step of the existing `Machine.step`. `WriteWitnesses.v` constructs
real source executions, rather than witnesses in a disconnected arithmetic model.
No external transition was removed and the original `IO.v`/`Machine.v` are unchanged.

The progress result is semantic definedness under the local effect interface.
It is not termination, fairness, a wall-clock bound, or a guarantee that Linux
returns from a blocked call. Arbitrarily many interruption/wait prefixes remain
possible. Function-call composition with the framer is still a separate obligation.

## Foundations and evidence boundary

The active `assurance/m4-connection-claims.json` records all 126 Rocq declarations
and the unchanged 12 Lean endpoint declarations with full types and transitive
assumptions. The previous 31 Rocq and 12 Lean records are preserved exactly in
`assurance/m4-writeall-baseline-claims.json`; the gate rejects their removal or
alteration and rejects an omitted authored Rocq module. All new terms are replayed
with `coqchk`. There is no admission, new authored axiom or native-compute shortcut.

The foundation/parameter union remains exactly the earlier six Rocq entries:
classical excluded middle, dependent functional extensionality, the two audited
constructive-real decision principles, and upstream external/assembly semantics
parameters appearing in Clight propositions. The machine continues to exclude
stock external/builtin calls; no correctness property of those abstract functions
is assumed. These are distinct from the unchanged Lean endpoint foundations.

`assurance/m4-writeall-evidence.json` records the source baseline, exact primary
claim names, checked proof artifact hashes, preserved inputs, command receipts,
observation model and remaining obligations. The original M4.1 source/tool/ABI
gate still checks all its 25 declarations, 12 Lean targets and 11 source witnesses.
The original M1–M3 native helpers, theorem records, dependencies, profiles and VM
evidence remain byte-identical. The roadmap's legacy M4.1 source hash advances
only for the explicit progress link; no old theorem expectation is refreshed.

## Validation and remaining work

The final receipt files named in `assurance/m4-writeall-evidence.json` record
Grund formatting, `./scripts/check.sh`, `./scripts/check_m4_connection.sh`,
`python3 scripts/run_m3_vm.py --check-artifacts` and `git diff --check`.
The repository gate covers 74 Python tests, 168 Lean guards and the preserved
445/274/419 M1/M2/M3 theorem inventories. The extended connection gate covers
126 Rocq declarations, 12 Lean declarations, kernel replay and 11 evidence tests.
M3 artifact revalidation checks the existing 70 artifacts and 60-case / three-API /
six-death-boundary record; this is not a fresh VM execution.

This closes the local write-loop source submilestone. The whole selected reporting
slice still needs local allocation, codecs/writes, `error_number`, frame acceptance
and rejected-frame mutation, terminal reception, failed publication and caller
composition. The checked C/Rocq-to-Lean bridge, all sixteen original M2/M3 Linux/
native obligations, GCC/Lean runtime/linker/loader correspondence and independently
reviewed deployment composition remain open. No Linux/libc effect contract has
been reclassified as foundational trust. M5 hardware confidentiality remains open.
