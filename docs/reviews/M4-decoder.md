# M4 source submilestone: complete private-frame decoding

This author source/proposition review advances [§AR-m4-decoder](../architecture/AR-m4-decoder.md#ar-m4-decoder-complete-private-frame-decoding-from-owned-bytes) and
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) from `2beffca736f25d4d229fb5ba6fd4eb8882b4ee4d`, following
[§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not the
independent composed-profile review. M4.2–M4.6 remain incomplete.

## Independent ownership and actual source

`DecoderInput.decoder_input` owns arbitrary initialized 160-byte input, an
aligned nonwrapping writable 144-byte output, and the actual source globals.
Input and globals read after output assignment must survive that write.
Disjoint ranges within one block are allowed. No valid header, accepted tag,
successful return, desired comparison result or source execution is assumed.
`decoder_memories_exist` derives fresh local allocation, all scalar stores,
complete typed structure assignment and both actual free outcomes from those
permissions. Padding remains arbitrary memory values.

`DecoderAssembly.decoder_after_comparison_source` composes the real header
checks, byte readers, both reserved-byte loops, result construction, common
payload checks, switch cases and actual returns. `ComparisonControl` and
`ComparisonRuns` classify every actual comparison step/history with arbitrary
signed nonzero comparison results, arbitrary waits and loss. The equality result
is derived from the first four owned frame bytes and actual magic literal.
`DecoderProgram.decoder_source_connection` constructs the entry and all later
source behavior from the independent input contract.

## Whole-function propositions and mutation

`DecoderProgram.decoder_whole_source_guarantee` gives preservation and ordinary
enabled progress or an exact return at every finite live prefix of the entire
function. `decoder_all_returns` states the exact return word from the complete
byte-level `decoder_accepts` predicate. A failed header leaves all previously
valid caller memory unchanged. A passed header writes all decoded/zero fields
before payload validation, so later rejection retains that constructed output.
This is the source's partial mutation behavior, not a transactional decoder.
The private parser accepts tags 0, 1, 2, 4, 5, 6 and preflight-gated 7 with their
actual constraints. It remains distinct from the public Lean parser.

`decoder_all_prefixes` preserves old memory outside the output even after loss.
`decoder_freed_local_has_no_permission` records actual local free on every
return. `DecoderRuns` supplies ordinary finite return runs for every owned
input, arbitrary comparison waits followed by loss, and loss from every live
prefix with the current memory. Enabled progress and existence of a finite run
do not imply termination under arbitrary waits or scheduling.

`DecoderAllocation.arbitrary_decoder_source_input` allocates the actual source
magic/run/UID/preflight blocks, arbitrary input bytes and independent output.
`DecoderWitnesses.every_accepted_tag_executes` covers all seven accepted tags.
Early and later rejection witnesses execute the entire source and establish
the respective preserved/constructed memory outcomes. These witnesses are local
owned inputs, not whole-program initialization or execution of a Linux binary.

## Dependency-closure correction

Review found that the caller checkpoint's 48 named modules imported fifteen
historical module names from ignored local build files. Its local kernel replay
passed, but the maintained source inventory did not include that dependency
closure. The exact fifteen sources are now maintained under `m4/connection/compat`
and compiled before their callers. All 73 declarations and compiled identities
are added to the audit. The `Draft` suffix preserves historical module identities
already printed in the frozen theorem types; these are complete checked proofs.

The gate rejects undeclared or unordered project imports, inventories every
maintained proof including compatibility files, and preserves the earlier query
context for exact full-statement printing. This correction does not weaken or
replace preceding claims. All 494 earlier Rocq records, 12 Lean records and 48
compiled artifacts remain exact. New decoder modules use maintained names.

## Replay and remaining obligations

The active inventory contains 680 Rocq declarations across 91 modules: 494
preceding records, 113 decoder/composition records and the 73 historical import
records. `assurance/m4-decoder-baseline-claims.json` is the byte-exact previous
manifest. `assurance/m4-decoder-evidence.json` binds full types/foundations,
sources, compiled artifacts, compatibility identities and raw validation receipts.
The gate replays the maintained-source/frontend/tool checks, complete compilation,
`coqchk`, full declarations, Lean endpoints, import-closure regressions and the
repository gate. The extended replay budget is ten minutes; individual prover
and kernel-check limits and all semantic checks remain enforced.

Frame sending, `finish`, terminal reception and whole-slice caller composition
remain open. So do the checked C/Rocq-to-Lean bridge, all sixteen original
native/Linux entries, libc/Linux interference, compiler observation/refinement,
executable and runtime chain, independent M4.6 review and M5 hardware channels.
No native helper, extracted AST, tool pin, VM/kernel profile or hardware guarantee
is changed by this package.
