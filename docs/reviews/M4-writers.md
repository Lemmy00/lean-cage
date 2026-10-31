# M4 source submilestone: byte writers and codec round trips

This author source/proposition review advances [§AR-m4-effects.writers](../architecture/AR-m4-effects.md#writers-byte-stores-and-source-codec-round-trips) and
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) from `ad71f8f729c08901b6208fd2c22e942f90b9a836` on `main`.
It follows [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not
an independent composed-profile review. M4.2–M4.6 remain incomplete.

## Exact checked behavior

`Writers.v` executes the complete generated `f_put32` and `f_put64` bodies.
The independent premise supplies four/eight writable bytes and excludes pointer
wrap. It requires neither initialized contents nor word alignment. All 32/64-bit
input words are quantified. Constructed source paths allow any call continuation;
the universal local-execution results use `Kstop` and end before a caller resumes.

| Function | Ordinary source steps | Maximum including loss | Exact completed memory |
|---|---|---|---|
| `put32` | 42 | 43 | Four little-endian bytes of the input word |
| `put64` | 74 | 75 | Eight little-endian bytes of the input word |

`writer_all_prefixes` establishes that every finite execution has the memory of
an actual prefix of these byte stores. `writer_prefix_content` exposes its exact
bytes, unchanged memory outside that prefix, and equivalence of all permissions.
`writer_defined_prefix` requires an enabled source step or the exact void return;
loss cannot serve as a progress witness. `writer_return_exact` requires all bytes
and the exact source trace at any return. These are model step counts, not elapsed
time bounds or machine-instruction counts.

`StoreSteps.store_path_all` classifies every transition of the unchanged machine
as the unique actual source successor or terminal loss. It retains the memory at
the interruption point. `put32_first_byte_loss` constructs the actual nine-step
prefix followed by loss with only the first byte stored; no whole-word atomicity
is assumed. The arbitrary-word allocation witnesses include fresh uninitialized
buffers and a shared unaligned offset-one witness for both writer widths.

`CodecRoundtrip.put_get32_word` and `put_get64_word` prove exact word identities
for every input using CompCert bit semantics. `put32_reader_input` and
`put64_reader_input` derive actual readable source inputs from completed stores.
The two `source_roundtrip` theorems then connect every completed writer to an
actual completed reader and classify every completed reader result as the original
word. Separate local invocations expose a reusable caller interface; they do not
certify the control flow or memory allocation of `send_frame` or `decode_frame`.

## Proof integrity and evidence

The active inventory contains 227 Rocq declarations and the same 12 Lean endpoint
claims. All previous 173 Rocq and 12 Lean full types and transitive assumptions are
preserved exactly in `assurance/m4-writers-baseline-claims.json`. All nine old
compiled connection artifacts are preserved. The four new modules are
`StoreSteps`, `WriteBytes`, `Writers`, and `CodecRoundtrip`; all 13 modules are
replayed with `coqchk`. The audit rejects omitted modules, truncated declarations,
source/statement/assumption drift and fabricated closure.

The memory predicate on internal path certificates is derived from independent
ownership by constructing actual `Mem.store` chains. No desired output, successful
trace, custom axiom, admission or compiler shortcut is a public premise. The
foundation/semantic-parameter union stays at the six previously audited Rocq
entries. Stock external and builtin transitions remain excluded, and no property
of those abstract semantics parameters is used to justify an external operation.
Three memory identities are reproved using proof irrelevance derived from the
already-declared classical excluded middle, avoiding the upstream memory helper's
additional `Axioms.proof_irr` parameter. Their upstream LGPL notice and provenance
are retained in `WriteBytes.v` and `m4/connection/LICENSES.md`. The earlier Lean
endpoints and their axioms are unchanged.

The additive `assurance/m4-writers-evidence.json` records primary claims, exact
source/artifact identities, command receipts and remaining obligations. The
roadmap-only legacy fingerprint amendment is explicit; old theorem expectations
and archived receipts are preserved. The original native source, extraction,
Clight AST, tool pins, M1–M3 proofs and VM artifacts remain unchanged.

## Validation and continuation

Required checkpoint validation is the full repository gate, the M4.1 plus
connection gate, the preserved M3 artifact check, Grund formatting and diff checks.
The connection gate inventories all 227 Rocq / 12 Lean declarations and runs 17
evidence regressions. The exact successful command results are recorded in the
JSON receipt and raw logs; preserved VM evidence is not a fresh VM experiment.

The next source work is frame construction, parser acceptance and partial mutation
on rejection, terminal reception and failed publication. Their actual libc calls,
local allocation, structure copies and caller continuations need explicit source
semantics. Whole-slice simulation, the checked C/Rocq-to-Lean bridge, all sixteen
original native/Linux obligations, compiler/runtime/linker/loader correspondence,
independent profile review and M5 hardware confidentiality remain open.
