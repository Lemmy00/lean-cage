# M4 source submilestone: reporting primitives

This author proof-statement/source review advances [§AR-m4-effects.errno](../architecture/AR-m4-effects.md#errno-source-errno-normalization-and-bounded-execution) and
[§AR-m4-effects.readers](../architecture/AR-m4-effects.md#readers-universal-bounded-frame-reader-execution) from `31ee71fa94af3714c0f16a70dc852ab94108a313` on `main`.
It follows [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and
[§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not an independent security review.
M4.2 as a whole and M4.3–M4.6 remain incomplete.

## Exact source results

The original maintained C, 260-line extraction, preprocessed C, generated Clight
program and effect/loss machine are unchanged. `ErrorNumber.source_error_number_body`
checks the full body equation, and `Readers` executes the original `f_get32` and
`f_get64` bodies directly. Public universal claims fix `Clight.globalenv Slice.prog`.
The old M4.1 gate still regenerates/checks the source and tool identities.

| Function | Independent memory premise | Checked ordinary execution | Exact returned result |
|---|---|---|---|
| `error_number` | Initialized aligned writable 32-bit TLS cell at a representable address | 18 steps / one errno call for nonpositive values; 26 / two for values above 4095; 34 / three for 1–4095 | Original signed errno for 1–4095, EIO (5) otherwise |
| `get32` | Four initialized readable bytes; complete range does not wrap | 59 silent source steps | The original `Codec.get32_word` expression over the four byte loads |
| `get64` | Eight initialized readable bytes; complete range does not wrap | 103 silent source steps | The original `Codec.get64_word` expression over the eight byte loads |

These counts are model transitions, not timing measurements. `source_execution`
and `reader_execution` construct actual source paths with arbitrary call
continuations, stopping at the source return. Universal whole-execution theorems
use `Kstop`, so they do not constrain a caller after it resumes.

`ErrorNumber.error_number_return_exact` and `Readers.reader_return_exact` quantify
over every returned value and every finite execution. `error_number_all_prefixes`
and `reader_all_prefixes` establish memory preservation and restricted events for
all prefixes, including loss. The reader theorem classifies every trace as silent
steps or a silent prefix followed by terminal loss. The errno bound is at most
35 steps including loss after return; reader bounds are 60 and 104. Loss cannot
create a return or resume a dead state. Each routine admits loss before, between
and after its reads, including immediately after its return.

`error_number_defined_prefix` and `reader_defined_prefix` prove that every live
prefix either reaches the exact return or enables an ordinary transition.
Waiting/loss are not progress witnesses. This establishes definedness and a
finite bound in the local model. It is not a Linux scheduling or wall-clock claim.

`Deterministic.v` supplies finite certificates whose edges prove an actual
machine step, unchanged memory, and uniqueness of the ordinary successor while
retaining the alternative loss edge. Its classification theorem quantifies over
the unchanged `Machine.steps`. No hostile transition was deleted or premise
requiring a successful run introduced. `allocated_errno`, `allocated_bytes` and
the arbitrary input/source witnesses construct actual CompCert allocation,
stores and loads for every errno bit pattern and every four/eight-byte sequence.
The checked errno boundaries include signed minimum/maximum, -1, 0, 1, 4095 and 4096.

## Evidence and preserved claims

The active connection inventory contains 173 Rocq declarations and the same 12
Lean endpoint declarations. All previous 126 Rocq and 12 Lean records are preserved
exactly in `assurance/m4-primitives-baseline-claims.json`, including full types and
transitive assumptions. The extended printer raises the depth limit and rejects
truncated statement text, including deeply nested numeric bounds. The original
six compiled connection modules remain
byte-identical; the gate checks their artifact hashes as a subset of the expanded
nine-module inventory. Every new term is replayed with `coqchk`. No admission,
new custom axiom or compiler-trust shortcut is used.

The foundation/semantic-parameter union remains the same six Rocq entries recorded
in the earlier write-loop review: classical excluded middle, dependent functional
extensionality, two constructive-real decision principles, and upstream external/
assembly semantics parameters. The replacement machine still excludes stock
external/builtin execution; no implementation property of those parameters is
assumed. The 12 Lean endpoint claims and their foundations are unchanged.

`assurance/m4-primitives-evidence.json` binds the primary declarations, source
baseline, proof artifacts, preservation audit and command receipts. Historical
receipts stay intact. The roadmap-only legacy source fingerprint amendment and
its propagation through evidence bookkeeping are explicitly recorded; no previous
theorem expectation is refreshed. The preserved M1–M3 sources, claims, toolchains
and VM evidence are unchanged. Their assurance register remains the frozen
baseline; the additive M4 record and roadmap state only this source sub-result.

## Validation and remaining obligations

The evidence receipt records Grund formatting, the full repository gate, the
M4.1 plus extended connection gate, preserved M3 artifact validation, and diff
checks. The extended gate checks 173 Rocq declarations, 12 Lean declarations,
all nine modules with `coqchk`, and 15 evidence regression tests. Repository
checks retain 74 Python tests, 168 Lean guards and the 445/274/419 theorem
inventories. Artifact validation rechecks the existing VM record, without running
a hostile workload or claiming a fresh VM experiment.

Still open: codec writes and their round trip, frame construction/acceptance,
partial decoder mutation on rejected frames, terminal reception, failed report
publication, allocation/caller composition through the whole slice, the checked
C/Rocq-to-Lean bridge, all sixteen original M2/M3 native/Linux obligations,
compiler/runtime/linker/loader correspondence and independent composed-profile
review. Stable TLS is a local external contract, not a proof of Linux/libc or
concurrent signal-handler behavior. M5 hardware confidentiality is unchanged.
