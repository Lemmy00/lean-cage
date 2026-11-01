# Native decimal parser source connection

This package follows [§AR-m4-controller.decimal](../architecture/AR-m4-controller.md#decimal-native-unsigned-decimal-fields) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition)
from frame checkpoint `dfaf997d040bd7b8bccb76087d3839bbc3086ec9`. The implementation
choice is [§DA-m4-controller.decimal](../decisions/architectural/DA-m4-controller.md#decimal-preserve-the-actual-parser-and-its-aliases). The selected
function is the unchanged `number` routine in `native/leancage_m3.c`. Extraction
preserves every token; its separate wrapper states the LP64 types, unsigned
maximum and signed-char behavior. Frontend provenance is distinct from deployed
executable correctness.

`decimal_number_exact` characterizes the complete nonempty digit language and
unsigned 64-bit range, accepting leading zeros. The arithmetic proofs connect
the actual machine subtraction, unsigned division, overflow comparison,
multiplication and addition to those integer conditions. The initial signed-char
read and subsequent unsigned reads are related explicitly.

`number_source_path` constructs a complete actual Clight path from independently
owned input bytes and a writable aligned output cell, for arbitrary caller
continuations. It derives every short-circuit branch, pointer increment and the
final store; no execution or expected return is an input premise.
`number_source_return` characterizes every completed return. `number_source_prefix`,
`number_source_progress`, `number_source_loss` and `number_source_finite_bound`
cover every finite execution in the established source/loss machine. The finite
bound is existential for each input, not a measured timing or numeric complexity
claim. Asynchronous loss remains possible at every source boundary.

`number_completed_acceptance` equates a zero return with nonempty valid digits
whose mathematical value fits the unsigned range. `number_success_value` relates
success to the exact stored 64-bit result. `number_rejection_unchanged` preserves
all memory on every prefix of rejected input, including loss. The outside-memory
and permission theorems cover both outcomes and every prefix.

The output may overlap the input. All reads precede the routine's sole successful
store, so no artificial disjointness premise is introduced. Input ownership is
for bytes up to the first NUL, without an earlier NUL, and explicit pointer
bounds. It makes no assumption about bytes following that terminator. Output
alignment and writable ownership remain explicit; all-run routine statements
use a stopped caller, while constructive paths retain arbitrary continuations.

The source machine is sequential and contains no concurrent memory-writer steps.
The enclosing controller must establish the absence of an interfering writer.
The final `Mint64` assignment is one Clight transition; these loss results do not
establish the atomicity of a deployed hardware store.

Twenty examples cover ten accepted and ten rejected inputs. Each has a complete
source execution from actual allocations with both overlapping and separate
buffers. They include zero, leading zeros, 32-bit boundaries, the signed 64-bit
boundary, UINT64_MAX, UINT64_MAX+1, empty input, signs, whitespace, alphabetic
characters and bytes 128/255. These are kernel-checked source witnesses, not
native or VM measurements.

The complete frame checkpoint is archived byte-for-byte. Earlier theorem types,
foundations, exported decoder terms, compiled proof identities and tool pins
remain unchanged. This parser adds no axiom, admitted proof or unchecked cast.
The existing semantic/logical foundations remain visible in the full declaration
inventory. It neither assumes nor establishes Linux argument provenance, policy
bounds, the live Lean plan encoder, controller ordering, native effects, deployed
runtime correspondence or hardware confidentiality. All original native/Linux
obligations remain open; neither M4.3 nor M4 is complete.

The collected inventory contains 83 full Rocq theorem records: 49 have no reported
axioms, 29 retain the existing six foundation/semantic parameters and five retain
the four logical foundations. None uses the bridge's definitional-UIP model.
The generated AST and sixteen proof modules give seventeen compiled artifacts;
the generated C, preprocessed input and AST text are three further provenance
artifacts. Eight integrity regressions pass. These counts describe the audit
inventory, not the strength or completeness of a security guarantee.
