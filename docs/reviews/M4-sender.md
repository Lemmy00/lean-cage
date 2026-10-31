# M4 source submilestone: complete frame sending and finish

This author source/proposition review advances [§AR-m4-sender](../architecture/AR-m4-sender.md#ar-m4-sender-complete-frame-sending-and-publication-return-behavior) and
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) from `05616f3829ceac3ce6291a4b97e019eb11299d66`, following
[§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not the
independent composed-profile review. M4.2–M4.6 remain incomplete.

## Independent ownership and actual source

`SenderProgram.sender_input` owns an aligned nonwrapping readable 144-byte
result with all eighteen machine-word fields and 32 digest bytes initialized,
the actual magic and fault-literal symbols, the mode pointer/string, and a
writable TLS error cell. Structure padding is arbitrary. Input values need not
pass either result decoder. Mode/literal data remain outside TLS writes, with
same-block nonoverlapping spans allowed. No desired fault outcome, successful
transfer, source path or prepared output is assumed.

`SenderEncoding.sender_encoding_connection` derives the actual by-value copy,
two fresh local allocations, all 160 zero stores, both library copies and every
byte-writer call. The exact 160-byte output uses the actual source offsets,
word widths and narrowed kind. Copy boundaries retain arbitrary waits, loss
and non-prefix partial-copy schedules. Typed structure assignment remains a
single Clight step; compiled interruption behavior is still an obligation.

`SenderReporting.sender_reporting_source` executes the descriptor and original
unsigned-kind guards, all five selector calls, wrapped sequence increment,
reserved-byte mutation, duplicate-first-write failure, short/drop behavior and
final write. Duplicate reporting preserves later selector inputs through TLS
updates. Every actual return executes both local frees.

## Universal propositions and constructed executions

`SenderProgram.sender_whole_source_guarantee` covers every finite source
history: old memory outside TLS is preserved; every live prefix can take an
ordinary step or has returned with the exact result. `sender_all_returns` binds
that result to actual emitted bytes. Zero means exactly the source-selected
zero-, seventeen-, 160- or 320-byte report. Minus one means a proper prefix.
`sender_all_prefixes` includes interrupted transfers and non-prefix copy loss.
`sender_returned_locals_have_no_permissions` records both actual frees.
`SenderOutcomes` proves the exact counts and the 320-byte prefix bound.

The certificate's explicit `allow_errors` parameter separates proof uses.
Universal guarantee/trace/prefix theorems require the unrestricted `true`
instance. The `false` instance only constructs successful histories in the
same unrestricted transition system. It neither changes that system nor
proves hostile-path safety. `SenderSuccessfulRuns` gives an exact successful
report for every owned input. `SenderFailedRuns` constructs failed reporting
with no emitted bytes when a nonempty report is expected. `SenderLossRuns`
constructs one-byte partial transfer/loss after arbitrary finite waits.

`SenderWitnesses` constructs every input field, digest, selector and TLS cell
from allocations at the actual source symbol identities. `SenderSamples`
executes complete normal, dropped, short, duplicate and malformed reports;
sequence `2^64-1` wraps to zero in the wrong-sequence sample. These are local
owned inputs, not an initialization or Linux binary execution claim.

`FinishProgram.finish_whole_source_guarantee` executes the real by-value copy,
complete sender and subsequent exit mapping. It retains the outer record
across every sender effect, ignores either sender return and frees its own
local copy. `FinishDetails` states the intended EXITED/SIGNALLED detail bounds
and proves a returned status in 0 through 255 under them. `FinishPublication`
and `FinishWitnesses` construct full-source finish executions with both full
publication and ignored failed publication from allocated caller inputs.

Enabled progress and existence of successful or failed finite runs do not
imply termination under arbitrary waits, retries or scheduling.

## Evidence preservation and remaining obligations

The inventory adds 195 Rocq declarations across 63 modules, totaling 875
Rocq records in 154 maintained modules and twelve unchanged Lean endpoints.
`assurance/m4-sender-baseline-claims.json` preserves the preceding manifest.
All 680 preceding full statements/foundations and 91 compiled identities are
checked unchanged, including the fifteen historical compatibility modules.
Both earlier query contexts remain fixed so new imports cannot alter frozen
name qualification. `assurance/m4-sender-evidence.json` binds source hashes,
compiled identities, reviewed types/foundations and raw validation receipts.

Terminal reception and remaining selected-slice caller composition stay open.
So do the checked C/Rocq-to-Lean bridge, all sixteen original Linux/native
entries, libc/Linux interference, compiler observation/refinement, executable
and runtime chain, independent M4.6 review and M5 hardware channels. No native
helper, extracted AST, tool pin, VM/kernel profile or hardware claim changes.
