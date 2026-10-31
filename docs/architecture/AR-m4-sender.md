# AR-m4-sender: Complete frame sending and publication-return behavior

This package continues [§AR-m4-native.contract](AR-m4-native.md#contract-intended-universal-simulation-and-ownership-obligations) and [§AR-m4-callers.control](AR-m4-callers.md#control-source-branching-and-helper-paths) for
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport). It targets the actual `send_frame` body and its `finish`
caller. Layout, allocation and initialization lemmas alone do not complete either
routine. The checked Lean connection and Linux/executable obligations remain open.

## input: Independent result, string and error-cell ownership

Own an aligned, nonwrapping readable 144-byte source result with all eighteen
scalar fields and all 32 digest bytes initialized. Structure padding may remain
arbitrary memory values. Quantify over arbitrary 32/64-bit field words and sequence;
do not assume the result is accepted by either decoder. Derive the callee's actual
by-value structure copy and separate 160-byte local array from fresh allocation.

Own the actual mode pointer and fault-literal strings, and a representable writable
TLS error cell. Keep the strings and pointer needed by later fault checks separate
from error-cell writes: a duplicate report can perform I/O before the next fault
check. Fresh local structures and frame bytes are separate from all old owned
objects. Do not assume a successful transfer or desired fault outcome.

## encoding: Actual initialization, copying and writer calls

Execute every source zero-initialization store, the typed parameter copy, both
`memcpy` calls and every complete `put32`/`put64` call. The outgoing frame is exactly
160 bytes. The kind narrows to one byte; all word fields use the source little-endian
encoding. Header and reserved bytes, sequence, export fields, digest, OOM and PID
fields use the actual wire offsets. Native structure padding does not become
initialized wire data.

Retain arbitrary library waits, process loss and the non-prefix partial-copy
schedules allowed by [§AR-m4-library.memory](AR-m4-library.md#memory-comparisons-strings-and-copying). A copied literal or digest cannot be
replaced by an assumed final buffer. Typed structure copying remains one Clight
step with the compiler-interruption boundary recorded separately.

## reporting: Source fault checks and complete writes

Fault selection occurs only when the descriptor differs from 1 and the original
unsigned kind is at most UNKNOWN. Preserve wrong-sequence increment modulo 2^64,
the changed reserved byte, duplicate reporting, the 17-byte short report and the
dropped report. Keep the actual ordering: duplicate reporting can fail before
later checks, and a completed first write can be followed by another write.

Prove exact return conditions and bounded emitted bytes for every finite source
history, including EINTR, errors, zero transfers and loss during transfer. A zero
return does not imply one complete frame: the deliberate drop, short and duplicate
branches remain distinct. Ordinary enabled progress is not a termination claim.

## memory: Prefix preservation and actual returns

Track every old memory location outside the permitted TLS error cell and every
fresh local object's permissions. Preserve initialized frame and selector inputs
through I/O effects and derive all later accesses from that ownership. Every local
return must execute the actual frees of the copied result and frame buffer.
Loss retains the current memory, including partially initialized or copied bytes.
No modeled close/exit event or local free establishes Linux cleanup correspondence.

## finish: Exit mapping despite publication failure

Compose the complete sender source into `finish`, including its actual by-value
copy. The source ignores publication failure and returns its exit mapping.
Keep the intended EXITED detail at most 255 and SIGNALLED detail in 1 through 64
when claiming the specified valid result domain; account explicitly for the
signed addition and casts. Do not infer successful publication from the returned
exit status or assume producer/domain correspondence that is still unproved.

## evidence: Complete statements and inhabited outcomes

Follow [§AR-m4-effects.gate](AR-m4-effects.md#gate-additive-evidence-and-completion-boundary), [§AR-m4-decoder.evidence](AR-m4-decoder.md#evidence-full-source-evidence-and-inhabited-inputs) and [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record).
Preserve all preceding declarations, compiled identities and receipts, including
the maintained historical import closure. Add full-source success, drop, short,
duplicate, malformed-header, failed-write and loss executions from allocated
inputs. Keep partial preparation results distinct from complete routine results.

For constructive successful-run witnesses, a source-path certificate may select
successful write returns. The universal preservation, progress and exact-return
theorems must instantiate the unrestricted certificate admitting every write
outcome. A successful witness does not remove failed or lost hostile executions.
