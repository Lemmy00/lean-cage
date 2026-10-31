# AR-m4-receiver: Complete terminal-error receiver from owned inputs

This package completes the selected receiver wrapper under [§AR-m4-native.contract](AR-m4-native.md#contract-intended-universal-simulation-and-ownership-obligations)
and [§AR-m4-effects.gate](AR-m4-effects.md#gate-additive-evidence-and-completion-boundary) for [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport). It covers the maintained
`namespace_init` fragment in `m4_collect_failure`; the surrounding poll/ptrace,
namespace, supervision and public-result assembly remain separate obligations.

## input: Independent caller memory and wrapper arguments

Own a writable aligned nonwrapping 144-byte caller result and a writable,
representable TLS error cell. Own initialized run/UID globals at the actual source
symbols, with their blocks distinct from TLS. Quantify over every 32-bit descriptor,
bad, entered, leader-done and wait-status argument. These wrapper inputs expose
upstream facts; they do not prove those facts were observed on Linux.

Derive all seven actual local allocations, their distinctness, freshness and
permissions, the descriptor store and the initially empty initialized byte prefix.
The nine-byte array's remaining bytes and structure padding may be uninitialized.
The result output may overlap old globals or TLS: only accesses before the final
copy need those values, and preservation excludes the caller output and TLS spans.
No prepared execution, successful read or selected result is an input premise.

## reads: Every source read and interruption boundary

Follow the exact loop with requested count `9-used` and destination `bytes+used`.
Positive reads append exactly their observed bytes. Zero reaches the close attempt;
EINTR retries with the same prefix; another error sets `bad=1` and reaches close.
A ninth byte ends the loop and cannot become an eight-byte setup record. Preserve
arbitrary finite waits and loss before, during and after reads, including bytes
written by a partial transfer before loss. Every finite trace observes at most
nine bytes; every reachable live prefix has ordinary progress or an exact return.
No fairness or termination follows from enabled progress or finite witnesses.

## classification: Exact raw wait and setup classification

The setup branch requires `bad=0`, `entered=0`, exactly eight bytes, unsigned stage
1 through 8 and unsigned error 1 through 4095. Execute all repeated `get32` calls
and actual short-circuit branches. Relate every completed output to the exact
bytes read in that execution and the source's effective bad flag. Bad, malformed,
short and ninth-byte setup paths reach UNKNOWN.

With an empty read prefix, no bad flag, a nonzero entered flag and a nonzero
leader-done flag, retain the source wait macros over arbitrary 32-bit words.
Do not assume those words are valid Linux wait statuses. In particular, raw status
65 is classified SIGNALLED with detail 65. A constructed complete source run
must preserve this behavior. Proving the SIGNALLED 1..64 domain required by
[§AR-m4-sender.finish](AR-m4-sender.md#finish-exit-mapping-despite-publication-failure) needs upstream wait-status provenance; it is not supplied by
this wrapper proof. UNKNOWN has stage 9, detail EPROTO (71), and entry 1 or 2
according to the input entered flag.

## memory: Ignored close results and actual copies and frees

Execute the real close call with every permitted success/error/TLS update, wait
and loss. Its returned value is discarded. A close attempt or return is not a
cleanup receipt. Execute the selected `result_of`, its fresh private allocation,
all field stores and its own free. Then perform both actual typed structure copies:
branch result to receiver result, and receiver result to caller output. Track
arbitrary padding and retain every old permission needed by subsequent operations.

Every completed receiver return frees all seven local blocks in the actual
`blocks_of_env` order. No permission remains in those object ranges. Every finite
prefix preserves old memory outside the permitted caller-output and TLS spans.
Loss retains the actual interrupted memory and does not become a returned result.
Typed structure copies are single Clight transitions, with compiler interruption
and concurrency correspondence still open.

## evidence: Complete source propositions and preserved history

Audit full statements and transitive foundations, replay the complete maintained
import closure with `coqchk`, and preserve all preceding 875 Rocq records, twelve
Lean records and 154 compiled module identities. Freeze the preceding printing
contexts so new imports cannot change their recorded qualification. Add allocated
complete runs for valid setup, short input, ninth-byte overflow, exit, signal,
stopped/raw status, arbitrary finite EINTR prefixes, fatal read errors, ignored
close errors and partial-read loss after arbitrary finite waits.

The additive audit grows to 197 modules. Its bounded wrapper allowance is 900
seconds, up from 600; the unchanged M4.1 replay retains its 300-second limit.
This changes the execution allowance only: full compilation, every type and
foundation comparison, historical identities, kernel replay and tamper checks
remain mandatory. Whole selected-slice cross-routine composition, the checked
C/Rocq-to-Lean bridge, all original Linux/native obligations, compiler/runtime
chain and independent M4.6 review remain open. No native or VM profile changes.
