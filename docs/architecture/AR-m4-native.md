# AR-m4-native: Bounded native semantics feasibility experiment

This experiment implements the feasibility assignment in [§RM-roadmap.m4.entry](../roadmap.md#m4entry-next-assignment--m41-native-semantics-feasibility)
for [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) and [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record). The existing conditional
M3 profile and its source, theorem and VM baselines remain unchanged.

## slice: Source-connected framing and terminal error boundary

Extract `write_all`, `error_number`, `fault`, the four little-endian codecs,
`send_frame`, `decode_frame`, `result_of`, `fail_child` and `finish` verbatim from
`native/leancage_m3.c`, with their original enum/struct/global dependencies.
Use explicit LP64 declarations for external effects rather than Linux headers.
Keep original branch order, fault modes, compound literals and narrowing casts.
Expand ordinary formatting in the generated readable view and enforce the
300-authored-C-line bound. The extraction is an experimental translation unit,
not a production replacement. Source hashes and extraction checks identify its
connection; they are not a proof of the frontend.

Also extract the terminal-error read/EOF loop and result dispatch from
`namespace_init`, from its `failure_bytes[9]` declaration through the branch before
`report:`. An experiment-only wrapper supplies the existing `bad`, `entered`,
`leader_done`, `leader_status` and pipe descriptor inputs. These parameters expose
all values of those dependencies rather than assuming successful setup or entry.
The complete translation unit has 260 authored C lines (218 in the extraction and 42 in its explicit ABI header), including adapters and
function-address roots used to prevent frontend dead-code elimination.

The poll/frame accumulator, ptrace dispatcher and namespace setup remain outside
this first slice. They supply the owned 160-byte input buffer and result object,
run/UID/preflight state and selected fault mode. Their concurrency, short reads,
EOF, cancellation and process loss remain explicit composition obligations.
Any smaller proof scope must be named separately; an AST is not verification.

## semantics: Candidate and acceptance boundary

Use the assigned CompCert commit `14d616046360a0b2611ebdfc2f98368af402e1f7`
Clight (the pinned VERSION actually reports 3.17, despite the inherited 3.18 label),
with exact compatible local frontend/prover/build and license identities
recorded before execution. Ordinary external calls must expose memory accesses,
short transfers, interruption, zero transfer, errno and failure. Repeated EINTR
or blocked calls do not promise termination. Asynchronous process loss must be
represented at the environment/composition boundary, never as successful reporting.

The intended universal result relates actual Clight executions for arbitrary
owned input bytes and permitted effects to the frame/error trace. Ownership must
provide distinct readable input and writable result regions, sufficient bounds,
and stable run/UID/mode state while each sequential call executes. Local buffer
allocation, pointer arithmetic, machine widths and errno conversion are proof
obligations. External contracts cannot assume containment or successful reporting.

## contract: Intended universal simulation and ownership obligations

The target is a forward simulation for every initialized input byte vector,
representable argument/global value and permitted local effect history, from
every finite selected Clight execution to the operation/error/frame trace.
A terminating return must have the specified value and emitted-byte prefix;
a rejected frame must return -1 with the source's actual result-object mutations;
blocked calls and loss have distinct outcomes, including loss after a transfer
or failed reporting. Every represented memory access and shift must be defined
under independently stated ownership/ABI premises. This does not require every
history to terminate, nor identify cancellation with completion. The full target
is **not proved**. `Attempt.v` states and attempts the first required write-bound
obligation, and the adapter refutations explain why the attempted effect route
cannot support that universal theorem. They do not replace it with a weaker
successful security theorem.

The independent boundary premises and behavior to preserve are:

- Linux x86-64 LP64: unsigned bytes, 32-bit int/unsigned, 64-bit long/size_t/ssize_t
  and pointers. `result` has the maintained member order and target composite
  layout. Header declarations, integer widths, errno constants and wait macros
  are checked separately; libc/kernel correspondence is not supplied by that check.
- `write_all` owns a readable initialized region of the requested size, has no
  address-space wrap, and cannot alias the mutable errno cell. A returned positive
  ssize_t is at most remaining count; zero returns -1; negative return retries only
  for EINTR, otherwise returns -1. A permitted write reads exactly its own prefix,
  never an arbitrary host object. Effects may change errno, block or lose the
  process. These are local effect obligations, not containment assumptions.
- `fault` needs stable NUL-terminated mode/name strings. Each `error_number` call
  may evaluate `__errno_location` several times; stable owned TLS errno between
  those evaluations is an obligation. Its positive 1..4095 result or fallback EIO
  must not be inferred from an unconstrained external function.
- `send_frame` uses a fresh 160-byte local buffer and all maintained field offsets,
  zero/reserved bytes, unsigned narrowing and fault branches. Success of its
  write helper does not by itself imply a complete frame (`report_drop` and
  `report_short` are deliberate examples). Unsigned sequence increment wraps.
- `decode_frame` owns 160 readable bytes, a distinct writable `result` object and
  stable run/UID/preflight globals. It checks header/version/sequence/reserved
  bytes, then writes the result before some further checks. Its accepted tags
  are 0/1/2/4/5/6/7 under the actual per-tag checks (7 requires preflight); 3 and
  all other arbitrary tag bytes reject. No failed-decode transactional guarantee
  is assumed. This private parser is not the final public Lean parser.
- The terminal receiver owns its nine-byte array, accepts only the exact eight
  stage/error bytes on the non-entered successful-read path, and preserves short
  read, EINTR, EOF, excess ninth byte and failure handling. Stage is 1..8 and error
  1..4095; malformed/short/error paths become UNKNOWN. Its wait/entry/bad inputs
  are explicit wrapper parameters, not fabricated observations. `close` failure
  is ignored by this source path; a call attempt is not a cleanup receipt.
- `fail_child` sends stage and error modulo 2^32, preserves dropped/short/failed
  reporting and then calls `_exit(125)`; noreturn behavior is an external contract.
  `finish` ignores publication failure and returns the source exit mapping. For
  its intended result domain EXITED detail is <=255 and SIGNALLED detail 1..64;
  unconstrained uint32 detail could make the signed `128 + detail` path invalid
  under ISO C and is not claimed safe. Producer/domain correspondence is open.

Pure codec proofs discharge byte access/shift/return execution obligations only
for those two reader functions. Whole-slice ownership preservation, buffer
allocation/copy safety, external string/memory routines, errno/return bounds and
C error/frame simulation remain open. Constructed legal codec executions are
not a theorem quantifying over every execution of the full effectful helper.

## evidence: Honest feasibility outcome

Record full checked types and transitive assumptions in each assistant, inhabited
success/rejection/error witnesses, reproducible failed proof attempts and exact
blockers. A partial theorem must not be presented as the intended universal
simulation or memory-safety result. Negative feasibility can settle a route choice
only with substantive source-connected semantics evidence and a revised route.

Lean targets include `LeanCageM3.decodeResult_valid`, `observe`,
`private_report_knowledge`, `report_loss_preserves_entry` and the lifecycle entry
invariant. Native `decode_frame` parses intermediate private helper events; Lean
`decodeResult` parses the final public frame. Their accepted domains differ, so
no equality between the decoders is presumed. A written map leaves the checked
bridge open for M4.2. GCC output, Linux effects, runtime and hardware stay open.

## outcome: Checked pure core and rejected direct effect adapter

`m4/Codec.v` constructs terminating executions of the actual generated `get32`
and `get64` bodies/calls, and connects them to Clight small-step runs. Input byte
values, memory/block/offset, program and call continuation are quantified.
The owned variants require no address-space wrap and successful byte loads at
every accessed address. Constructive allocated-and-written 4/8-byte witnesses
inhabit those premises. Output is the explicit unsigned shift/OR reconstruction;
memory is unchanged and trace empty. These are Rocq semantic subproofs, not a
Lean bridge, universal whole-helper safety proof, or a compiler guarantee.

The full reporting simulation was attempted through the actual `write` external
call. `m4/Attempt.v` preserves its universally quantified owned-buffer return-bound
obligation, the remaining goal, and an exact equation to the generated call.
It uses `Abort` and exports no theorem for that obligation. Stock Clight leaves
`external_functions_sem` abstract; typing does not imply `-1`/zero/short transfer
bounds, an owned errno cell, byte transfer or progress. Adding those contracts
is a real obligation, not a consequence of AST extraction.

`m4/Effects.v` proves that a silent nondeterministic short-write adapter cannot
satisfy CompCert's `ec_determ`. A count-only read trace also cannot describe two
possible byte contents with the same return count and trace. Allocated buffers
with different loaded bytes inhabit the obstruction. Bare Clight's actual first
`write_all` step is silent; it has no process-loss edge. This rejects the direct
silent/count-only adapter and unextended loss model, **not every possible Clight
or CompCert approach**. The universal simulation and memory safety of
`write_all`, framing, result mutation and terminal receiver remain unproved.

## revision: Byte-aware effects and loss before the Lean bridge

Retain Clight for sequential C memory/integer reasoning. Before M4.2's bridge,
implement and validate a byte-aware effect semantics and an environment product
with loss at every source boundary. A candidate read event must carry arbitrary
returned bytes as well as transfer count and errno, or use an explicit deterministic
input oracle with a checked observation relation. Merely appending differing byte
arguments to CompCert syscall events does not automatically satisfy `match_traces`
and `ec_determ`; changing upstream event types/properties requires renewed proofs.
Do not silently reuse compiler theorems for modified semantics.

The adapter must specify permitted buffer reads/writes and separation of input,
result and errno cells; ssize_t/size_t bounds, signed errno and zero/short/EINTR/EOF
behavior; calls that block; and asynchronous death before, during and after
reporting. Repeated interruption has no termination guarantee. The independent
`write_trace` model preserves bounded transfer, errors, blocking, arbitrary finite
EINTR prefixes and loss including zero remaining bytes/after an error. Its
arithmetic lemmas are not connected to the source by the unfinished simulation.

Next prove the complete selected C slice under those inhabited local contracts,
then relate intermediate-event assembly and final public result to the precise
Lean declarations. `decode_frame` can partially modify `*r` before returning -1;
do not assume failure leaves it unchanged. `finish` can return the observed exit
status even when publishing the frame fails; `fail_child` exits after short/failed
reporting. The existing M3 report-storage correction remains unchanged.

## register: M4 experiment claim and obligation register

The additive register is `assurance/m4-claims.json` (full theorem types/transitive
assumptions and exact Lean targets) and `assurance/m4-evidence.json` (source/tool/
artifact identities, negative outcome and open edges). The M1/M2/M3 manifests and
the existing [§FS-assurance.status](../functional-spec/FS-assurance.md#status-initial-claim-register) register are preserved byte-for-byte: none of
their open native-correspondence entries changes status. This additive record
updates assurance for M4 without changing their reviewed source fingerprints.

The direct effect route has an evidence-backed negative feasibility outcome.
Full native correspondence, whole-slice memory safety, checked Lean connection,
compiler/runtime/linker/loader/Linux and hardware obligations remain open. No
production assurance or successful containment premise is introduced.
