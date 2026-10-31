# AR-m4-library: Local library effects for the reporting slice

This package supplies the remaining local external-call contracts needed by
[§AR-m4-native.contract](AR-m4-native.md#contract-intended-universal-simulation-and-ownership-obligations) for [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport). It follows [§AR-m4-effects.machine](AR-m4-effects.md#machine-source-steps-blocked-calls-and-loss)
without altering the frozen machine or its earlier claims. Contracts and source
proofs are separate from proving that libc, Linux or the compiled executable
implements them.

## memory: Comparisons, strings and copying

Use actual CompCert byte loads, stores, pointer widths and permissions. A readable
span contains initialized bytes at a representable nonwrapping address. Counts
fit the unsigned 64-bit ABI. A C string has a finite initialized prefix containing
no zero bytes followed by a zero byte, all within that span. No guessed string
length or presumed comparison outcome is an ownership premise.

`memcmp` compares equal-length spans lexicographically as unsigned bytes.
`strcmp` compares the two prefixes before their first NUL. Permit any signed
32-bit negative/positive return with the required ordering; equality returns zero.
Both local contracts preserve memory. Prove equality characterization and
uniqueness of the loaded spans/terminated string interpretations. Their actual
libc implementations and concurrent mutation/signal interference remain open.

`memcpy` reads an initialized source and owns a writable destination of the same
length. Require nonoverlapping ranges, including same-block disjoint ranges.
Do not require destination initialization or word alignment. A completed return
contains exactly the source bytes, returns the destination pointer, and preserves
permissions and memory outside the destination. Derive existence from independent
ownership, rather than requiring a successful store as an input assumption.

Loss during copying permits any finite order of writes of source bytes to their
corresponding destination positions, with repetitions allowed. This includes
non-prefix subsets and vector-copy store orders. Each position must be in range;
all writes use the captured source byte at that position. Prove preservation of
permissions, source bytes and memory outside the destination at every such
partial state. No lost copy returns to the caller. This is an overapproximation
of store order, not a verification of a libc implementation.

## process: Close attempts and nonreturning exit

A close call may return zero or signed minus one. Its explicit optional errno
update uses a writable, aligned, representable TLS cell. An error carries an
errno update; a success may preserve or update errno. The source ignores close's
return, so no close attempt or return supplies a cleanup/extinction receipt.
Whether a descriptor remains open after an error is a Linux correspondence
obligation. Separate the TLS cell from all caller-owned stable regions in source
composition proofs.

`_exit` records the requested signed 32-bit argument and has no source return.
Its terminal state means the source cannot resume; it is not an observed kernel
process-extinction or descendant-cleanup receipt. Supported external calls may
wait or lose the process, including while copying or exiting. Do not count a wait
or loss edge as defined ordinary progress, or infer scheduling termination.

## machine: Additive external-call semantics

Introduce an explicit extension with injected original machine events and named
library events. Preserve every original transition and every loss boundary.
Enable returns only at the exact maintained `strcmp`, `memcmp`, `memcpy`, `close`
and `_exit` signatures and argument lists. Unsupported external calls and builtins
remain missing semantics. Prove that added effects cannot execute at an internal
source state or masquerade as an original source/read/write/errno event.

Record source-signature equations against the regenerated AST. Reuse existing
source proofs only after proving the relevant preservation/composition statement;
an embedding of successful runs alone does not transfer universal safety to a
larger transition system. All caller memory ownership, source allocation, struct
copies and error paths remain explicit obligations.

## source: Source connections and completion boundary

Connect complete maintained routines in dependency order. Start with `fault`:
an owned initialized global mode pointer and two stable terminated strings imply
that every completed return is one exactly when the strings agree, zero otherwise.
Cover arbitrary comparison magnitudes, waiting, loss and actual caller
continuations. Memory remains unchanged. Defined progress requires a source step,
an enabled comparison return or the exact function return.

Then compose these contracts with the byte codecs, `write_all`, frame routines,
terminal receiver and publication paths. Preserve reserved bytes, narrowing,
sequence wrap, fault injection, partial rejected-frame mutation and ignored
publication failure. Do not mark a larger function or the selected slice complete
until all its branches, allocation and external/caller transitions are checked.

## evidence: Replay and retained obligations

Follow [§AR-m4-effects.gate](AR-m4-effects.md#gate-additive-evidence-and-completion-boundary) and [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record): full declaration/type/axiom
inventory, independent owned-memory witnesses, actual generated-source mappings,
term replay, preserved earlier claims/artifacts and negative evidence-gate tests.
Use the existing pinned local tools. No native workload runs on the shared host.
These results do not discharge any of the sixteen original Linux/native entries,
the C/Rocq-to-Lean bridge, compiler/runtime correspondence or M5 hardware channels.
