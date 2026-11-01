# Actual initialization stores and ordered validation

For [§AR-m4-controller.initialization](../../docs/architecture/AR-m4-controller.md#initialization-actual-flag-and-pointer-initialization), this package connects the actual preflight,
export, digest-pointer and argument-pointer assignments to their exact memory
updates. The export-to-bounds region composes the existing source checks with
these writes. Earlier mutations remain visible on rejection or process loss.

The public source theorem starts from independently owned strings, argument
cells, numeric policy memory and writable output cells. It constructs the
certificate, ordinary execution and universal boundary split internally. The
write footprint and memory permissions are explicit. Mode/preflight is a
separate region until numeric and parent validation are composed with it.

Run `python3 m4/initialization/check.py` after the original connection, bridge,
controller, plan, main, policy, arguments, digest and caller-string gates.
`--collect` writes ignored candidates and never updates reviewed expectations.
The gate preserves the exact caller-string export and checks the imported flag
computations, full theorem records, compiled artifacts, negative controls and
independent kernel replay. See `docs/reviews/M4-initialization.md`.

The allocated cases are checked source executions, not VM measurements.
Whole-main entry, physical argument provenance, parent identity, subsequent
reporting, setup, supervision, cleanup, libc/Linux implementation, compiler and
runtime correspondence, translation faithfulness and hardware channels remain
open. This package does not complete M4 or the whole controller.
