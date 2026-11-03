# Reporting source binding

The live producer is `native/leancage_m3.c:capture`, called during supervision
and final draining. Its result flows through the actual `finish`/`send_frame`
encoder to `LeanCageM3.decodeResult`, `detailedReport` and `persistReport`.
The collector closes and clears a failed destination, accounts acknowledged reads
before writes, and never resumes persistence after an error. This implements
[§FS-workspace.results](../../docs/functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) and [§AR-workspace.transport](../../docs/architecture/AR-workspace.md#transport-private-events-and-public-result).

Run `./scripts/check_reporting.sh`. Its scripted short-write/error/recovery case
uses the maintained C functions and passes their actual frame to the live Lean
decoder and publisher. It checks both successful and failed report publication.
The current VM record separately covers the actual helper and public CLI.

Changing the collector also renames generated temporaries in the complete-helper
AST. `source.py` compares the main body through its first collector call with the
preserved AST, permitting an injective renaming of temporaries only. It adapts
the existing proof copies and checks their terms against the current complete
AST. Input/history witnesses and loss paths remain included. Full statements
and transitive foundations must match their original records modulo that same
renaming. Original proof sources, snapshots and accepted records are preserved.

`check.py` checks source, tool/dependency and compiled-artifact fingerprints and
reuses a matching checked cache under [§AR-tooling.checks](../../docs/architecture/AR-tooling.md#checks-one-development-gate). Missing artifacts are
rebuilt; `--rebuild` explicitly replays the affected source consumers and kernel
check. Ordinary checking never refreshes the reviewed binding.

This binding retains the bounded source contracts through the accepted input
and initialization frontier. The collector correction has native regression and
VM evidence; these source contracts do not extend through its supervision loop.
The ordinary Lean reporting semantics connection, Linux transport producer,
compiler/runtime/loader composition and export correspondence remain the work
described by [§AR-m4-routes.reporting.chain](../../docs/architecture/AR-m4-routes.md#reportingchain-required-producer-to-consumer-chain). No original obligation is closed here.
