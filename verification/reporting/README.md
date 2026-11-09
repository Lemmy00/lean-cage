# Reporting source binding

The live producer is `native/leancage_m3.c:capture`, called during supervision
and final draining. Its result flows through the actual `finish`/`send_frame`
encoder to `LeanCageM3.decodeResult`, `detailedReport` and `persistReport`.
The collector closes and clears a failed destination, accounts acknowledged reads
before writes, and never resumes persistence after an error. This implements
[§FS-workspace.results](../../docs/functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) and [§AR-workspace.transport](../../docs/architecture/AR-workspace.md#transport-private-events-and-public-result).

The current helper's input/history source binding is checked with
`python3 verification/reporting/check.py`. Its reviewed record is
`assurance/workspace-source.json.gz`; its separate current cache lives in
`.tools/reporting/entry-rebase`. The complete current native VM suite is recorded
by `scripts/run_m3_vm.py` in `assurance/workspace-vm-*`, using distinct production
and fault-injection binaries. Native VM observations and source proofs keep their
separate scopes.

Generated temporaries and string symbols can change when admission is replaced.
`source.py` compares the main body through its first collector call under a
bijective identifier mapping. For every mapped string it checks the complete
registered global: type, initializer bytes, read-only/volatile flags, and alias
relationships. Literal identities used by the copied proofs are checked too.
The adapter then replays the original proof terms against the actual current
complete-helper AST. Full declaration statements and transitive foundations must
match the original records modulo that same mapping; the mapping alone is not
correspondence evidence.

Matching checked artifacts are reused under
[§AR-tooling.checks](../../docs/architecture/AR-tooling.md#checks-one-development-gate).
Missing artifacts are rebuilt; `--rebuild` explicitly replays the current source
consumers and kernel check. `--collect` writes an ignored proposal after those
checks and never updates reviewed expectations. The current receipt preserves
only the accepted input, argument, digest and initialization frontier. It records
the unchanged reporting functions separately from the intentionally changed
production fault selector and preflight terminal receiver. Those changed bodies
need their application proofs; an unchanged complete reporting slice is no
longer claimed.

The original `assurance/reporting-{source,connection,compiler}.json.gz` records
retain their historical scopes. Their exact predecessor inputs are preserved in
`assurance/workspace-baseline.json.gz`; `--historical` verifies the prior source
inputs and matching checked source artifacts. The original reporting connection
and compiler records do not automatically certify the changed helper. The
remaining observation/capture/export composition is assigned under
[§AR-reporting.boundary](../../docs/architecture/AR-reporting.md#boundary-supply-the-remaining-implementation-producers).

The preserved reporting connection relates the native sender call to the
ordinary Lean decoder proof under
[§AR-reporting.interface](../../docs/architecture/AR-reporting.md#interface-preserve-the-complete-call-observation).
Its explicit ownership, runtime and observation premises retain their original
meaning. The scripted collector regression uses the maintained C functions and
passes the actual frame to the live Lean decoder and publisher, including
successful and failed report publication. Neither this regression nor the VM
suite supplies an unfinished source theorem.

The interface preserves every byte prefix and running, published, failed and lost
calls. The preserved source executions witness complete publication, failed writes and a
one-byte transfer followed by loss after arbitrary waits. The source producer
supplies the header/tag/field equations consumed by the ordinary Lean theorem;
it does not assume the decoder's result. Its explicit input ownership and effect
premises still need the physical startup, pinned Linux and executable producers.
Controller/capture/export composition remains under [§AR-reporting.boundary](../../docs/architecture/AR-reporting.md#boundary-supply-the-remaining-implementation-producers).
