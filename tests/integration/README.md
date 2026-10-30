# Integration tests

The M0 tests validate [§AR-tooling.grund](../../docs/architecture/AR-tooling.md#grund-local-wrapper-and-citation-scope) and [§AR-tooling.checks](../../docs/architecture/AR-tooling.md#checks-one-development-gate) against the pinned
Grund binary. They copy the documentation/configuration into disposable fixtures,
then verify valid Lean references, rejection of a dangling reference, and exclusion
of dependency sources. They do not modify project documents or global settings.

Run them through `./scripts/check.sh`, or build before running separately:

```sh
lake build
python3 -m unittest discover -s tests/integration -p 'test_*.py' -v
```

Later tests here must cite the architecture contracts for the component boundaries
they exercise. Passing integration tests is evidence of tested behavior, not a
substitute for a formal refinement or isolation theorem.

M1.1 adds `FilterContract.lean` under [§AR-filter-slice.contracts](../../docs/architecture/AR-filter-slice.md#contracts-lean-declarations-and-downstream-ownership). Its pure
interpreter checks 14 allowed, denied, architecture-mismatch, x32, and unsigned
boundary cases against the reference program. After `lake build`, run
`lake env lean tests/integration/FilterContract.lean`, or use `./scripts/check.sh`.
These checks exercise neither byte decoding nor Linux enforcement.

M1.2 adds `FilterDecoder.lean` under [§AR-filter-decoder.checks](../../docs/architecture/AR-filter-decoder.md#checks-malformed-inputs-and-audit-failures). Its 21 guards
cover the canonical bytes, ABI/error precedence, all truncated prefixes, size/count
boundaries, and all 18360 single-byte substitutions. Run after building with
`lake env lean tests/integration/FilterDecoder.lean`.

`test_axiom_audit.py` queries real Lean environments and rejects missing/changed
declarations, source drift, non-theorem claims, unreviewed axiom sets, and actual
transitive custom, `sorryAx`, and compiler-trust axioms. All bad declarations
exist only in disposable ignored fixtures; none supports a project proof.

M1.3 adds `Launch.lean` under [§AR-m1-launch.model](../../docs/architecture/AR-m1-launch.md#model-total-transitions-and-trace-evidence). Its pure guards exercise
successful order, skipped/duplicated/reordered steps, terminal errors,
interruption/cancellation/termination, operation labels and actual decoder/entry
verdicts. Run `lake env lean tests/integration/Launch.lean` after building.

M1.4 adds the source-bound VM record verifier and negative evidence tests in
`test_m1_vm_evidence.py` under [§AR-m1-launch.vm](../../docs/architecture/AR-m1-launch.md#vm-disposable-linux-profile-and-evidence). They reject missing/duplicate
cases, runtime infrastructure errors, unexpected guest execution, wrong errno/
receipts and source drift. They validate archived observations; the separate
`python3 scripts/run_m1_vm.py --prepare` check actually boots the isolated VM.
The Grund tests now also cover native C citations.
