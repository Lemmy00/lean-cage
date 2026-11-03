# Checked recursive representations and CompCert type relation

This package implements the representation prerequisites of
[§AR-m4-routes.reporting.bridge](../../docs/architecture/AR-m4-routes.md#reportingbridge-repair-the-shared-semantics-bridge)
and [§AR-m4-routes.reporting.types](../../docs/architecture/AR-m4-routes.md#reportingtypes-relate-the-actual-type-representations).

It imports the actual exported datatype prefix of `CC.Step`, checks the full
`CC.Ty` and `CC.Stmt`/`CC.LStmts` recursors and every constructor reduction, and
proves a total representation bijection with the pinned CompCert `Ctypes.type`.
Named constructor equations prevent a tag permutation from satisfying the
contract. The integer, alignment, identifier and calling-convention codecs are
total and have checked inverse laws.

Use the existing bridge and route preparation first. The input is the unchanged
`ported-step.ndjson` produced by `m4/routes/check.py`, at its recorded hash.
Run from the project root:

```sh
python3 m4/types-bridge/check.py --collect
python3 m4/types-bridge/check.py
```

The first command writes an ignored candidate under `.tools/m4/types-bridge`.
Normal replay compares the checked declaration types, foundations, authored
inputs and compiled artifact identities with the evidence record. It also checks
disabled guardedness, an unresolved recursor, a wrong signature and an opaque
helper whose reductions cannot be checked.

The derived importer is built in a separate directory. `derivation.json` binds
the original and changed source bytes and the patch. The accepted importer,
upstream inspection checkout, native sources, VM profiles and dependency pins
remain intact. No workload or kernel experiment runs on the host.

The importer is derived from `rocq-lean-import` under LGPL-2.1. Its upstream
notices and license remain in the prepared copy; the patch does not relicense
them. The inspected Certora/clean/CompCert sources retain their original upstream
license as described in `m4/routes/README.md`. No upstream source closure is
vendored here. The hand-written helper recursors follow the exported constructor
interfaces, and the type codecs refer to those interfaces and pinned CompCert.

These Rocq results supply a representation producer. They do not prove the
faithfulness of the whole Lean translation or a native/Linux security property.
The source transition, memory, effect and executable connections remain required
by [§AR-m4-routes.reporting.chain](../../docs/architecture/AR-m4-routes.md#reportingchain-required-producer-to-consumer-chain).
