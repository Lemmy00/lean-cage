# Integration tests

The M0 tests validate [§AR-tooling.grund](../../docs/architecture/AR-tooling.md#grund-local-wrapper-and-citation-scope) and [§AR-tooling.checks](../../docs/architecture/AR-tooling.md#checks-one-development-gate) against the pinned
Grund binary. They copy the documentation/configuration into disposable fixtures,
then verify valid Lean references, rejection of a dangling reference, and exclusion
of dependency sources. They do not modify project documents or global settings.

Run them through `./scripts/check.sh`, or separately:

```sh
python3 -m unittest discover -s tests/integration -p 'test_*.py' -v
```

Later tests here must cite the architecture contracts for the component boundaries
they exercise. Passing integration tests is evidence of tested behavior, not a
substitute for a formal refinement or isolation theorem.
