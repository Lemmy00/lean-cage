# Runtime scenario tests

This directory will hold tests of [§FS-filter-loading](../../docs/functional-spec/FS-filter-loading.md#fs-filter-loading-prove-a-small-real-launch-boundary-first) and the growing supported
subset in [§FS-compatibility.matrix](../../docs/functional-spec/FS-compatibility.md#matrix-initial-compatibility-matrix). There are no runtime scenarios at M0.

For each implemented behavior, cite the specific functional contract, test useful
allowed actions and denied actions, and cover failure paths. Run hostile native
programs only in an isolated integration environment with recorded artifact and
platform identities. Tests provide behavioral evidence, not formal proofs.
