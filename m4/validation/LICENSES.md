# Caller string proof provenance

The maintained proof, interface and checker sources are Apache-2.0 under the
repository license. They connect the unchanged native helper and live Lean
policy implementation. The complete frontend/header provenance and notices are
preserved by `m4/main/LICENSES.md` and the preceding checkpoints.

Generated frontend output, Lean exports and compiled proof artifacts remain
ignored local research outputs. Pinned CompCert, Rocq, Lean, exporter and importer
sources retain their upstream licenses and notices. This package does not
redistribute preprocessed host headers or change any toolchain pin. Archived
proof output records complete statements, foundations and artifact identities.
See [§AR-m4-controller.strings](../../docs/architecture/AR-m4-controller.md#strings-actual-caller-string-checks) and [§DA-m4-controller.strings](../../docs/decisions/architectural/DA-m4-controller.md#strings-preserve-library-nondeterminism-through-caller-regions).
