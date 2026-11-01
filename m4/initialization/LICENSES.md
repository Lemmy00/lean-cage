# Initialization proof provenance

The maintained proofs, interface and checker sources are Apache-2.0 under the
repository license. They connect the unchanged native helper and live Lean
policy implementation. Complete frontend/header provenance and upstream notices
remain in `m4/main/LICENSES.md` and the preceding checkpoints.

The existing strictly imported byte computation is reused without modification.
Generated frontend output, Lean exports and compiled artifacts remain ignored
local research outputs. Pinned CompCert, Rocq, Lean, exporter and importer sources
retain their upstream licenses and notices. No host headers or changed toolchain
pins are introduced. Archived evidence retains complete statements, foundations
and artifact identities. See [§AR-m4-controller.initialization](../../docs/architecture/AR-m4-controller.md#initialization-actual-flag-and-pointer-initialization) and
[§DA-m4-controller.initialization](../../docs/decisions/architectural/DA-m4-controller.md#initialization-keep-sequential-stores-visible-during-composition).
