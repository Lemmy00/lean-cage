# Parent checkpoint provenance

The candidate proofs, Lean interface, replay script and documentation are original
Apache-2.0 work under the repository license. They build on the existing local
source proofs and their unchanged pinned dependencies. Copies strengthened from
earlier local proofs remain covered by that license.

The native helper, frontend output, header closure, Lean computation and imports
are unchanged. Upstream CompCert, Rocq, Lean, exporter and importer licenses and
notices remain in their existing locations; see `m4/main/LICENSES.md`,
`m4/plan/LICENSES.md` and `m4/initialization/LICENSES.md`. Generated and compiled
files stay under ignored `.tools/`; the frozen archive records proof-check output
and identities. No new upstream code or toolchain pin is introduced.

This provenance record supports the candidate work in
[§AR-m4-controller.composition](../../docs/architecture/AR-m4-controller.md#composition-remaining-controller-obligations) and does not promote it into an accepted claim.
