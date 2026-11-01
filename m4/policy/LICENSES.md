# Policy-bound proof provenance

The new maintained proof, interface and checker sources are Apache-2.0 under the
repository license. They connect the unchanged Apache-2.0 native helper and live
Lean policy implementation. The actual frontend/header provenance and notices
are retained by `m4/main/LICENSES.md` and its preserved checkpoint.

Generated CompCert/frontend output, Lean exports and compiled proof artifacts
remain local ignored research outputs. The pinned CompCert, Rocq, Lean, exporter
and importer keep their respective upstream licenses and notices. This package
does not redistribute the full helper's preprocessed host headers or change any
toolchain pin. The archived proof log reports statements, foundations and
artifact identities. See [§AR-m4-controller.bounds](../../docs/architecture/AR-m4-controller.md#bounds-actual-policy-bound-validation) and [§DA-m4-controller.bounds](../../docs/decisions/architectural/DA-m4-controller.md#bounds-check-the-real-short-circuit-sequence).
