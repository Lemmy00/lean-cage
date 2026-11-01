This experimental profile implements the normalization, primitive-reader and complete imported-frame
connections in [§AR-m4-bridge](../../docs/architecture/AR-m4-bridge.md#ar-m4-bridge-strict-imported-endpoint-and-source-byte-correspondence). It is separate from the established Coq 8.18 profile.

Run from the repository root:

```sh
python3 m4/bridge/profile.py
python3 m4/bridge/check.py
```

Setup uses only `.tools/m4/bridge`, with a private opam root and extracted GMP
packages. It never installs host packages or changes shell setup. The complete
switch export includes pinned versions and package source metadata. CompCert
uses the original pinned source with `-ignore-rocq-version`: that skips its
advertised-version filter, not proof checking. The bootstrap builds its proofs
and does not deploy or execute hostile native workloads.

The checker recompiles the archived Clight AST, all 212 earlier source-proof
modules, the actual Lean public endpoint and exact normalization. It exports the
decoder closure, imports it with strict checks, proves byte and source-reader
correspondence and exact source-frame parsing/validation, audits full statements
and foundations, preserves the original primitive records and artifacts, tests refusal of disabled
guardedness, and independently replays the resulting modules. `--collect` writes
only an ignored candidate report; ordinary checks never refresh expectations.

The importer uses SProp and definitional UIP. These foundations and the semantic
faithfulness of its translation require explicit review. The exact Lean
normalization theorem preserves all returned fields and error messages, while
the exported computational root uses error codes. Direct import of the original
string-bearing closure currently fails because the importer's predeclared
`UInt32` does not match Lean 4.35. Translation review, whole-controller composition,
Linux byte provenance, executable correspondence and all original native/Linux obligations
remain open. See [§AR-m4-bridge.import](../../docs/architecture/AR-m4-bridge.md#import-checked-terms-and-explicit-logical-model) and [§AR-m4-bridge.profile](../../docs/architecture/AR-m4-bridge.md#profile-separate-replay-and-remaining-composition).
