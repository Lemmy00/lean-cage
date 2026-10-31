The new LeanCage proof and audit sources use the repository Apache-2.0 license.
Downloaded tools retain their own licenses; source pins and archive hashes are
recorded in `toolchain-lock.json` under [§AR-m4-bridge.import](../../docs/architecture/AR-m4-bridge.md#import-checked-terms-and-explicit-logical-model).

`strict-importer.patch` modifies rocq-community/rocq-lean-import at
`2d28bbe80e7361bf3ac54f5ef099207fc61ce837`. It is a derivative of its
LGPL-2.1-only source, not Apache-2.0 code. The original notices and license stay
in the downloaded checkout. The LGPL-2.1 text is also available at
`m4/LGPL-2.1.txt`. The patch refuses unchecked elimination and any disabled
kernel typing check, and adapts development APIs to released Rocq 9.3.

leanprover/lean4export at `5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` uses
Apache-2.0. CompCert remains the separately licensed, original pinned source
described in `m4/LICENSES.md`; this profile does not redistribute a compiler binary
or apply a compiler correctness theorem. Rocq, OCaml, GMP, opam and the remaining
packages retain the licenses and notices identified in their pinned source
metadata and local installations. `opam-switch.export` records package metadata,
not a relicensing of those packages.
