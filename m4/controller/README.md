# Native controller decimal parser

This bounded package follows [§AR-m4-controller.decimal](../../docs/architecture/AR-m4-controller.md#decimal-native-unsigned-decimal-fields) and
[§AR-m4-controller.extraction](../../docs/architecture/AR-m4-controller.md#extraction-independent-controller-slice-and-evidence). It proves the actual `number` function from owned
NUL-terminated bytes, including overflow, invalid input, output/input aliasing,
all returns, every finite prefix and asynchronous loss. See the proposition
review in `docs/reviews/M4-controller-number.md`.

The unchanged CompCert frontend extracts a separate `NumberSlice.v`. The sixteen
authored proof modules use the existing isolated Rocq profile and actual Clight
step interfaces. No native parser or hostile workload is executed on the host.

After preparing and replaying the preceding M4 source and strict bridge profiles:

```sh
python3 m4/controller/check.py
```

The checker refuses stale parent evidence, source or tool drift, missing theorem
records, unchecked proofs, and changed prior compiled identities. It independently
checks the generated AST and all new modules with the kernel. `--collect` writes
an ignored candidate report; it never refreshes reviewed expectations.

This is a source-level parsing result. Policy bounds, Lean plan encoding, argument
provenance, main-routine ordering, Linux enforcement, translation faithfulness,
executable/runtime correspondence and hardware confidentiality remain open under
[§AR-m4-controller.composition](../../docs/architecture/AR-m4-controller.md#composition-remaining-controller-obligations).
