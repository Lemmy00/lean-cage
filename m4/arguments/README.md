# Actual guest-argument loop

This package implements [§AR-m4-controller.arguments](../../docs/architecture/AR-m4-controller.md#arguments-actual-guest-argument-length-accumulation) using the unchanged complete
helper translation from `m4/main`. It proves actual initialization, signed loop
control, owned `strlen`, first-invalid-string rejection, unsigned accumulation
and the transition into the previously proved policy bounds.

The conservative string-effect extension retains previous transitions, arbitrary
waiting and terminal loss. All actual prefixes within the selected non-wait
step count preserve memory and have defined live progress. Source acceptance
matches the strictly imported length predicate; the successful total matches the
live Lean UTF-8 argument fold. A failed scan retains only its accepted prefix.

After the parent replays, run:

```sh
python3 m4/arguments/check.py
```

The gate records full propositions and transitive foundations, exact source and
parent artifacts, strict export/import, independent kernel replay and rejected
mutations. `--collect` only writes ignored candidate output. The proposition
review is `docs/reviews/M4-arguments.md`.

Twelve allocated inputs exercise empty strings, 4096/4097-byte boundaries,
count/total limits and raw bytes. Another source witness repeats one pointer.
These constructed states do not establish physical Linux argv provenance or
reachability through preceding main checks. Libc, translation faithfulness,
concurrent writers, remaining controller code, Linux enforcement, the executable
chain and hardware channels remain explicit obligations. M4 remains open.
