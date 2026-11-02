# Early compiler-semantics compatibility experiment

This bounded experiment follows [§AR-m4-effects.machine](../../docs/architecture/AR-m4-effects.md#machine-source-steps-blocked-calls-and-loss) and the early feasibility
assignment in `M4-CONTINUE.md`. Its target edge is the custom byte/loss machine to
the stock semantics used by the pinned CompCert compiler proofs. It is not a
compiler-correctness or Linux-effect claim.

`CompilerBoundary.v` connects delegated internal parent-machine steps to actual
Clight `step2` and gives an exact equivalence at the real `getppid` boundary:
projecting every permitted local observation into a stock step requires precisely
`parent_external_compatibility`. The local observation constructor does not prove
this producer. The attempted direct producer is retained and fails without an
external-semantics implementation/contract. This naive forward route is too
strong for an overapproximation that permits every signed observation.

The concrete replacement reverses that local refinement direction:
`stock_internal_refines_parent` maps actual stock internal steps into the custom
machine, and `stock_parent_refines_local_under_effect_contract` maps stock parent
returns into it under `parent_external_safety`. This safety contract requires
only unchanged memory and an integer result, rather than requiring the real
kernel to produce every abstractly permitted value. Its actual libc/Linux
producer and composition through the compiler simulation remain unproved.

The stock compiler proof starts from its original C/Clight semantics, not this
custom machine. Loss and waiting additionally need a stuttering/product relation
through the compiler simulation. Frontend/header/libc/linking/loader and Lean
runtime obligations remain separate. No original M4 obligation is closed.

Concrete next routes are: define external semantics satisfying the actual effect
safety contracts and CompCert's external-call properties, then prove stock-to-
custom refinement and compose the compiler simulation; or extend compiler-pass
simulations with the byte/loss semantics and prove that extension. Each route
still needs the pinned Linux producer. Stock compiler correctness cannot be
inherited by identifying the toolchain alone.

After the parent package has been built, replay with:

```sh
python3 m4/feasibility/check.py
```

The parent gate (and therefore the aggregate M4 gate) also invokes this check.
Full types, foundations, the failed direct attempt and compiled identities are
preserved in separate `assurance/m4-compiler-feasibility*` records. Normal replay
compares expectations; `--collect` only writes an ignored report.
