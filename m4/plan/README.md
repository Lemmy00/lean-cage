# Live plan and native decimal connection

This package implements [§AR-m4-controller.plan](../../docs/architecture/AR-m4-controller.md#plan-live-lean-plan-fields-and-their-decimal-bytes).
It proves the actual Lean launch-plan layout and decimal UTF-8 bytes, imports the
numeric byte interface with the pinned strict profile, and connects its exact
result to native source executions. Read the [proposition review](../../docs/reviews/M4-plan.md)
for the remaining translation and runtime boundaries.

After replaying the preceding profiles, run from the repository root:

```sh
python3 m4/plan/check.py
```

The gate rebuilds both Lean modules and all five Rocq modules, exports the actual
computational root, rejects disabled kernel checks, audits every theorem's full
type and transitive foundations, and runs an independent kernel check. It
preserves the preceding 83 native decimal records, their artifacts and the entire
frame checkpoint. `--collect` writes an ignored candidate report and never
refreshes reviewed expectations.

The pure prepend of the executable name exposes the argument-layout boundary;
it does not certify the Lean runtime or Linux's argument table. Native main-loop
ordering, input ownership, parent identity, translation faithfulness, executable
correspondence, Linux enforcement and hardware channels remain open. No native
workload is executed on the shared host.
