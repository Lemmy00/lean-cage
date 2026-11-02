# Maintained parent composition work

This package implements [§AR-m4-parent.history](../../docs/architecture/AR-m4-parent.md#history-selected-execution-history) and [§AR-m4-parent.inputs](../../docs/architecture/AR-m4-parent.md#inputs-owned-input-representation) from
the continuation assignment. It preserves the frozen review input under
`m4/parent-checkpoint/`. It is under development until its full statement review,
composition cases, negative controls and maintained gate pass.

`TraceRegion.v` carries the actual observation history through certificates.
`TraceExecution.v` splits every execution at its selected source endpoint.
`ParentTrace.v`, `TraceInitialization.v` and `NumericTrace.v` compose numeric
parsing, parent admission and initialization with that history. The earlier
state-only certificates remain compatibility lemmas; the trace contracts are
the maintained public interface. `InputRepresentation.v` exposes allocated
strings, argument cells and numeric mappings in the actual starting memory.

The public universal contracts allow all aliases admitted by their explicit
premises. Allocated examples use fresh storage. Neither establishes physical
process argv provenance, persistent parent identity or Linux behavior.

The inventory rejects unsupported Rocq syntax and audits all supported named
definitions as well as theorem forms, so a proof-valued definition cannot hide
behind a keyword change. Native controls compile unchanged C and three actual
parent-guard/narrowing/comparison edits, and kernel-check whole-main identity.

Replay after the existing dependency chain:

```sh
python3 m4/parent/check.py
```

`--collect` writes only an ignored report for reviewing full statements. It does
not refresh maintained expectations. Full M4, the ordinary Lean proof connection,
compiler-semantics compatibility and pinned Linux effects remain open. This
package performs no guest execution on the host.
