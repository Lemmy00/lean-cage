# DA-m4-routes: Expose failed central connections before expanding setup

Under [§AR-m4-routes.lean](../../architecture/AR-m4-routes.md#lean-checked-semantics-route-and-its-current-blocker) and [§AR-m4-routes.linux](../../architecture/AR-m4-routes.md#linux-pinned-reporting-channel-source-attempt), the native behavior required
by [§FS-assurance.native](../../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence) needs both an ordinary Lean semantics connection
and pinned Linux effect producers. Record actual strict-import and kernel-source
translation attempts separately from successful local source proofs.

Keep the experimental Clight port in an isolated directory at an explicit
inspection revision. It is not a maintained dependency or an alternative
compiler-correctness theorem. Preserve its license and documented semantic gaps.
Do not change existing pins or relax kernel checking to import it. Repair and
review the recursor translation before attempting full semantics equivalence.

Retain the unchanged configured Linux input and its frontend rejection. Do not
erase unsupported types, atomics, fault paths or concurrency to manufacture a
successful import. Require a checked source-refinement route and a complete
reporting-channel producer, including partial-copy failure effects. These open
edges prevent full M4 completion; the bounded parent package has its own review
and acceptance gate. Hardware-channel confidentiality remains M5.
