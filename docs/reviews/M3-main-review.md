# M3 main integration review

This review covers implementation `77a05d3` and contract `39435e3`, integrated
by fast-forward into `main` from `milikic/leancage-m3-contract`. It follows
[§REQ-proof-integrity](../requirements/REQ-proof-integrity.md#req-proof-integrity-never-substitute-a-weaker-claim-for-an-unfinished-proof),
[§FS-assurance.workspace](../functional-spec/FS-assurance.md#workspace-m3-workspace-model-and-vm-evidence) and
[§RM-roadmap.m3](../roadmap.md#m3-useful-offline-workspace-sandbox). It is a source/proof-statement and regression
review, not an independent production security certification.

## Assessment and correction

M3 is coherent for the named disposable VM profile. The source review covered
policy/plan bounds, object and process model premises, generated filter semantics,
native setup/handle/credential paths, supervision, captured output, snapshots and
export, private framing, and source-bound evidence validation. The exact claim
limits in the original [handoff](M3-handoff.md) remain essential: abstract object
permissions and component traces still require a native/Linux simulation.

One report failure path required correction. After receiving and decoding a
valid helper result, `API.invoke` previously wrote `report.json` directly. If
that write failed, `Main`'s outer exception handler replaced known entry,
termination and cleanup with unknown fields. A partial write could also leave
an incomplete public report at the retrieval path.

[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) and
[§AR-workspace.transport](../architecture/AR-workspace.md#transport-private-events-and-public-result) now separate report
publication from the observed result. The controller writes a temporary file,
publishes by rename, and reports `report_storage` plus a separate diagnostic.
Publication failure returns command status 126 without rewriting the guest's
observed outcome. Preflight/no-run results do not promise a stored report.
Atomic visibility is claimed within the live VM; crash durability is not proved.
The native helper, filter, policy bounds and model theorems are unchanged.

## Verification record

The original `77a05d3` passed `./scripts/check.sh` during this review: 71 Python
tests, 168 Lean guards and all M1/M2/M3 audits. Three new filesystem regressions
pass for successful publication, a missing result directory and failed rename.
They use synthetic observations and disposable files, without host guest execution.

The revised source passed the following checks on 2026-10-31:

- `./scripts/grund.sh fmt --write` and `./scripts/check.sh`: exit 0, 74 Python
  tests (21 M1, 21 M2, 32 M3), 168 Lean guards, all theorem/type/axiom audits,
  strict native compilation and archived evidence checks.
- `python3 scripts/run_m3_vm.py`: exit 0, fresh replay of all 60 workload cases,
  three API checks and six death/cancellation boundaries, with positive controls
  and surviving sentinels. Its transcript SHA-256 is
  `7f9c8d92c09690244207ffb5b62202536ae11303a7cce49fad865f8296282183`.
- `python3 scripts/run_m3_vm.py --check-artifacts`: exit 0; all 70 recorded
  artifacts match. The replay binds 69 source identities; the M3 theorem audit
  binds 84 source/dependency/evidence identities.
- The live Lean query preserves all 419 M3 declaration names, full types and
  transitive axiom sets. The 445 M1 and 274 M2 declarations also pass their
  preserved audits. The only logical foundations remain `propext`,
  `Classical.choice` and `Quot.sound`.
- M1/M2 raw VM evidence, the independent M1 baseline, all three native helper
  sources, the M3 filter and dependency/toolchain pins are byte-identical to
  `77a05d3`. `git diff --check` passes.

The original VM evidence remains recoverable at `77a05d3`; new evidence identifies
the changed controller and source revision rather than relabelling the old run.
Only reviewed source/dependency/evidence fingerprints changed in the theorem
manifests; no statement, claim or axiom expectation changed. These local results
do not pre-empt the separate hosted CI result for the published commit.

## Next assignment

[§RM-roadmap.m4.entry](../roadmap.md#m4entry-next-assignment--m41-native-semantics-feasibility) defines the next worker's bounded M4.1
native-semantics experiment, owned files and acceptance criteria.
[§RM-roadmap.m4.packages](../roadmap.md#m4packages-integrated-product-deliveries) sequences the subsequent Lean connection,
controller/helper composition, pinned Linux effects, executable/runtime chain
and composed profile review. The original M2 and M3 correspondence ledgers stay
open. An AST, source hash, differential test or Rocq result with an unchecked
Lean mapping cannot be described as end-to-end Lean verification.

M5 hardware observations and M7 production closure remain unchanged. Completed,
reviewed work belongs on `main`; a temporary worktree may isolate active work,
but it must be integrated after passing its gates.
