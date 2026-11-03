# Foundation CI repair — 2026-11-03

The [foundation run for `462b54b`](https://github.com/Lemmy00/lean-cage/actions/runs/41668854983)
stopped before proof compilation with `Source/dependency identities differ from
the reviewed manifest`. The reviewed changes in `FS-assurance.md` and
`FS-compatibility.md` had stale fingerprints, and the root integration-test
inventory had not recorded the new output-capture test from `34d6dae`.

The reporting aggregate had passed because its current-helper route omitted
foundation input validation. It therefore supplied insufficient coverage for
the foundation CI result; the earlier reporting pass remains valid only for the
inputs that route actually checked.

## Repair and preservation

Under [§AR-tooling.checks](../architecture/AR-tooling.md#checks-one-development-gate), the aggregate now checks all three current foundation
input inventories before reusing reporting proofs. The check lists mismatched
paths and never updates expectations or invokes a build. Regression tests cover
changed and newly discovered inputs in each package.

The capture integration test now explicitly builds its imported Lean workspace
library. Previously, the foundation gate discovered that test before building
the workspace package; a prepared local checkout hid the missing prerequisite.

The three foundation manifests change only `source_sha256`: the reviewed spec
updates, capture/fingerprint tests and the dependent M2-manifest identity. Module
inventories, named claims, theorem types, axiom sets, toolchain and scope fields
are identical to `462b54b`. No Lean/C proof or runtime implementation changed.

The existing compiler amendment checker binds these exact input updates and the
single added aggregate command. It also checks preserved foundation-payload
digests. Reporting source, connection and compiler records change only their
input-fingerprint maps. Their declarations, foundations, witnesses, checked
artifact hashes and kernel-check receipts remain identical. The existing archived
preimages are unchanged. Normal checks still reject unreviewed input changes.

## Validation

`./scripts/check.sh` and `./scripts/check_m4_all.sh` both passed with exit code 0
on the repaired inputs. The reporting path reused matching proof artifacts and
passed the new foundation-input guard. Their logs are retained locally as
`.tools/assurance/foundation-ci-repair-check.log` and
`.tools/assurance/foundation-ci-repair-reporting.log`. The fresh GitHub run on the
repair commit supplies the clean-checkout result. VM inputs and workload behavior
are unchanged, so archived VM evidence is checked without replaying workloads.

The accompanying roadmap correction restores seLe4n as a named planned backend
at [§RM-roadmap.m6.sele4n](../roadmap.md#m6sele4n-a-sele4n-backend-using-the-same-portable-contracts), with a real execution/refinement delivery and independent
entry after the accepted Linux baseline.
