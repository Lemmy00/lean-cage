# Functional specification

These are target contracts. M1 proves the pure filter decoder and launch order,
and tests a native filter driver in a disposable Linux VM. M2 adds owned lifecycle
and general filter-action proofs plus capable-VM tests. Use the claim register
to distinguish those model/test results from native/Linux correspondence and
the broader sandbox isolation guarantees that remain future work.

| Contract | Subject |
|---|---|
| [§FS-policy](FS-policy.md#fs-policy-grant-only-explicit-supported-authority) | Authority, validation, and default denial |
| [§FS-launch](FS-launch.md#fs-launch-establish-containment-before-executing-the-guest) | Launch ordering, failure, and cleanup |
| [§FS-lifecycle](FS-lifecycle.md#fs-lifecycle-m2-owned-launcher-lifecycle) | Versioned M2 owned-resource, namespace, privilege, supervision, cancellation and filter contracts |
| [§FS-isolation](FS-isolation.md#fs-isolation-confine-all-supported-guest-effects) | Files, processes, memory, IPC, devices, and network |
| [§FS-observations](FS-observations.md#fs-observations-state-exactly-what-an-attacker-may-observe) | Confidentiality and side channels |
| [§FS-resources](FS-resources.md#fs-resources-define-and-enforce-supported-resource-limits) | Resource bounds and limit behavior |
| [§FS-compatibility](FS-compatibility.md#fs-compatibility-publish-an-explicit-supported-subset) | Supported workloads and Bubblewrap subset |
| [§FS-filter-loading](FS-filter-loading.md#fs-filter-loading-prove-a-small-real-launch-boundary-first) | First executable verification slice |
| [§FS-assurance](FS-assurance.md#fs-assurance-bind-every-advertised-guarantee-to-auditable-evidence) | Evidence, claim status, and assumption register |
