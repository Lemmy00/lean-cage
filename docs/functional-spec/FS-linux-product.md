# FS-linux-product: A reusable Linux workspace with an explicit trust boundary

Serve [§GOAL-native-isolation.outcome](../goals.md#outcome-useful-constrained-execution) and [§GOAL-reuse](../goals.md#goal-reuse-extend-milestones-without-discarding-their-foundations) with one buildable, usable product.
This is the revised product contract adopted on 2026-11-03. Its implementation
starts from the existing offline workspace and preserved proof components.
Delivery status is recorded in [§FS-assurance.product](FS-assurance.md#product-product-assurance-levels-and-trusted-components).

## operation: Run a caller's workload through one supported interface

From the repository root, an operator can build the controller, helper and
supported profile bundle, then use `check`, `run` and `report` for their own
policy and inputs. A library caller uses the same typed policy and result code.
The first execution environment is the existing disposable Linux VM; general
host deployment is a separate supported-profile change. No guest runs on the
shared development host.

Retain the workspace behavior in [§FS-workspace.policy](FS-workspace.md#policy-bounded-typed-request),
[§FS-workspace.filesystem](FS-workspace.md#filesystem-snapshots-aliases-and-lifetime),
[§FS-workspace.resources](FS-workspace.md#resources-units-ownership-and-failure) and [§FS-workspace.results](FS-workspace.md#results-entry-cancellation-and-bounded-transport):
offline shell/Python, frozen runtime, private copied inputs, bounded output and
export, resource accounting, cancellation and descendant cleanup. Preserve the
existing exact policy/result versions unless an explicit migration is needed.

The public workflow accepts arbitrary supported policies, not only built-in test
cases. It returns the run's typed report, captured stdout/stderr and permitted
export files. A fresh checkout with documented prerequisites must support the
workflow using pinned downloads, without an agent's private caches or knowledge
of milestone directory names. Existing caches may accelerate repeated runs.

## transport: Carry requests and results across the VM boundary

Before implementation, define the request, input-snapshot and result channel
formats, bounds and ownership in the execution architecture. The host validates
requests and constructs the VM invocation from typed fields. Guest-controlled
bytes must never become host shell commands, paths with authority, or control
frames. Keep trusted result framing separate from guest output and boot logs.

Bound copying, capture and export; reject traversal, symlink and size violations.
Tie each returned report and artifact to the requested run and bundle. Preserve
observed entry/cleanup facts when storage fails. Timeout or VM/channel loss yields
an explicit incomplete result and a cleanup outcome; it never manufactures
successful execution or confirmed cleanup. Cancellation reaches the owned VM and
descendants. Construction and teardown of the VM itself have explicit owners.

## trust: Platform assumptions for the initial product

Publish the exact components and versions trusted by each advertised property.
The initial product may rely on these named boundaries:

| Boundary | Permitted assumption | Required engineering evidence |
|---|---|---|
| Linux | The selected kernel implements the specified filesystem, descriptor, credential, namespace, seccomp, cgroup and process operations | Pinned image/configuration, capability preflight, explicit byte/error/interference contracts and conformance/fault tests |
| Compiler and userspace runtime | The selected Lean/C compiler, linker, loader, libc and runtime execute the identified source with their stated ABI | Reproducible build recipe, locked runtime closure, source/binary identities and deployment checks |
| Hardware and VM | CPU, memory and the selected virtual-machine implementation honor the supported execution model | Recorded environment and isolation configuration; supported functional observations |
| Native adapter | Specifically enumerated helper operations implement their primitive contracts while their source correspondence is being established | Named functions and callers, review and targeted integration tests; separately list any formally connected regions |
| Operator and bootstrap | The trusted operator selects the policy and prepares the declared profile correctly | Policy validation, host/guest preflight, fail-closed setup and documented privileges |

The native adapter is application code, not a Linux theorem. It remains visible
in the product's trusted component list until the application-verification work
supplies its correspondence proofs. Never assume the desired conclusion, such as
"the guest is confined" or "the report is truthful", as an OS effect contract.

Kernel implementation proofs and hardware-channel confidentiality are later
assurance upgrades. Their research does not gate the initial usable product.
Changes to the trusted boundary require a versioned claim/profile decision.
Compiler trust concerns execution of the delivered binaries; it does not permit
unchecked computation, added axioms or skipped kernel checks in a proof.

## proofs: Useful proofs connected to shipped code

The initial product ships an inventory of the actual executable Lean definitions
used for policy validation, policy/filter construction and result decoding, their
checked properties, and the CLI/library consumers that call them. Reuse existing
theorems only where their statements cover those definitions and profile.
Supply missing connections before advertising that property.

At minimum, establish the supported policy's acceptance/rejection and bounds,
its emitted filter's specified decision behavior, and the live decoder's result
validation/publication equations. Include useful accepted inputs as well as
rejection cases. Native reporting/source/compiler results remain attached to
their exact implementation and explicit premises. Kernel checks and full theorem
types remain mandatory for proof claims.

Complete application verification then proves, against the explicit primitive
platform contracts, that the maintained controller/helper establishes the requested
authority before guest entry, fails closed on setup errors, supervises/cancels the
owned descendants, preserves output bounds and reports only justified observations.
This requires correspondence for the actual application code and call sites;
it cannot be replaced by an assumption that the entire native helper is correct.

### proofs.application: The complete application guarantee

This is the target for application verification, not an additional claim of the
delivered core. It covers the public CLI/library, host request/snapshot/VM runner,
VM init and transport, Lean controller, native helper, and artifact publication
and retrieval. Preparing an identified bundle is a trusted operator/bootstrap
action; per-request validation, identity checks and execution are application work.

For an accepted request in the supported profile, prove these connected results:

- The workload starts with only the policy-authorized filesystem, handles,
  credentials and filter. Every failed setup path prevents guest entry. The
  `check` operation reports preflight observations without executing the workload.
- The application owns the relevant run/descendant identities and uses the
  specified resource and cancellation mechanisms on those identities. Distinguish
  a cancellation request, observed guest exit, observed inner cleanup and VM
  teardown. Eventual completion needs stated scheduling and primitive-progress
  assumptions; safety must hold for incomplete executions as well.
- Returned output and exports respect the policy's bounds and authority. Report
  fields are justified by observations of this request; guest bytes, malformed
  frames, channel loss or storage failure cannot manufacture stronger facts.
  Retrieval preserves the binding between the request, bundle, report and files.

Compose source-connected proofs of these results across actual call sites.
Application-side ownership, argument construction, error handling, concurrency
and observation provenance must be established by their producers. Primitive
platform contracts may assume Linux/compiler/runtime behavior at the boundary
in [§FS-linux-product.trust](FS-linux-product.md#trust-platform-assumptions-for-the-initial-product); they may not assume an entire host/native adapter or
any of the conclusions above. Record cryptographic and environment assumptions
where identities or private storage depend on them. Test evidence continues to
establish conformance of the configured deployment, separately from these proofs.

### proofs.entry: Establish actual state at workload entry

The application proof must describe values and owned objects at guest execution,
not just successful operation labels. Its entry-state contract includes:

| State | Required relation to the accepted request and profile |
|---|---|
| Policy and arguments | Exact executable, argv, environment and limits derived from the accepted bytes; bounded storage with the stated ABI and ownership |
| Credentials | The run's leased UID/GID, real/effective/saved/filesystem IDs, empty supplementary groups and capability sets, required securebits and no-new-privileges |
| Handles | Only the intended stdin/stdout/stderr and pre-exec failure pipe; the failure pipe is close-on-exec; no surviving host/control/namespace authority |
| Filesystem | The authorized runtime and copied workspace objects, mount flags, root and working directory; aliases cannot add authority |
| Process scope | The owned namespaces, run/cgroup membership and requested resource settings; only the trusted supervisor may supply the tracing/entry observation |
| Filter and signals | The exact proved filter installed under the supported ABI, controlled dispositions/mask, and no unsupported inherited filter state |

The entry gate establishes credential/handle/filter restrictions and the actual
exec arguments from explicit prepared-run inputs. Workspace construction proves
the identity, object and namespace/cgroup producers for those inputs. Both are
needed for the complete authority result. Every failed setup branch prevents
execution; reporting may itself fail or be lost and must then preserve uncertainty.
Preflight success is a separate observation and never implies that a guest ran.

## acceptance: Product completion

The first delivery passes a caller-supplied Python workflow and a shell workflow
through the public interface, with private inputs, returned captures, an exported
file and report retrieval. It also demonstrates policy rejection, a denied effect,
cancellation with cleanup, output/storage failure and a lost VM/result channel.
Use one targeted VM suite on the final changed inputs.

The root build, reusable library and functional source layout are documented.
The bundle names its trusted components and exact proved properties. Ordinary
proof checks cover the shipped core and the new adapters' affected consumers;
unchanged results are reused. There is no requirement to translate Linux source
or build a new compiler bridge to finish this product delivery.
