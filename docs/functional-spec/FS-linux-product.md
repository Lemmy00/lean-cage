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
