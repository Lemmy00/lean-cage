# FS-host-boundary: Preserve host authority and bounds for arbitrary VM bytes

Implement [§FS-linux-product.transport](FS-linux-product.md#transport-carry-requests-and-results-across-the-vm-boundary) and [§FS-linux-product.proofs.application](FS-linux-product.md#proofsapplication-the-complete-application-guarantee)
for the public CLI and `Workspace` API. This is the host guarantee; delivery
status remains in [§RM-roadmap.m5](../roadmap.md#m5-verify-the-complete-application-control-path). A valid frame does not establish that its
reported guest observations are true.

## caller: Preserve the public request and result interfaces

Keep `Workspace`, `Outcome`, `Cancellation`, `check`, `run`, `validate`, `report`
and the documented CLI arguments and version-1 policy/result formats. A native
gateway must preserve the actual caller's policy bytes, paths, optional stdin,
output destination, cancellation token and timeout, including type/size errors.
Use fixed executable arguments; request data never selects a host command.
Each returned value comes from the same engine invocation and identified bundle.
Before request dispatch, require the actual running host engine's copied bytes
to match the selected bundle's engine identity. Selecting a different bundle
must not silently advertise its unused host executable as the running engine.

`Outcome.observation` exposes the received engine metadata through the bounded
native value projection. At the original `Workspace` result return, its builtin
graph comes from that same response, including the lossless filesystem-decoded
output spelling. Path presentation callbacks do not receive or replace that
graph. `Outcome.output` keeps the existing path-constructor presentation, and
`Outcome.json()` keeps its current-field presentation behavior. A caller may
customize that path constructor or mutate returned presentation records; those
changes do not supply a new engine observation. Manually constructed or
reinitialized outcomes without received metadata expose `observation = None`.
No observation or presentation object is accepted as filesystem authority.
The native `Outcome` type keeps its maintained method, slot and getset bindings;
ordinary class mutation and instance-class reassignment cannot replace them.
Its instance fields and received presentation graph remain mutable, and direct
construction and explicit reinitialization retain their existing behavior.

CLI timeouts use a positive decimal duration, at most 128 bytes with exponent
magnitude at most 400, rounded up to nanoseconds and capped at 3660 seconds.
Library timeouts preserve their positive finite binary64 value with the same
outward nanosecond rounding and cap. Reject unsupported numeric inputs explicitly.

Gateway buffers remain rooted or copied for their complete use. Released-GIL
calls cannot use borrowed mutable storage or leave Python exceptions unchecked.
Process/thread/runtime and cancellation handling retain explicit source contracts.

Response provenance covers each actual committed stream prefix while its write
may still be blocked. It does not require a later acknowledgement or engine
return. Bind the source request and payload to the same process lifetime,
endpoint and open file description; a descriptor number alone is insufficient.
Partial acknowledgements advance the source writer only by their actual counts.
Kernel progress and later error, loss or acknowledgement are separate observations
and cannot publish the same committed bytes twice.

### caller.initialization: Reject nested initialization before changing module state

Check the supported interpreter before accessing mutable initialization state.
An ordinary callback may attempt to initialize the same native extension again.
Reject that nested entry before bootstrap or class-global changes. Keep the
guard active throughout the actual initializer and clear it on every returned
success or failure. A sequential retry after failure remains possible until
first success. A failed or lost attempt cannot authorize request execution.

After the first successful initialization of a loaded native image, reject any
later direct initializer entry before changing bootstrap or class globals.
Normal cached imports remain available. Loading that same image under a new
module name must not reset class roots while an existing public call uses them.
This is the native image's initialization compatibility rule; aliases do not
create independent native application state.

Sequential retries retain their actual earlier class-global state. Prove each
replacement from that state; do not assume a fresh loader image or vacant C
root on every initialization. An overwritten unreleased reference remains an
explicit retained allocation and cannot supply active reference ownership or
a reclamation observation.

A returned initialized module follows the actual successful import, attribute
lookup, module creation and class-publication path. Each publication uses the
same returned reference and name checked at that call. Failed creation or
publication cannot become a usable module. Public Python attribute mutation
and cached-object aliases do not replace the source-owned C roots.

Heap-type creation can expose the real public classes through Python's weak
subclass registry before module initialization returns. An exposed constructor
or request entry cannot use incomplete module state as authority. The workspace
constructor, path-result conversion, request exchange and CLI entry check the
actual successful-initialization flag before their first effect. Before success
they return an error without starting an engine or changing CLI signal handlers.

## ownership: Derive fresh objects and retain their identity

The trusted operator selects the identified bootstrap bundle, host account and
publication parent. Bootstrap bytes and the namespace bindings used to load the
extension, engine, controller, VM executable and runtime closure remain protected
throughout the request, including their ancestors. Immutable inode contents alone
do not protect a later pathname lookup. Trusted operator/root reconfiguration and arbitrary hostile
code with the host account's memory/descriptor privileges are outside this
profile. This does not make a caller path, an existing file or a VM-provided
name private. Concurrent verified requests, hostile input contents, changing
input trees, shared-parent name interference and arbitrary VM output remain.

The supported initialized mount profile uses the host UID mapping consistently
across permitted aliases. Ordinary bind aliases remain covered. Idmapped mount
aliases are outside this profile until the physical model includes their mount
views. Mount configuration and its privileged changes remain operator setup;
an observed mount ID alone does not establish an identity mapping.

The initialized system root and its `tmp` binding have protected lifetime
identities, including the visible object when `/tmp` is a mount cover. Removing
or replacing that system binding, or reconfiguring its mount resolution, is
operator authority outside the supported request execution profile. This
condition applies when the host account is root as well as when it is unprivileged.
The initialized system-root directory is owned by UID 0 and is not writable by
its group or other users; these are facts about the system anchor, not a
restriction on the host account's UID.
It does not identify a newly created run path: the application must connect its
actual `/tmp` open to that initial object, retain the opened parent, and compose
the actual reserved child name and later child uses. Ordinary foreign users
remain subject to their actual per-operation DAC checks.

Host Python callbacks retain their ordinary signal, reentry and configuration
behavior, including mutation of objects passed to them or already publicly
reachable. They do not access the gateway's private C storage, owned IPC
descriptors or private Python object graphs. Enumerating and mutating private
objects through GC introspection is host-memory access outside this profile,
just as guessing descriptor numbers is descriptor access. The application must
derive graph ownership from its actual allocations, retained roots and argument
exposure. Freshness alone does not exclude GC introspection. Publicly returned
`Outcome` records remain mutable presentation objects. The same restriction
applies to other native code in the host process. Holding the GIL or setting
close-on-exec alone does not give descriptor exclusivity against arbitrary code
in that process.

External host code also has the host account's filesystem authority. Private
pathname or descriptor acquisition by that code is outside the same host-code
profile; private modes do not deny a callback running as their owner. Profile 1
permits callback changes to public inputs, outputs and configuration, with their
actual filesystem operations recorded on the shared history. It does not treat
such operations as different-UID interference or assume that all callback
effects preserve private state. Each callback's permitted authority is an
external caller requirement. UID, mode, ACL or sticky-bit reconfiguration of
active trusted parents is operator/host-account authority reconfiguration,
including when that parent is publicly named; it is outside the same profile.
Permitted public data/name changes do not include those authority changes.
Application-mediated path selection, including
private aliases, remains an application obligation, as does deriving which
fresh objects and retained references belong to each private run.

An actual engine or native caller exit stops that process's source execution.
Resource release is a separate observed progression: a partial teardown retains
every surviving descriptor and working-directory reference, and only an actual
completion observation establishes that those resources are empty. A lost SDK
reply or EOF does not establish process exit or completed release. Keep lifetime
births, source transcripts, published objects and private orphan provenance after
exit; retiring one process does not establish that its controller or VM descendants
have exited or been reaped.

The application creates each temporary/run/staging directory freshly, requests
private permissions, opens and retains its directory identity, and publishes
only freshly created objects. Other verified requests use their own capabilities;
untrusted peers cannot gain private descriptors through this application.
Primitive Linux contracts expose actual objects, aliases, access checks,
descriptor reuse, interruptions, errors and permitted concurrent changes.
Application-owned raw directory, file and IPC descriptors close on backend exec;
the controller/VM's intended standard streams come from the explicit spawn
mapping. A spawn error or lost observation does not establish that exec or
reaping completed.

Host paths supplied as policy, workspace, stdin, output or report inputs cannot
enter a component beginning `.leancage-private-`. Relative selection starts from
the retained inherited working-directory object, not a pathname obtained by
reopening `getcwd`. Retain each ancestor and open without following
links. Reject private attributes on every opened ancestor and final input object,
including aliases of an existing private object. Snapshot traversal applies
the same checks recursively. Accept only a definite missing-attribute observation;
unsupported attribute lookup is an error, since it does not establish absence
on an aliased object. Bootstrap reads use their separate trusted role.
This host path restriction preserves the version-1 guest policy format.

Each validator/VM directory and publication stage has a fresh reserved name.
Create it exclusively under the retained parent, verify its identity and private
permissions, and never adopt another request's existing directory. Randomness
chooses names; successful exclusive creation establishes freshness. Publication
stages stay in the target filesystem for atomic rename. A lost setup operation
may leave a private orphan; it does not authorize adoption or block use of a
different fresh name. VM/validator private roots are marked before content is
created. A publication stage becomes public only at its final nonreplacement.

Release a validator's backing directory only after an actual successful wait
status establishes reaping, including a rejected policy's nonzero exit status.
An unknown spawn/wait outcome retains its reserved directory name and contents;
stdout EOF or an error string does not establish that the child has stopped.
This prevents a delayed child pathname lookup from entering another request's
later directory at a reused name.
The same rule applies to a returned VM spawn error: without a definite no-child
observation, retain its backing directory and report cleanup as unknown. A
failure before any spawn attempt can still report that the VM was not started.

Every artifact operation is relative to retained directories with checked
components. No final-component-only no-follow check establishes ancestor safety.
Never overwrite an existing target or another run. If an operation's success is
lost, retain uncertainty; do not turn that loss into permission to replace or
delete an unrelated object. Linux UID equality alone is not a privacy proof.

## lookup: Reject unsupported directory-name semantics

Private reserved components and nonreplacement use the actual directory's name
comparison, not an assumption that every Linux filesystem compares raw bytes.
The adapter accepts tmpfs or an ext-family observation with neither casefold
nor directory encryption enabled. Check the retained directory's filesystem
type and, for the ext family, its actual inode flags. Reject unknown types,
unsupported observations and observed casefold/encryption before relative
lookup, enumeration or mutation. Check newly opened directory handles
too, including the initial root and working directory, so traversal cannot enter
an unsupported mounted filesystem. Caller paths still use retained no-follow
ancestors and the existing component/private-attribute checks.

A probe is an observation, not a directory lock. Foreign owners may change
flags and names in their public input directories between operations; retain
those transitions and the actual later lookup semantics. For active trusted
write/private-root parents, derive stable comparison from their retained
authority and the operator/host-account reconfiguration profile in
[§FS-host-boundary.ownership](FS-host-boundary.md#ownership-derive-fresh-objects-and-retain-their-identity). Do not extend that restriction to foreign-owned
public inputs. Ordinary foreign and permitted public callback name/content
changes remain recorded. Keep every probe, opened descriptor, rejection close
and lost reply in the primitive transcript; a failed post-open check does not erase the open.
Trusted bootstrap paths retain their separately protected ancestor contract.

## snapshot: Identify the bytes actually copied

Copy input directories/files through retained, no-follow descriptor operations.
Reject unsupported links/special files, malformed UTF-8 tree names, reserved
`.tmp`, noncanonical paths, depth over 64, components over 255 bytes and paths
over 4095 bytes. Bound directory enumeration before retaining/sorting names.
Enforce the request's workspace byte/inode and stdin bounds while copying,
including partial reads and observed changes. Hash acknowledged copied bytes.
After filling input identities and revalidating the emitted policy, require its
actual host budgets to equal those used for copying. A serialization/parsing
disagreement cannot increase the later stream/export authority.

The resulting `LCTREE1` identity and blob set describe those copied bytes.
They do not assert an atomic view of a live tree or undetected concurrent writes.
Caller input objects never become writable guest backing objects or host output
destinations. The per-run archive/configuration uses only this frozen result and
the accepted request fields; its host writes stay within the fresh run directory.

## transport: Accept only complete bounded consistent framing

Preserve the `LCVM1` prefix, 32-byte request identity, 64-byte bundle identity,
16-byte little-endian record headers and existing tags. Every native read
requests at most 65536 bytes; the executable decoder enforces its own bound
before retaining data. Validate lengths
before allocation/copying, including machine-width conversion.

Reports are at most 65536 bytes each, exports 16 MiB, captures their policy caps,
and blobs their aggregate workspace byte/inode caps. Retained metadata and
transient copies also have explicit bounds. The library may return all permitted
file bytes; do not claim constant memory for that interface.

Require exact identities, supported tags, zero reserved fields, unique non-blob
records, unique correctly hashed blobs, one exact terminal record and observed
EOF. Reject malformed/truncated/trailing/duplicate records and all exceeded
bounds. An error is sticky; a later valid suffix cannot complete a rejected stream.
VM exit alone never completes framing. Diagnostics use capped collectors and
bounded reads, including failure formatting.

## artifacts: Validate all authority before materialization

A total bounded JSON parser rejects duplicate decoded keys and invalid encodings.
This explicitly tightens legacy host report/envelope loading, whose Python JSON
decoder selected the last duplicate value. Such ambiguous reports or stored
envelopes are rejected. Unambiguous version-1 documents retain their shape and
meaning; version-1 policy decoding already rejects duplicate keys.
Typed validation checks profile/runtime/request consistency, run/preflight kind,
capture counts and policy caps, stored-report equality and committed export
presence/absence for every accepted run kind. Represent every failure explicitly.

Validate the complete manifest identity, canonical hex/decimal fields, unique
names, directory hierarchy, inode/aggregate byte bounds, exact referenced blob
set and content digests before publication. Native raw-byte names retain their
manifest identity. The current host materializes supported UTF-8 names only;
an unsupported name yields an incomplete host artifact result with known inner
observations retained. It never silently publishes a partial export as complete.

## publication: Preserve observations through storage and retrieval

Publish validated files and an identity-bound envelope from a fresh private
stage by atomic nonreplacement. A complete artifact result requires complete
transport and all consistency checks. Failure/loss preserves any already
recognized report while leaving captures/exports explicitly incomplete.
Host publication failure changes publication status, error and public exit status;
it does not rewrite known inner entry/cleanup fields.
After any rename attempt, release handles without rolling back files or names.
An error acknowledgement can leave the commit uncertain, so it does not authorize
removing the old staging name or a possibly published object. Pre-attempt failures
still clean up their owned private stage.

Retrieval uses retained directory identities and rechecks the envelope's
request/bundle/policy binding, path hierarchy, aggregate/file/inode bounds and
every returned content digest. A stored digest alone does not prove safe paths,
authority, inner observation truth or the original publisher's identity.

Publication version 1 additionally records a directory attribute written only
by the host publisher while preparing its private stage. Its bound envelope
identifies the stage object and the final parent object/name. The stage name
differs from that final name. Retrieval requires the marker on the retained
target and checks both identities and the actual final parent/name; a private
uncommitted stage cannot satisfy this check. Guest files and serialized metadata
cannot supply that origin. Unsupported attribute storage fails before publication
and preserves known observations. The attribute and envelope bind the same
request, bundle and copied policy. Raw OS paths remain lossless in the stored
typed envelope and public native result.

The marker authenticates the exact envelope with HMAC-SHA256 and a private
32-byte installation key. Trusted preparation identifies that host-owned `0400`
key in the bundle under `.leancage-private-host/publication.key`; request-time
checks verify its metadata, size, private attribute and bytes. Inspect the private
attribute on the same retained key descriptor used for copying. Reject aliases
in caller input roles before reading their contents.
Neither snapshot nor VM image receives the key. The stated crypto contract is
unforgeability for the permitted observed messages and verification outcomes,
not global injectivity of a finite digest. Its public signing-query history
contains exact envelopes whose tags were actually exposed by a committed
publication. Preparing a marker in a private stage and computing an internal
verification MAC do not themselves expose signing queries. A commit with an
error or lost acknowledgement still belongs to that history when its actual
namespace effect exposed the tag. Fixed-time runtime comparison avoids
an application prefix-comparison oracle. Human JSON and typed storage metadata
are bounded by 64 MiB each; all policy, stream and artifact bounds still apply.

## acceptance: Prove and consume the real host implementation

Supply a source-connected finite-prefix theorem for arbitrary VM bytes and
permitted filesystem changes, with explicit primitive/platform contracts and
named later producers. Prove native caller extraction, argument construction,
sequencing, errors and result projection; do not assume a whole host adapter.
Use the same executable Lean programs for the live engine and proofs.

Exercise the actual public caller early with a useful and failing round trip,
then integrate snapshot, stream, validation, publication and retrieval through
both CLI and library. The final identified bundle must pass the affected public
and hostile-frame/snapshot/export/storage acceptance. Kernel-check full theorem
types and transitive assumptions; keep complete records under
[§FS-assurance.evidence](FS-assurance.md#evidence-required-claim-record). VM reaping and truthful inner observations retain their
assigned lifetime/composition producers until those deliveries establish them.
