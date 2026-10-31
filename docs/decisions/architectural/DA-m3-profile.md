# DA-m3-profile: Frozen runtime, copied workspace and distinct run authority

Implement [§FS-workspace.profile](../../functional-spec/FS-workspace.md#profile-supported-environment-and-useful-workloads) and [§FS-workspace.authority](../../functional-spec/FS-workspace.md#authority-objects-and-rights) through
[§AR-workspace.runtime](../../architecture/AR-workspace.md#runtime-frozen-input-and-provenance) and [§AR-workspace.filesystem](../../architecture/AR-workspace.md#filesystem-linux-construction-and-handle-discipline). This is the M3.1 design
decision; implementation and profile acceptance belong to M3.2–M3.7.

## runtime: One complete pinned distribution closure

Select the Linux/amd64 Docker Official Image Python 3.13.18 slim-bookworm filesystem
as an immutable input artifact. It includes Dash, glibc, the dynamic loader, Python
and runtime data in one digest-addressed ordered layer closure. Preserve all package
notices and record its 97 Debian package versions, source names and notice hashes.
Do not run an OCI runtime, an image command, maintainer scripts or a package manager
on the host. M3's own VM helper mounts the prepared filesystem.

A whole root filesystem costs more space and exposes more public executable code
than a hand-trimmed stdlib. It gives a concrete, inspectable first closure without
an implicit dependency on host libraries. Extra executables remain untrusted and
subject to the same object/filter policy. Compatibility is the bounded workload
set, not every command or optional extension in the image. A later reduction or
package refresh requires a new reviewed runtime lock and renewed workload evidence.

## authority: Copy input and reserve identities

Use a fresh private workspace copied from a frozen input tree; never bind a live
caller directory. This deliberately gives snapshot/export semantics, not in-place
editing. It eliminates host hard-link/write aliases by construction, while guest
links, open handles and races still require the filesystem model and proof.

Reserve a distinct UID/GID per concurrent run and use private filesystem, mount,
PID, network and IPC scopes. M2's common nobody UID and public fixture root cannot
support the new authority claim. Kernel root/operator trust remains explicit;
ordinary host/sibling interference remains in scope. No user namespace or general
capability/delegation language is introduced for this first profile.

## supervision: Separate knowledge and resource mechanisms

Build a private authenticated-by-ownership result transport before shell/Python
entry. Console strings cannot authenticate a result once the guest controls output.
Keep entry, termination, cancellation and cleanup knowledge separate.

Use cgroup v2 accounting and containment with supervision outside guest budgets.
Expose the actual accounting, sampling and overshoot semantics. Reject demands for
strict instantaneous memory or cumulative CPU/deadline ceilings that this profile
cannot supply. This is a specified restriction, not permission to relabel a timeout
as a resource proof. Require a new decision if these semantics cannot meet a later
consumer's requirements.

## correspondence: Test the native proof route before expansion

Select CompCert Clight small-step semantics for the first bounded native dispatcher
experiment in [§AR-workspace.experiment](../../architecture/AR-workspace.md#experiment-bounded-first-native-semantics-connection). It can express C memory/integer behavior
with explicit external-effect boundaries; it does not supply Linux concurrency or
a Lean-to-Rocq proof bridge automatically. Keep the existing compiler and Lean pins.
The experiment must expose those gaps or trigger replanning before a larger helper
is advertised as verified. No CompCert dependency or proof claim is added by M3.1.
