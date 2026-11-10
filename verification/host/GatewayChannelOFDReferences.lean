import GatewayChannelReferences
import FilesystemProcesses

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.primitives: Socket queue authority follows the original
-- open-file-description lifetime. An O_PATH inode alias with another OFD
-- neither consumes this queue nor keeps this socket file alive.
structure SocketLifetime where
  object : ObjectId
  description : DescriptionId

def SocketLifetime.matches (socket : SocketLifetime) (handle : Handle) : Prop :=
  handle.object = socket.object ∧ handle.description = socket.description

inductive SDKReferenceOwner where
  | native (process : NativeToken)
  | engine (actor : ActorId)
  | child (process : ProcessToken)

-- All current support views are sampled here. A stored execution snapshot
-- is history, so it does not create a current SDK or retiring reference.
inductive SocketReferencePlace where
  | native (process : NativeToken) (descriptor : UInt64)
  | retiring (process : NativeToken) (descriptor : UInt64)
  | engine (actor : ActorId) (descriptor : UInt64)
  | child (process : ProcessToken) (descriptor : UInt64)
  | support (owner : SDKReferenceOwner) (descriptor : UInt64)
  | foreign (process : Nat) (descriptor : UInt64)
  | kernel (reference : Nat)

structure SocketReferenceSnapshot where
  population : Population
  native : NativeProcesses
  children : Processes
  support : SDKReferenceOwner → UInt64 → Option Handle
  foreign : Nat → UInt64 → Option Handle
  kernel : Nat → Option Handle

def SocketReferenceSnapshot.at (snapshot : SocketReferenceSnapshot) : SocketReferencePlace → Option Handle
  | .native process descriptor => (snapshot.native.references process).bind (fun table => table.handles descriptor)
  | .retiring process descriptor => (snapshot.native.retiring process).bind (fun table => table.handles descriptor)
  | .engine actor descriptor => (snapshot.population.actors actor).bind (fun engine => engine.references descriptor)
  | .child process descriptor => (snapshot.children.references process).bind (fun table => table.handles descriptor)
  | .support owner descriptor => snapshot.support owner descriptor
  | .foreign process descriptor => snapshot.foreign process descriptor
  | .kernel reference => snapshot.kernel reference

def SocketReferenceSnapshot.released (snapshot : SocketReferenceSnapshot) (socket : SocketLifetime) : Prop :=
  ∀ place handle, snapshot.at place = some handle → ¬ socket.matches handle

def SocketReferenceSnapshot.held (snapshot : SocketReferenceSnapshot) (socket : SocketLifetime) : Prop :=
  ∃ place handle, snapshot.at place = some handle ∧ socket.matches handle

theorem SocketReferenceSnapshot.held_not_released (snapshot : SocketReferenceSnapshot) (socket : SocketLifetime)
    (held : snapshot.held socket) : ¬ snapshot.released socket := by
  obtain ⟨place, handle, present, identity⟩ := held
  exact fun absent => absent place handle present identity

theorem SocketReferenceSnapshot.retained_native
    (snapshot : SocketReferenceSnapshot) (socket : SocketLifetime) (process : NativeToken)
    (table : NativeReferences) (descriptor : UInt64) (handle : Handle)
    (current : snapshot.native.references process = some table) (held : table.handles descriptor = some handle)
    (identity : socket.matches handle) : ¬ snapshot.released socket := by
  intro absent
  apply absent (.native process descriptor) handle _ identity
  simp only [SocketReferenceSnapshot.at, current, Option.bind_some, held]

theorem SocketReferenceSnapshot.retained_retiring
    (snapshot : SocketReferenceSnapshot) (socket : SocketLifetime) (process : NativeToken)
    (table : RetirementResources) (descriptor : UInt64) (handle : Handle)
    (current : snapshot.native.retiring process = some table) (held : table.handles descriptor = some handle)
    (identity : socket.matches handle) : ¬ snapshot.released socket := by
  intro absent
  apply absent (.retiring process descriptor) handle _ identity
  simp only [SocketReferenceSnapshot.at, current, Option.bind_some, held]

theorem SocketReferenceSnapshot.retained_engine
    (snapshot : SocketReferenceSnapshot) (socket : SocketLifetime) (actor : ActorId)
    (engine : EngineState) (descriptor : UInt64) (handle : Handle)
    (current : snapshot.population.actors actor = some engine) (held : engine.references descriptor = some handle)
    (identity : socket.matches handle) : ¬ snapshot.released socket := by
  intro absent
  apply absent (.engine actor descriptor) handle _ identity
  simp only [SocketReferenceSnapshot.at, current, Option.bind_some, held]

theorem SocketReferenceSnapshot.retained_child
    (snapshot : SocketReferenceSnapshot) (socket : SocketLifetime) (process : ProcessToken)
    (table : ChildReferences) (descriptor : UInt64) (handle : Handle)
    (current : snapshot.children.references process = some table) (held : table.handles descriptor = some handle)
    (identity : socket.matches handle) : ¬ snapshot.released socket := by
  intro absent
  apply absent (.child process descriptor) handle _ identity
  simp only [SocketReferenceSnapshot.at, current, Option.bind_some, held]

-- The full snapshot may contain an inode alias. Its distinct OFD is recorded
-- without pretending it is absent or that its holder can read this socket.
theorem different_description_not_socket (socket : SocketLifetime) (handle : Handle)
    (different : handle.description ≠ socket.description) : ¬ socket.matches handle := by
  intro identity
  exact different identity.2

end LeanCage.Host.PrivateStreams
