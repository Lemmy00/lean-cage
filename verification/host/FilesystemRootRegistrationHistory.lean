import FilesystemAcknowledgedBirth
import FilesystemPrimitiveParents
import FilesystemRunCreation
import FilesystemStagingParents

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: A root use names actual source prefixes/operands and the
-- SAME raw tick. It carries no private-object label, birth, catalogue entry, or owned FD role.
structure PrimitiveRootUse {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (tick : ActorTick runtime) where
  actor : ActorId
  engine : EngineState
  request : Request
  reply : Reply
  action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, some reply))
  present : tick.before.actors actor = some engine
  mkdir : request.op = .mkdirAt
  component : Directories.component request.left = true
  parent : Handle
  reference : engine.references request.first = some parent
  accepted : reply.1 = 0 ∧ reply.2.isEmpty = true
  adapter : PrimitiveAdapterAt runtime initial all tick actor engine request (some reply)
  invocation : Nonempty (RunCreationPrefix adapter.occurrence.logicalBefore request none) ∨
    Nonempty (StagingCall adapter.occurrence.logicalBefore request)

-- §FS-host-boundary.ownership: This is a constructed source-classification history.
-- Other cases must establish the absence of an actual root call at THIS selected tick.
-- It is not a kernel/private-region premise for the final public application guarantee.
inductive RootRegistrationHistory {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) : Nat → Capabilities → Catalogue runtime all →
    List (ActorTick runtime) → Capabilities → Catalogue runtime all → Prop where
  | nil (position : Nat) (caps : Capabilities) (catalogue : Catalogue runtime all) :
      RootRegistrationHistory runtime initial all position caps catalogue [] caps catalogue
  | creation {position : Nat} {before middle after : Capabilities}
      {prior next final : Catalogue runtime all} {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      (choice : CurrentRootCreation before prior middle next tick position)
      (tail : RootRegistrationHistory runtime initial all (position + 1) middle next ticks after final) :
      RootRegistrationHistory runtime initial all position before prior (tick :: ticks) after final
  | other {position : Nat} {before middle after : Capabilities} {catalogue final : Catalogue runtime all}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      (source : ¬ Nonempty (PrimitiveRootUse runtime initial all tick))
      (tail : RootRegistrationHistory runtime initial all (position + 1) middle catalogue ticks after final) :
      RootRegistrationHistory runtime initial all position before catalogue (tick :: ticks) after final

theorem RootRegistrationHistory.included {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {position : Nat}
    {before after : Capabilities} {prior final : Catalogue runtime all} {ticks : List (ActorTick runtime)}
    (history : RootRegistrationHistory runtime initial all position before prior ticks after final) :
    ∀ record ∈ prior, record ∈ final := by
  induction history with
  | nil => exact fun _ member => member
  | creation choice tail ih => exact fun record member => ih record (choice.included record member)
  | other source tail ih => exact ih

-- §FS-host-boundary.ownership: Select the actual acknowledged creation in the SAME
-- completed prefix; catalogue inclusion retains it through later calls and real retirements.
theorem RootRegistrationHistory.registered {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {start : Nat}
    {before after : Capabilities} {prior final : Catalogue runtime all} {ticks : List (ActorTick runtime)}
    (history : RootRegistrationHistory runtime initial all start before prior ticks after final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    (use : PrimitiveRootUse runtime initial all tick) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root), birth.tick = tick ∧
      birth.position = start + position ∧ Sigma.mk root birth ∈ final ∧
      root.actor = use.actor ∧ root.parent = use.parent.object ∧ root.name = use.request.left := by
  induction history generalizing position with
  | nil => cases selected
  | @creation ordinal before middle after prior next final first ticks choice tail ih =>
    cases position with
    | zero =>
      have same : first = tick := Option.some.inj selected
      subst first
      obtain ⟨root, birth, current, count, member, caps, owner, parent, name⟩ := choice.acknowledged_origin
        use.action use.present use.mkdir use.component use.reference use.accepted
      exact ⟨root, birth, current, by simpa only [Nat.add_zero] using count,
        tail.included _ member, owner, parent, name⟩
    | succ position =>
      obtain ⟨root, birth, current, count, member, owner, parent, name⟩ := ih selected
      exact ⟨root, birth, current, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using count,
        member, owner, parent, name⟩
  | @other ordinal before middle after catalogue final first ticks source tail ih =>
    cases position with
    | zero =>
      have same : first = tick := Option.some.inj selected
      subst first
      exact False.elim (source ⟨use⟩)
    | succ position =>
      obtain ⟨root, birth, current, count, member, owner, parent, name⟩ := ih selected
      exact ⟨root, birth, current, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using count,
        member, owner, parent, name⟩

theorem RootRegistrationHistory.append {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {start : Nat}
    {before middle after : Capabilities} {prior next final : Catalogue runtime all}
    {first last : List (ActorTick runtime)}
    (leading : RootRegistrationHistory runtime initial all start before prior first middle next)
    (trailing : RootRegistrationHistory runtime initial all (start + first.length) middle next last after final) :
    RootRegistrationHistory runtime initial all start before prior (first ++ last) after final := by
  induction leading with
  | nil => exact trailing
  | @creation position before middle after prior next final tick ticks choice tail ih =>
    apply RootRegistrationHistory.creation choice
    apply ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trailing
  | @other position before middle after catalogue final tick ticks source tail ih =>
    apply RootRegistrationHistory.other source
    apply ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trailing

-- §FS-host-boundary.ownership: Retirement, native and runtime-only ticks cannot conceal
-- an acknowledged source mkdir. Their explicit kernel effects remain in the shared history.
theorem no_root_use_of_nonfilesystem {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    (kind : actionFamily tick.action ≠ .filesystem) : ¬ Nonempty (PrimitiveRootUse runtime initial all tick) := by
  rintro ⟨use⟩
  exact kind (selected_filesystem_action_family use.action)

theorem no_root_use_of_other_operation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (notMkdir : request.op ≠ .mkdirAt) : ¬ Nonempty (PrimitiveRootUse runtime initial all tick) := by
  rintro ⟨use⟩
  obtain ⟨sameActor, sameRequest, sameObserved⟩ := filesystem_action_origin_unique action use.action
  exact notMkdir ((congrArg Request.op sameRequest).trans use.mkdir)

end LeanCage.Host.Kernel
