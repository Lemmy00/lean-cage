import FilesystemCurrentBirth

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

private def filesystemInput : Program.Event → Option (Request × Option Reply)
  | .returned (.filesystem request) reply => some (request, some reply)
  | .lost (.filesystem request) => some (request, none)
  | _ => none

private theorem event_actor_unique {action : ActorAction} {first second : ActorId}
    {initial final : Program.Event} (left : action.eventFor first = some initial)
    (right : action.eventFor second = some final) : first = second := by
  cases action with
  | launch | foreign | retire | nativeRetire => cases left
  | returned owner effect reply =>
    dsimp only [ActorAction.eventFor] at left right
    split at left
    · rename_i firstOwner
      split at right
      · rename_i secondOwner
        exact firstOwner.trans secondOwner.symm
      · cases right
    · cases left
  | lost owner effect =>
    dsimp only [ActorAction.eventFor] at left right
    split at left
    · rename_i firstOwner
      split at right
      · rename_i secondOwner
        exact firstOwner.trans secondOwner.symm
      · cases right
    · cases left

-- §FS-host-boundary.ownership: One source action has one actor and exact syscall input,
-- even when its acknowledgement is absent. A same-tick receipt cannot name a peer call.
theorem filesystem_action_origin_unique {action : ActorAction} {first second : ActorId}
    {initial final : Request} {before after : Option Reply}
    (left : action.eventFor first = some (Program.filesystemPrefixEvent (initial, before)))
    (right : action.eventFor second = some (Program.filesystemPrefixEvent (final, after))) :
    first = second ∧ initial = final ∧ before = after := by
  have actors := event_actor_unique left right
  subst second
  have events := Option.some.inj (left.symm.trans right)
  have inputs := congrArg filesystemInput events
  have pairs : (initial, before) = (final, after) := by
    cases before <;> cases after <;> simpa only [Program.filesystemPrefixEvent, filesystemInput, Option.some.injEq] using inputs
  exact ⟨rfl, congrArg Prod.fst pairs, congrArg Prod.snd pairs⟩

-- §FS-host-boundary.ownership: A real successful private mkdir cannot take the retained
-- no-birth case. Kernel freshness and the exact same namespace delta force its catalogue entry.
theorem CurrentRootCreation.acknowledged {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {before after : Capabilities} {oldCatalogue newCatalogue : Catalogue runtime all}
    {tick : ActorTick runtime} {position : Nat} {engine : EngineState} {request : Request} {reply : Reply}
    (choice : CurrentRootCreation before oldCatalogue after newCatalogue tick position)
    (actual : kernel.step (tick.before.project engine) request (some reply) tick.after.shared)
    (mkdir : request.op = .mkdirAt) (component : Directories.component request.left = true)
    {parent : Handle} (reference : engine.references request.first = some parent)
    (acknowledged : reply.1 = 0 ∧ reply.2.isEmpty = true) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root), birth.tick = tick ∧
      birth.position = position ∧ Sigma.mk root birth ∈ newCatalogue ∧ after = before.addRoot root := by
  cases choice with
  | retained caps catalogue entries =>
    obtain ⟨object, fresh, allocated, absent, bound⟩ := kernel.mkdir_fresh _ _ _ _ _ actual mkdir reference
      component acknowledged.1 acknowledged.2
    change tick.before.shared.entries parent.object request.left = none at absent
    rw [entries] at bound
    rw [absent] at bound
    cases bound
  | created root birth current ordinal caps catalogue =>
    exact ⟨root, birth, current, ordinal, by rw [catalogue]; exact List.mem_cons_self, caps⟩

-- §FS-host-boundary.ownership: This is the exact acknowledged caller/root association,
-- including its retained parent object and raw component, not only existence of some birth.
theorem CurrentRootCreation.acknowledged_origin {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {before after : Capabilities} {oldCatalogue newCatalogue : Catalogue runtime all}
    {tick : ActorTick runtime} {position : Nat} {actor : ActorId} {engine : EngineState}
    {request : Request} {reply : Reply}
    (choice : CurrentRootCreation before oldCatalogue after newCatalogue tick position)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, some reply)))
    (present : tick.before.actors actor = some engine)
    (mkdir : request.op = .mkdirAt) (component : Directories.component request.left = true)
    {parent : Handle} (reference : engine.references request.first = some parent)
    (acknowledged : reply.1 = 0 ∧ reply.2.isEmpty = true) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root), birth.tick = tick ∧
      birth.position = position ∧ Sigma.mk root birth ∈ newCatalogue ∧ after = before.addRoot root ∧
      root.actor = actor ∧ root.parent = parent.object ∧ root.name = request.left := by
  obtain ⟨root, birth, current, ordinal, member, caps⟩ := choice.acknowledged
    (selected_filesystem_step tick action present) mkdir component reference acknowledged
  have birthAction := birth.action
  rw [current] at birthAction
  obtain ⟨actorSame, requestSame, observedSame⟩ := filesystem_action_origin_unique action birthAction
  have earlier := birth.present
  rw [current, ← actorSame] at earlier
  have engineSame := Option.some.inj (present.symm.trans earlier)
  have birthReference := birth.reference
  rw [← engineSame, ← requestSame] at birthReference
  have parentSame := Option.some.inj (reference.symm.trans birthReference)
  exact ⟨root, birth, current, ordinal, member, caps, actorSame.symm,
    ((congrArg Handle.object parentSame).trans birth.parentObject).symm,
    birth.name.symm.trans (congrArg Request.left requestSame).symm⟩

end LeanCage.Host.Kernel
