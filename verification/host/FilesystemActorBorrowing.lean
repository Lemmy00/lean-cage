import FilesystemProjection

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.acceptance: Runtime and filesystem operations share the actual actor history.
inductive ActorPhysicalPrefix {kernel : Contract} (runtime : ActorRuntime kernel) (actor : ActorId)
    {α : Type} : Program α → World → List Program.Event → World → Prop where
  | stop (program : Program α) (world : World) : ActorPhysicalPrefix runtime actor program world [] world
  | environment {program : Program α} {before middle after : World} {events : List Program.Event}
      (actual : kernel.interference before middle)
      (tail : ActorPhysicalPrefix runtime actor program middle events after) :
      ActorPhysicalPrefix runtime actor program before events after
  | returned {β : Type} {effect : Effect β} {next : β → Program α} {reply : β}
      {before middle after : World} {events : List Program.Event}
      (actual : ActorOperation runtime actor effect (some reply) before middle)
      (tail : ActorPhysicalPrefix runtime actor (next reply) middle events after) :
      ActorPhysicalPrefix runtime actor (.call effect next) before (.returned effect reply :: events) after
  | lost {β : Type} {effect : Effect β} {next : β → Program α} {before after : World}
      (actual : ActorOperation runtime actor effect none before after) :
      ActorPhysicalPrefix runtime actor (.call effect next) before [.lost effect] after

theorem actor_borrow_physical_prefix {kernel : Contract} {runtime : ActorRuntime kernel}
    {actor : ActorId} {fd : UInt64} {handle : Handle} {α : Type} {program : Program α} {post : α → Prop}
    (source : ActorBorrowPost runtime actor fd handle post program)
    {before after : World} {events : List Program.Event}
    (run : ActorPhysicalPrefix runtime actor program before events after)
    (live : before.handles fd = some handle) : after.handles fd = some handle := by
  induction run with
  | stop => exact live
  | environment actual tail ih =>
    apply ih source
    rw [kernel.interference_handles _ _ actual]
    exact live
  | returned actual tail ih =>
    cases source with
    | call preserve following => exact ih (following _ _ _ actual live) (preserve _ _ _ actual live)
  | lost actual => cases source with | call preserve following => exact preserve _ _ _ actual live

-- §FS-host-boundary.ownership: The postcondition and exact reference follow from actual returns.
theorem actor_borrow_returns {kernel : Contract} {runtime : ActorRuntime kernel}
    {actor : ActorId} {fd : UInt64} {handle : Handle} {α : Type} {program : Program α} {post : α → Prop}
    (source : ActorBorrowPost runtime actor fd handle post program)
    {before after : World} {events : List Program.Event} {value : α}
    (history : ActorReturnsHistory runtime actor before events after)
    (returned : Program.Returns program events value) (live : before.handles fd = some handle) :
    after.handles fd = some handle ∧ post value := by
  induction history generalizing program with
  | nil =>
    cases returned
    cases source with
    | pure property => exact ⟨live, property⟩
  | returned actual tail ih =>
    cases returned with
    | call effect next reply rest value continued =>
      cases source with
      | call preserve following => exact ih (following _ _ _ actual live) continued (preserve _ _ _ actual live)
  | environment actual tail ih =>
    apply ih source returned
    rw [kernel.interference_handles _ _ actual]
    exact live

def observedEvent {β : Type} (effect : Effect β) : Option β → Program.Event
  | some reply => .returned effect reply
  | none => .lost effect

-- §FS-host-boundary.acceptance: Reconstruct the exact pending call, including its lost effect.
theorem actor_prefix_from_history {kernel : Contract} {runtime : ActorRuntime kernel} {actor : ActorId}
    {α : Type} {program : Program α} {before middle after : World} {events : List Program.Event}
    {β : Type} {effect : Effect β} {observed : Option β}
    (history : ActorReturnsHistory runtime actor before events middle)
    (actual : ActorOperation runtime actor effect observed middle after)
    (source : Program.Prefix program (events ++ [observedEvent effect observed])) :
    ActorPhysicalPrefix runtime actor program before (events ++ [observedEvent effect observed]) after := by
  induction history generalizing program with
  | nil =>
    cases observed with
    | none => cases source with | lost => exact .lost actual
    | some reply =>
      cases source with
      | returned => exact .returned actual (.stop _ _)
  | returned operation tail ih =>
    cases source with
    | returned effect next reply rest following => exact .returned operation (ih actual following)
  | environment interference tail ih => exact .environment interference (ih actual source)

end LeanCage.Host.Kernel
