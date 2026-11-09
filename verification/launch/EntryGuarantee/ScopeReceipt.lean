import CallerPhysical

set_option autoImplicit false

namespace LeanCage.Entry

-- §AR-entry.caller.receipt: Keep actual source positions in the same physical history.
structure SourceScopeInputs (owner child : ProcessIdentity) (ticks : List CallerPhysical.Tick)
    (readOffset : Nat) (readTick : CallerPhysical.Tick) (group : Nat) where
  parentProgram : Nat
  closeOrdinal : Nat
  closeOffset : Nat
  closed : CallerPhysical.Tick
  closeAt : CallerPhysical.TickAt ticks closeOffset closed
  closeSource : closed.source = some ⟨parentProgram, closeOrdinal⟩
  assigned : closed.after.cgroup = some group
  optionsOffset : Nat
  owned : CallerPhysical.Tick
  optionsAt : CallerPhysical.TickAt ticks optionsOffset owned
  tracer : owned.before.tracer = some owner
  optionsBeforeClose : optionsOffset ≤ closeOffset
  resumeOrdinal : Nat
  resumeOffset : Nat
  resumed : CallerPhysical.Tick
  resumeAt : CallerPhysical.TickAt ticks resumeOffset resumed
  resumeSource : resumed.source = some ⟨parentProgram, resumeOrdinal⟩
  resumeAction : resumed.action = .request owner 7 0
  closeBeforeResume : closeOffset < resumeOffset
  sendOrdinal : Nat
  sendOffset : Nat
  sent : CallerPhysical.Tick
  sendAt : CallerPhysical.TickAt ticks sendOffset sent
  sendSource : sent.source = some ⟨parentProgram, sendOrdinal⟩
  resumeBeforeSend : resumeOffset < sendOffset
  sendBeforeRead : sendOffset < readOffset
  readAt : CallerPhysical.TickAt ticks readOffset readTick

-- §AR-entry.caller.receipt: Consume the actual release read and expose raw table facts.
def SourceScopeProducer (owner child : ProcessIdentity) (start limit : Nat)
    (ticks : List CallerPhysical.Tick) (group failure endpoint : Nat)
    (cgroupFiles : Nat → Option Nat) : Prop :=
  ∀ readOffset readTick flag,
    CallerPhysical.TickAt ticks readOffset readTick →
    readTick.socket = .read child failure 1 [165] →
    CallerPhysical.TickBinding readTick (CallerPhysical.taskKey child) failure endpoint flag →
    ∃ scope : SourceScopeInputs owner child ticks readOffset readTick group,
      (∀ offset tick, start + scope.closeOffset + 1 ≤ start + offset → start + offset < limit →
        CallerPhysical.TickAt ticks offset tick → CallerPhysical.PlacementRecording cgroupFiles tick) ∧
      (∀ offset tick, start + scope.closeOffset + 1 ≤ start + offset → start + offset < limit →
        CallerPhysical.TickAt ticks offset tick → ∀ reference, tick.source = some reference →
          CallerPhysical.WriteOutsideCgroup cgroupFiles tick) ∧
      (∀ offset tick, start + scope.closeOffset + 1 ≤ start + offset → start + offset < limit →
        CallerPhysical.TickAt ticks offset tick → ∀ actor, actor ≠ owner → actor ≠ child →
          CallerPhysical.CgroupAbsent cgroupFiles tick actor)

end LeanCage.Entry
