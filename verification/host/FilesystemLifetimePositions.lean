import FilesystemIntervals

namespace LeanCage.Host.Kernel

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: A live reference to an allocated lifetime occurs
-- strictly after its actual fresh birth. This orders real journal positions without
-- finite inode-number injectivity or a guessed source-operation order.
theorem journal_birth_before_allocated {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {start finish : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime start ticks finish) {first last : Nat} {birth current : ActorTick runtime}
    (birthAt : ticks[first]? = some birth) (currentAt : ticks[last]? = some current) {object : ObjectId}
    (fresh : birth.before.shared.allocated object = false) (allocated : current.before.shared.allocated object = true) :
    first < last := by
  apply Classical.byContradiction
  intro unordered
  have ordered : last ≤ first := Nat.le_of_not_gt unordered
  obtain ⟨leading, inside, trailing, trace, interval⟩ := journal_between_selected journal currentAt birthAt ordered
  have impossible := actor_journal_allocated lifetimes interval object allocated
  rw [fresh] at impossible
  cases impossible

end LeanCage.Host.Kernel
