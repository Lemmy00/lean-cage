import FilesystemPrimitiveSources
import FilesystemExecFlags
import FilesystemAuthoritySources

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Extra guard probes and rejection closes cannot mutate namespace.
theorem primitive_mutation_primary {before : List Program.Event} {request : Request}
    {observed : Option Reply}
    (occurrence : PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run before request observed)
    (mutating : ¬ NamespacePassive request) : request = occurrence.primary := by
  apply PrimitiveFilesystem.filesystem_occurrence_primary occurrence
  all_goals
    intro extra
    apply mutating
    simp only [NamespacePassive, extra]

structure PrimitiveMutation (before : List Program.Event) (request : Request) (observed : Option Reply) where
  occurrence : PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run before request observed
  primary : request = occurrence.primary
  source : EntryMutation occurrence.logicalBefore (.lost (.filesystem request))

-- §FS-host-boundary.caller: The raw mutation's role comes from the actual packet/CLI source cut.
theorem primitive_mutation_origin {before : List Program.Event} {request : Request}
    {observed : Option Reply}
    (active : Program.Prefix (PrimitiveFilesystem.lower Entrypoint.run)
      (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (mutating : ¬ NamespacePassive request) : Nonempty (PrimitiveMutation before request observed) := by
  obtain ⟨occurrence⟩ := PrimitiveFilesystem.lowered_filesystem_source Entrypoint.run active
  have same := primitive_mutation_primary occurrence mutating
  have logical : Program.Prefix Entrypoint.run (occurrence.logicalBefore ++ [.lost (.filesystem request)]) := by
    simpa only [← same] using PrimitiveFilesystem.filesystem_occurrence_logical occurrence
  obtain ⟨source⟩ := entrypoint_mutation_origin (observed := none) logical mutating
  exact ⟨⟨occurrence, same, source⟩⟩

theorem primitive_closed_open {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (PrimitiveFilesystem.lower Entrypoint.run)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : ClosedOpenRequest request := by
  intro opening
  obtain ⟨occurrence⟩ := PrimitiveFilesystem.lowered_filesystem_source Entrypoint.run active
  have same := PrimitiveFilesystem.filesystem_occurrence_primary occurrence
    (by intro other; rw [opening] at other; cases other)
    (by intro other; rw [opening] at other; cases other)
    (by intro other; rw [opening] at other; cases other)
  have logical : Program.Prefix Entrypoint.run (occurrence.logicalBefore ++ [.lost (.filesystem request)]) := by
    simpa only [← same] using PrimitiveFilesystem.filesystem_occurrence_logical occurrence
  exact entrypoint_closed_open (observed := none) logical opening

theorem primitive_authority_safe {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (PrimitiveFilesystem.lower Entrypoint.run)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : AuthoritySafeRequest request := by
  intro setting
  obtain ⟨occurrence⟩ := PrimitiveFilesystem.lowered_filesystem_source Entrypoint.run active
  have same := PrimitiveFilesystem.filesystem_occurrence_primary occurrence
    (by intro other; rw [setting] at other; cases other)
    (by intro other; rw [setting] at other; cases other)
    (by intro other; rw [setting] at other; cases other)
  have logical : Program.Prefix Entrypoint.run (occurrence.logicalBefore ++ [.lost (.filesystem request)]) := by
    simpa only [← same] using PrimitiveFilesystem.filesystem_occurrence_logical occurrence
  exact entrypoint_authority_safe (observed := none) logical setting

theorem selected_primitive_mutation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (mutating : ¬ NamespacePassive request) :
    Nonempty (PrimitiveMutation engine.events request observed) :=
  primitive_mutation_origin (selected_source_prefix_for journal selected action present) mutating

end LeanCage.Host.Kernel
