import FilesystemPublicTraversal

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.ownership: The public target parent is derived from the actual retained
-- root/CWD selection and every real descendant open, under the completed global prefix.
theorem parent_history_public {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (laws : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel) (lifetimes : LifetimeContract runtime)
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initialObjects dataObjects)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {leading trailing : List (ActorTick runtime)} {first family : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initialObjects dataObjects semantics
      (Population.empty initial) first leading tick.before family)
    (ordinal : Nat) (path : ByteArray) (create : Bool)
    {before after : World} {events : List (Request × Reply)} {parent : Directories.Parent}
    (run : RecordedRun kernel (fun index request reply =>
      SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply)
      ordinal (Directories.parent path create).lower before events after (.ok parent))
    (bound : ordinal + events.length ≤ engine.events.length) :
    ∃ handle, after.handles parent.directory.fd = some handle ∧ family handle.object = none := by
  have opens := actual_public_directory_opens laws aliases lifetimes lookup journal selected present shape count prefixLabels
  have source := run
  unfold Directories.parent at source
  obtain ⟨selecting, result, rest, selectedWorld, selectTrace, selectedRun, afterSelect⟩ :=
    recorded_run_bind_split _ _ source
  cases result with
  | error error => cases afterSelect.1
  | ok started =>
    have startBound : ordinal + selecting.length ≤ engine.events.length := by
      have length := congrArg List.length selectTrace
      simp only [List.length_append] at length
      omega
    obtain ⟨baseHandle, baseLive, basePublic, components⟩ := source_start_history_public laws lifetimes lookup cwdLookup
      journal selected present shape count prefixLabels.family path ordinal selectedRun startBound
    obtain ⟨base⟩ := source_start_guard_recorded laws _ ordinal path selectedRun
    have sameBase : base.handle = baseHandle := Option.some.inj (base.live.symm.trans baseLive)
    have publicBase : family base.handle.object = none := by rw [sameBase]; exact basePublic
    have baseRaw : base.handle.rawOwned = true := by
      apply laws.after_raw _ _ _ _ base.guard.actual started.base base.handle
      rw [(kernel.attribute_frame _ _ _ _ base.guard.actual rfl).1]
      exact base.guard.live
    have restSource := afterSelect.1
    dsimp only at restSource
    split at restSource
    · rename_i name named
      split at restSource
      · obtain ⟨logical, rejected⟩ := returns_source _ restSource
        have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
        cases impossible
      · obtain ⟨identity, later, identityTrace, afterIdentity⟩ := Snapshot.returns_call_split restSource
        have remaining := afterSelect.2
        rw [identityTrace] at remaining
        obtain ⟨identityBefore, identityAfter, initialHistory, operation, sampled, afterUid⟩ := recorded_history_head remaining
        have identityLive : identityBefore.handles started.base = some base.handle := by
          rw [empty_recorded_handles initialHistory]
          exact base.live
        have afterIdentityLive : identityAfter.handles started.base = some base.handle := by
          rw [laws.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
          exact identityLive
        change Returns (if nativeError identity || !identity.2.isEmpty || identity.1.toNat > 2 ^ 32 - 1 then
          closeResult started.base (.error (failure "host identity" identity))
        else do
          let base ← Directories.inspect identity.1.toNat started.base
          match base with
          | .error error => pure (.error error)
          | .ok base => do
            let result ← Directories.descend identity.1.toNat create base started.parts.dropLast
            pure (result.map (fun directory => (⟨directory, name, identity.1.toNat⟩ : Directories.Parent)))).lower
          later (.ok parent) at afterIdentity
        split at afterIdentity
        · obtain ⟨logical, rejected⟩ := returns_source _ afterIdentity
          have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
          cases impossible
        · have afterIdentityRun : RecordedRun kernel _ (ordinal + selecting.length + 1) _
              identityAfter later after (.ok parent : Result Directories.Parent) := ⟨afterIdentity, afterUid⟩
          obtain ⟨inspecting, result, remainingEvents, inspectedWorld, inspectTrace, inspected, afterInspect⟩ :=
            recorded_run_bind_split _ _ afterIdentityRun
          cases result with
          | error error => cases afterInspect.1
          | ok inspectedDirectory =>
            obtain ⟨inspectedObservation⟩ := Kernel.directory_inspect_recorded laws _
              (ordinal + selecting.length + 1) identity.1.toNat started.base base.handle
              ⟨directory_inspect_identity _ _ ▸ inspected.1, inspected.2⟩ afterIdentityLive baseRaw
            have sameHandle : inspectedObservation.handle = base.handle := by
              obtain ⟨sameFd, reply, inspectionTrace, parsed, trusted⟩ := Retrieval.directoryInspection_source _ _
                (directory_inspect_identity _ _ ▸ inspected.1)
              have handles := recorded_retaining_handles laws inspected.2 (by
                intro event member
                have same : event = ({op := .stat, first := started.base}, reply) := by
                  simpa only [inspectionTrace, List.mem_singleton] using member
                rw [same]
                simp [RetainsDescriptors])
              have live : inspectedWorld.handles inspectedDirectory.fd = some base.handle := by
                rw [sameFd, handles]
                exact afterIdentityLive
              exact Option.some.inj (inspectedObservation.live.symm.trans live)
            obtain ⟨descending, result, last, descendedWorld, descendTrace, descended, finish⟩ :=
              recorded_run_bind_split _ _ afterInspect
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq finish.1
            cases result with
            | error error => cases same
            | ok directory =>
              cases same
              have descendBound : ordinal + selecting.length + 1 + inspecting.length + descending.length ≤
                  engine.events.length := by
                have length := congrArg List.length selectTrace
                simp only [identityTrace, inspectTrace, descendTrace, List.length_append, List.length_cons,
                  List.length_nil] at length
                omega
              have recorded := recorded_history_source_bound descended.2 engine.events.length descendBound
              have names : ∀ component ∈ started.parts.dropLast,
                  Directories.component component = true ∧ PrivateNames.reservedBytes component = false := by
                intro component member
                exact source_components_are_components path started.parts components component
                  (List.dropLast_subset started.parts member)
              obtain ⟨handle, live, publicObject⟩ := directory_descend_public laws opens
                (ordinal + selecting.length + 1 + inspecting.length) identity.1.toNat create inspectedDirectory
                started.parts.dropLast inspectedObservation.handle ⟨descended.1, recorded⟩ inspectedObservation.live
                (by simpa only [sameHandle] using publicBase) names
              exact ⟨handle, by rw [empty_recorded_handles finish.2]; exact live, publicObject⟩
    · obtain ⟨logical, rejected⟩ := returns_source _ restSource
      have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
      cases impossible

end LeanCage.Host.Kernel.Lowered
