import GatewayResponseSourceBounds
import GatewayStreamCommitSources

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

private theorem ordinal_key_range (events : List (Request × Reply)) (actor : ActorId) (base : Nat)
    (records : List Record) :
    (List.range' base events.length).flatMap (fun ordinal => records.flatMap (Record.bytesFor (.engine actor ordinal))) =
      events.zipIdx.flatMap (fun item => records.flatMap (Record.bytesFor (.engine actor (base + item.2)))) := by
  have indexes : (events.zipIdx.map Prod.snd).map (base + ·) = List.range' base events.length := by
    rw [List.zipIdx_map_snd, List.map_add_range', Nat.add_zero]
  rw [← indexes, List.flatMap_map, List.flatMap_map]

-- §FS-host-boundary.caller: Select the last actual partial write and derive
-- its real response plus the complete ordered written prefix. No expected
-- response, future ACK, engine return or writer-success premise is accepted.
theorem actual_response_written_prefix
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (introductions : DescriptionIntroductionContract kernel) (retirement : DescriptorRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final)
    (actor : ActorId) (handle : Handle) (sources : ChannelWriteSources primitive actor handle.description)
    (tick : ActorTick runtime) (engine : EngineState)
    (history : SelectedActorHistory runtime initialWorld ticks tick actor engine)
    (inherited : history.launch.references 1 = some handle) (endpoint : handle.object = pair.engine)
    (nonempty : (records.flatMap Record.actions).flatMap (written .caller) ≠ []) :
    ∃ entry token, primitive.enteredEngine token entry ∧ entry.actor = actor ∧
      ∃ response : EngineResponse entry, ∃ current,
        final.ledger entry.key = some current ∧
        response.source.writer.offset + current.committed ≤ response.source.context.bytes.size ∧
        (records.flatMap Record.actions).flatMap (written .caller) =
          (response.source.context.bytes.extract 0 (response.source.writer.offset + current.committed)).data.toList := by
  classical
  have writer := actual_channel_writer_bytes sources physical.erase (registered_unborn primitive)
  let chunks := records.filterMap (Record.engineChunk actor)
  have chunkNonempty : chunks ≠ [] := by
    intro empty
    rw [writer] at nonempty
    change chunks.flatMap Prod.snd ≠ [] at nonempty
    rw [empty] at nonempty
    exact nonempty rfl
  cases lastFound : chunks.getLast? with
  | none => exact False.elim (chunkNonempty (List.getLast?_eq_none_iff.mp lastFound))
  | some last =>
    obtain ⟨leading, shape⟩ := List.getLast?_eq_some_iff.mp lastFound
    have member : last ∈ chunks := by rw [shape]; simp
    obtain ⟨record, recordMember, recordSelected⟩ := List.mem_filterMap.mp member
    obtain ⟨extent, commit, bytes⟩ := record.engine_chunk_source actor last recordSelected
    obtain ⟨entry, token, current, entered, key, stored⟩ := physical.erase.engine_commit_source
      (registered_unborn primitive) record recordMember actor last.1 extent commit
    have keyFields := CallKey.engine.inj key
    obtain ⟨response⟩ := source_channel_engine_response descriptors introductions retirement sdk lifetimes references environment
      source actor handle sources tick engine history inherited endpoint entry token entered
    have ordered : chunks.Pairwise (fun first last => first.1 ≤ last.1) := actual_engine_chunks_ordered source physical actor
    have maximal : ∀ item ∈ chunks, item.1 ≤ last.1 := by
      rw [shape] at ordered ⊢
      have together := (List.pairwise_append.mp ordered).2.2
      intro item member
      rcases List.mem_append.mp member with first | final
      · exact together item first last (by simp)
      · cases List.mem_singleton.mp final; exact Nat.le_refl _
    let base := entry.engine.events.length - response.source.writer.acknowledged.length
    have bounds : ∀ record ∈ records, ∀ ordinal extent,
        record.event = .commit (.engine actor ordinal) extent →
          base ≤ ordinal ∧ ordinal < base + (response.source.writer.acknowledged.length + 1) := by
      intro actual belongs ordinal extent event
      obtain ⟨earlier, earlierToken, progress, earlierEntered, earlierKey, progressAt⟩ :=
        physical.erase.engine_commit_source (registered_unborn primitive) actual belongs actor ordinal extent event
      obtain ⟨earlierResponse⟩ := source_channel_engine_response descriptors introductions retirement sdk lifetimes references environment
        source actor handle sources tick engine history inherited endpoint earlier earlierToken earlierEntered
      have earlierFields := CallKey.engine.inj earlierKey
      have sameActor : earlier.actor = entry.actor := earlierFields.1.trans keyFields.1.symm
      have lower := actual_response_base_unique source earlier entry sameActor earlierResponse response
      have present : (ordinal, actual.bytesFor (.engine actor ordinal)) ∈ chunks := by
        apply List.mem_filterMap.mpr
        exact ⟨actual, belongs, by simp [Record.engineChunk, event]⟩
      have upper := maximal _ present
      obtain ⟨raw, returned, responseShape⟩ := pending_response_raw response.pending response.source
      have length := congrArg List.length responseShape
      simp only [List.length_append, List.length_map] at length
      dsimp [base]
      rw [earlierFields.2] at lower
      omega
    have grouped := actual_engine_bytes_grouped source physical actor base
      (response.source.writer.acknowledged.length + 1) bounds
    have liveHistory : ∃ atEntry : SelectedActorHistory runtime initialWorld ticks entry.tick entry.actor entry.engine,
        atEntry.launch.references 1 = some handle := by
      have sameActor := keyFields.1
      subst actor
      obtain ⟨atEntry⟩ := actual_running_actor_history descriptors lifetimes references environment source
        entry.selected entry.present entry.running
      have sameLaunch := selected_launch_references_unique source atEntry history
      exact ⟨atEntry, by rw [sameLaunch]; exact inherited⟩
    obtain ⟨atEntry, inheritedAtEntry⟩ := liveHistory
    have earlier := actual_response_ack_grouped_prefix descriptors directories sdk lifetimes references environment
      source physical entry response atEntry handle inheritedAtEntry endpoint
    have previous : (List.range' base response.source.writer.acknowledged.length).flatMap
        (fun ordinal => records.flatMap (Record.bytesFor (.engine actor ordinal))) =
          (response.source.context.bytes.extract 0 response.source.writer.offset).data.toList := by
      rw [ordinal_key_range]
      simpa only [base, keyFields.1] using earlier
    have finalChunk := actual_response_final_chunk source physical entry response current stored
    obtain ⟨raw, returned, responseShape⟩ := pending_response_raw response.pending response.source
    have sourceLength := congrArg List.length responseShape
    simp only [List.length_append, List.length_map] at sourceLength
    have lastKey : base + response.source.writer.acknowledged.length = entry.engine.events.length := by dsimp [base]; omega
    have allWritten : (records.flatMap Record.actions).flatMap (written .caller) =
        (response.source.context.bytes.extract 0 (response.source.writer.offset + current.committed)).data.toList := by
      rw [writer, grouped, List.range'_concat, List.flatMap_append]
      simp only [Nat.one_mul, lastKey, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [previous]
      have currentBytes : records.flatMap (Record.bytesFor (.engine actor entry.engine.events.length)) =
          (response.source.context.bytes.extract response.source.writer.offset
            (response.source.writer.offset + current.committed)).data.toList := by
        simpa only [EngineWriteEntry.key, keyFields.1] using finalChunk.2
      rw [currentBytes]
      exact response_prefix_with_pending response.source.context.bytes finalChunk.1 _ _ rfl rfl
    exact ⟨entry, token, entered, keyFields.1, response, current, stored, finalChunk.1, allWritten⟩

end LeanCage.Host.PrivateStreams
