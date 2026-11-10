import ArtifactsProofs.Files
import TransportProofs.Results

namespace LeanCage.Host.Artifacts

open Filesystem

private theorem pure_error_false {α : Type} (error : Failure) (value : α)
    (events : List (Request × Reply)) (run : Returns (.pure (.error error : Result α)) events (.ok value)) : False := by
  have same := (Snapshot.returns_pure_eq run).2
  cases same

-- §FS-host-boundary.artifacts: Extract actual manifest and content hash operations from one run.
theorem validateExport_execution (limits : Transport.Limits) (raw : ByteArray) (expectedDigest : String)
    (omitted : Nat) (sources : List Transport.Blob) (events : List (Request × Reply)) (output : Export)
    (run : Returns (validateExport limits raw expectedDigest omitted sources) events (.ok output)) :
    ∃ digest hashEvents blobEvents manifest blobs files,
      events = hashEvents ++ blobEvents ∧
      Returns (Filesystem.hash raw) hashEvents (.ok digest) ∧ digest.size = 32 ∧
      Snapshot.hex digest = expectedDigest ∧ parseManifest limits raw = .ok manifest ∧
      manifest.omitted = omitted ∧ Returns (checkBlobs limits sources {}) blobEvents (.ok blobs) ∧
      bindFiles blobs manifest.entries.toList {} = .ok files ∧ allReferenced blobs files = true ∧
      output = ⟨files.reversed.reverse, manifest.dirs, manifest.omittedPaths, raw, digest⟩ := by
  unfold validateExport at run
  split at run
  · exact False.elim (pure_error_false _ _ _ run)
  · obtain ⟨hashEvents, result, last, hashed, continued, eventShape⟩ :=
      Snapshot.returns_bind_split (Filesystem.hash raw) _ run
    cases result with
    | error error => exact False.elim (pure_error_false _ _ _ continued)
    | ok digest =>
      dsimp only at continued
      split at continued
      · exact False.elim (pure_error_false _ _ _ continued)
      · rename_i digestMatches
        cases parsed : parseManifest limits raw with
        | error error => simp only [parsed] at continued; exact False.elim (pure_error_false _ _ _ continued)
        | ok manifest =>
          simp only [parsed] at continued
          split at continued
          · exact False.elim (pure_error_false _ _ _ continued)
          · rename_i omissionMatches
            obtain ⟨blobEvents, result, final, checked, continued, tailShape⟩ :=
              Snapshot.returns_bind_split (checkBlobs limits sources {}) _ continued
            cases result with
            | error error => exact False.elim (pure_error_false _ _ _ continued)
            | ok blobs =>
              dsimp only at continued
              cases bound : bindFiles blobs manifest.entries.toList {} with
              | error error => simp only [bound] at continued; exact False.elim (pure_error_false _ _ _ continued)
              | ok files =>
                simp only [bound] at continued
                split at continued
                · exact False.elim (pure_error_false _ _ _ continued)
                · rename_i referenced
                  obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq continued
                  have digests : digest.size = 32 ∧ Snapshot.hex digest = expectedDigest := by simpa using digestMatches
                  refine ⟨digest, hashEvents, blobEvents, manifest, blobs, files, ?_, hashed, digests.1,
                    digests.2, rfl, ?_, checked, bound, ?_, Except.ok.inj same⟩
                  · simpa only [List.append_nil] using eventShape.trans (congrArg (hashEvents ++ ·) tailShape)
                  · simpa using omissionMatches
                  · simpa using referenced

-- §FS-host-boundary.artifacts: Successful assembly retains the exact same report and captures.
theorem validate_execution (expected : Expected) (received : Transport.Result)
    (events : List (Request × Reply)) (output : Validated)
    (run : Returns (validate expected received) events (.ok output)) :
    ∃ value report, checkReport expected received = .ok (value, report) ∧
      ((report.exportState ≠ "complete" ∧ events = [] ∧ output = assemble received value report none) ∨
        ∃ raw digest exported, report.exportState = "complete" ∧ received.manifest = some raw ∧
          report.exportDigest = some digest ∧
          Returns (validateExport expected.limits raw digest report.exportOmitted received.blobs) events (.ok exported) ∧
          output = assemble received value report (some exported)) := by
  unfold validate at run
  cases checked : checkReport expected received with
  | error error => simp only [checked] at run; exact False.elim (pure_error_false _ _ _ run)
  | ok pair =>
    rcases pair with ⟨value, report⟩
    simp only [checked] at run
    split at run
    · rename_i committed
      cases manifest : received.manifest <;> cases identity : report.exportDigest <;>
        simp only [manifest, identity] at run
      all_goals try exact False.elim (pure_error_false _ _ _ run)
      rename_i raw digest
      obtain ⟨before, result, last, exported, continued, eventShape⟩ :=
        Snapshot.returns_bind_split (validateExport expected.limits raw digest report.exportOmitted received.blobs) _ run
      have pureResult := Snapshot.returns_pure_eq continued
      rcases pureResult with ⟨rfl, answer⟩
      cases result with
      | error error => cases answer
      | ok actual =>
        simp only [Except.map] at answer
        refine ⟨value, report, rfl, Or.inr ⟨raw, digest, actual, committed, rfl, identity, ?_, Except.ok.inj answer⟩⟩
        simp only [List.append_nil] at eventShape
        rw [eventShape]
        exact exported
    · rename_i uncommitted
      obtain ⟨empty, same⟩ := Snapshot.returns_pure_eq run
      exact ⟨value, report, rfl, Or.inl ⟨uncommitted, empty, Except.ok.inj same⟩⟩

structure ExportValid (limits : Transport.Limits) (raw : ByteArray) (expectedDigest : String)
    (sources : List Transport.Blob) (events : List (Request × Reply)) (output : Export) : Prop where
  manifest : output.manifest = raw
  manifestHash : HashSeen events raw output.digest
  manifestIdentity : Snapshot.hex output.digest = expectedDigest
  manifestBound : raw.size ≤ manifestMax
  bytes : fileBytes output.files ≤ limits.workspaceMax
  count : output.files.length ≤ limits.inodesMax
  uniqueFiles : (output.files.map (fun file => file.path.text)).Nodup
  parents : ∀ file ∈ output.files, ∀ parent ∈ file.path.parents,
    ∃ directory ∈ output.dirs, directory.text = parent
  fileSources : ∀ file ∈ output.files, ∃ source ∈ sources,
    file.bytes = source.content ∧ (Snapshot.hex file.digest).toUTF8 = source.digest ∧
      HashSeen events file.bytes file.digest
  referenced : ∀ source ∈ sources, ∃ file ∈ output.files,
    (Snapshot.hex file.digest).toUTF8 = source.digest
  inodeCount : output.files.length + output.dirs.length + output.omitted.length ≤ limits.inodesMax
  directoryParents : ∀ directory ∈ output.dirs, ∀ parent ∈ directory.parents,
    ∃ declared ∈ output.dirs, declared.text = parent
  omittedParents : ∀ omitted ∈ output.omitted, ∀ parent ∈ omitted.parents,
    ∃ directory ∈ output.dirs, directory.text = parent
  declarations : ∃ state, parseManifest limits raw = .ok state ∧ output.dirs = state.dirs ∧
    output.omitted = state.omittedPaths ∧ ∀ file ∈ output.files,
      Node.file file.path file.executable file.bytes.size (Snapshot.hex file.digest) ∈ state.entries.toList

-- §FS-host-boundary.artifacts: The program derives hierarchy, bounds and byte/hash provenance.
theorem validateExport_sound (limits : Transport.Limits) (raw : ByteArray) (expectedDigest : String)
    (omitted : Nat) (sources : List Transport.Blob) (events : List (Request × Reply)) (output : Export)
    (run : Returns (validateExport limits raw expectedDigest omitted sources) events (.ok output)) :
    ExportValid limits raw expectedDigest sources events output := by
  rcases validateExport_execution limits raw expectedDigest omitted sources events output run with
    ⟨digest, hashEvents, blobEvents, manifest, blobs, files, shape, hashed, _, identity, parsed, _, checked,
      bound, referenced, rfl⟩
  have manifestFacts := parseManifest_sound limits raw manifest parsed
  have invariant := manifestFacts.2.1
  have index := checkBlobs_index_sound limits sources {} blobs blobEvents blob_index_empty checked
  have fileOrigins : ∀ file ∈ files.reversed, ∃ node ∈ manifest.entries.toList, FileFromNode blobs node file := by
    intro file member
    rcases bindFiles_provenance blobs manifest.entries.toList {} files bound file member with old | fresh
    · simp at old
    · exact fresh
  refine ⟨rfl, ?_, identity, manifestFacts.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [shape]
    exact hashSeen_append_left _ _ _ _ (hash_returned _ _ _ hashed)
  · have measured := bindFiles_bytes blobs manifest.entries.toList {} files bound
    have reversed : fileBytes files.reversed.reverse = fileBytes files.reversed := by
      simp only [fileBytes, List.map_reverse, List.sum_reverse]
    change fileBytes files.reversed.reverse ≤ limits.workspaceMax
    rw [reversed, measured]
    simpa only [fileBytes, List.map_nil, List.sum_nil, Nat.add_zero, invariant.bytes] using invariant.total
  · have count := bindFiles_count blobs manifest.entries.toList {} files bound
    change files.reversed.reverse.length ≤ limits.inodesMax
    simp only [List.length_reverse]
    have length : manifest.entries.toList.length = manifest.entries.size := Array.length_toList
    have maximum := invariant.count
    change files.reversed.length ≤ manifest.entries.toList.length + 0 at count
    omega
  · have names := bindFiles_names blobs manifest.entries.toList {} files bound
    change (files.reversed.reverse.map (fun file => file.path.text)).Nodup
    rw [names]
    simpa only [List.reverse_nil, List.map_nil, List.nil_append] using
      fileNames_unique manifest.entries.toList invariant.unique
  · intro file member parent parentMember
    rcases fileOrigins file (List.mem_reverse.mp member) with ⟨node, nodeMember, origin⟩
    rcases origin with ⟨path, executable, size, key, blob, nodeShape, _, _, samePath, _, _, _, _⟩
    apply manifest_hierarchy limits manifest invariant manifestFacts.2.2 node nodeMember parent
    rw [nodeShape]
    simpa only [Node.path, samePath] using parentMember
  · intro file member
    rcases fileOrigins file (List.mem_reverse.mp member) with ⟨node, _, origin⟩
    rcases origin with ⟨_, _, _, key, blob, _, lookup, _, _, _, sameBytes, sameDigest, _⟩
    have blobMember := (index key blob lookup).1
    rcases checkBlobs_provenance limits sources {} blobs blobEvents checked blob blobMember with old | fresh
    · simp at old
    · rcases fresh with ⟨source, sourceMember, sameSource, seen⟩
      refine ⟨source, sourceMember, ?_, ?_, ?_⟩
      · rw [sameBytes, CheckedBlob.bytes, sameSource]
      · rw [sameDigest]
        exact blob.encoding.trans (congrArg Transport.Blob.digest sameSource)
      · rw [sameBytes, CheckedBlob.bytes, sameSource, sameDigest, shape]
        exact hashSeen_append_right _ _ _ _ seen
  · intro source sourceMember
    obtain ⟨added, values, origins, _⟩ := checkBlobs_sequence limits sources {} blobs blobEvents checked
    change blobs.values.toList = [] ++ added at values
    simp only [List.nil_append] at values
    rw [← origins] at sourceMember
    rcases List.mem_map.mp sourceMember with ⟨selected, selectedMember, sameSource⟩
    have actualMember : selected ∈ blobs.values.toList := by rw [values]; exact selectedMember
    have used : files.required.contains selected.key = true := List.all_eq_true.mp referenced selected actualMember
    have keyMember : selected.key ∈ files.required := Std.TreeSet.mem_iff_contains.mpr used
    rcases bindFiles_required blobs manifest.entries.toList {} files bound selected.key keyMember with old | fresh
    · simp at old
    · rcases fresh with ⟨path, executable, size, nodeMember⟩
      rcases bindFiles_complete blobs manifest.entries.toList {} files bound path executable size selected.key nodeMember with
        ⟨file, fileMember, origin⟩
      refine ⟨file, List.mem_reverse.mpr fileMember, ?_⟩
      rcases origin with ⟨_, _, _, key, blob, nodeShape, _, sameKey, _, _, _, sameDigest, _⟩
      have selectedKey : key = selected.key := (Node.file.inj nodeShape).2.2.2.symm
      rw [sameDigest]
      change blob.key.toUTF8 = source.digest
      rw [sameKey, selectedKey]
      exact selected.encoding.trans (congrArg Transport.Blob.digest sameSource)
  · have names := bindFiles_names blobs manifest.entries.toList {} files bound
    have fileCount : files.reversed.reverse.length = (fileNames manifest.entries.toList).length := by
      simpa only [List.length_map, List.length_append, List.reverse_nil, List.map_nil, List.length_nil,
        Nat.zero_add] using congrArg List.length names
    have partition := node_partition_count manifest.entries.toList
    change (fileNames manifest.entries.toList).length + manifest.dirs.length + manifest.omittedPaths.length =
      manifest.entries.toList.length at partition
    have maximum := invariant.count
    have length : manifest.entries.toList.length = manifest.entries.size := Array.length_toList
    change files.reversed.reverse.length + manifest.dirs.length + manifest.omittedPaths.length ≤ limits.inodesMax
    omega
  · intro directory member parent parentMember
    exact manifest_hierarchy limits manifest invariant manifestFacts.2.2 (.directory directory)
      (manifest_directory_member manifest directory member) parent parentMember
  · intro omitted member parent parentMember
    exact manifest_hierarchy limits manifest invariant manifestFacts.2.2 (.omitted omitted)
      (manifest_omitted_member manifest omitted member) parent parentMember
  · refine ⟨manifest, parsed, rfl, rfl, ?_⟩
    intro file member
    rcases fileOrigins file (List.mem_reverse.mp member) with ⟨node, nodeMember, origin⟩
    rcases origin with ⟨path, executable, size, key, blob, nodeShape, _, sameKey,
      samePath, sameExecutable, _, sameDigest, sameSize⟩
    rw [samePath, sameExecutable, sameSize, sameDigest]
    change Node.file path executable size blob.key ∈ manifest.entries.toList
    rw [sameKey, ← nodeShape]
    exact nodeMember

theorem validateExport_omitted (limits : Transport.Limits) (raw : ByteArray) (expectedDigest : String)
    (omitted : Nat) (sources : List Transport.Blob) (events : List (Request × Reply)) (output : Export)
    (run : Returns (validateExport limits raw expectedDigest omitted sources) events (.ok output)) :
    output.omitted.length = omitted := by
  rcases validateExport_execution limits raw expectedDigest omitted sources events output run with
    ⟨_, _, _, manifest, _, _, _, _, _, _, parsed, omissions, _, _, _, rfl⟩
  have invariant := (parseManifest_sound limits raw manifest parsed).2.1
  exact (node_omitted_count manifest.entries.toList).trans (invariant.omitted.trans omissions)

structure ArtifactsValid (expected : Expected) (received : Transport.Result)
    (events : List (Request × Reply)) (output : Validated) : Prop where
  rawReport : output.rawReport = received.report
  report : ReportValid expected received output.report output.details
  stored : output.stored = received.stored
  stdout : output.stdout = received.stdout.getD .empty
  stderr : output.stderr = received.stderr.getD .empty
  exported :
    (output.files = [] ∧ output.dirs = [] ∧ output.omitted = [] ∧ output.manifest = none ∧
      output.manifestDigest = none ∧ received.manifest = none ∧ received.blobs = []) ∨
    ∃ exported : Export, output.files = exported.files ∧ output.dirs = exported.dirs ∧
      output.omitted = exported.omitted ∧ output.manifest = some exported.manifest ∧
      output.manifestDigest = some exported.digest ∧ received.manifest = some exported.manifest ∧
      output.details.exportState = "complete" ∧
      output.details.exportDigest = some (Snapshot.hex exported.digest) ∧
      ExportValid expected.limits exported.manifest (Snapshot.hex exported.digest) received.blobs events exported

theorem uncommitted_absent (expected : Expected) (received : Transport.Result) (report : Report)
    (control : ControlValid expected received report) (uncommitted : report.exportState ≠ "complete") :
    received.manifest = none ∧ received.blobs = [] := by
  cases preflight : expected.preflight with
  | true =>
    rcases noArtifacts_fields received (control.unallocated (Or.inl preflight)).1 with ⟨_, _, _, manifest, blobs⟩
    exact ⟨manifest, blobs⟩
  | false =>
    by_cases unallocated : report.runId = 0
    · rcases noArtifacts_fields received (control.unallocated (Or.inr unallocated)).1 with ⟨_, _, _, manifest, blobs⟩
      exact ⟨manifest, blobs⟩
    · exact control.uncommitted preflight unallocated uncommitted

-- §FS-host-boundary.artifacts: Complete results use checked data; failures expose no partial plan.
theorem validate_sound (expected : Expected) (received : Transport.Result)
    (events : List (Request × Reply)) (output : Validated)
    (run : Returns (validate expected received) events (.ok output)) : ArtifactsValid expected received events output := by
  rcases validate_execution expected received events output run with ⟨value, report, checked, cases⟩
  have reportValid := checkReport_sound expected received value report checked
  rcases cases with ⟨uncommitted, _, rfl⟩ | ⟨raw, digest, exported, committed, manifest, identity, call, rfl⟩
  · have absent := uncommitted_absent expected received report reportValid.control uncommitted
    exact ⟨rfl, reportValid, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, absent⟩⟩
  · have verified := validateExport_sound expected.limits raw digest report.exportOmitted received.blobs events exported call
    refine ⟨rfl, reportValid, rfl, rfl, rfl, Or.inr ⟨exported, rfl, rfl, rfl, rfl, rfl, ?_, committed, ?_, ?_⟩⟩
    · simpa only [verified.manifest] using manifest
    · simpa only [assemble, verified.manifestIdentity] using identity
    · simpa only [verified.manifest, verified.manifestIdentity] using verified

-- §FS-host-boundary.acceptance: Framing is produced by the actual decoder, never an implicit cast.
theorem actual_transport_artifacts (request bundle : ByteArray) (expected : Expected)
    (initial : Transport.State) (initialized : Transport.State.init request bundle expected.limits = .ok initial)
    (stream : List Transport.Event) (received : Transport.Result)
    (finished : (initial.run stream).finish = .ok received)
    (events : List (Request × Reply)) (output : Validated)
    (run : Returns (validate expected received) events (.ok output)) :
    ArtifactsValid expected received events output ∧
      Transport.eventsWire stream = (Transport.identityPrefix request bundle).data.toList ++
        Transport.frameWire received.frames ∧ Transport.Event.eof ∈ stream :=
  ⟨validate_sound expected received events output run,
    (Transport.accepted_stream request bundle expected.limits initial initialized stream received finished).1,
    Transport.accepted_has_eof request bundle expected.limits initial initialized stream received finished⟩

-- §AR-host-boundary.interfaces: Only the actual successful SHA primitive replies supply hash truth.
def HashReplyContract (meaning : ByteArray → ByteArray → Prop) (events : List (Request × Reply)) : Prop :=
  ∀ request reply, (request, reply) ∈ events → request.op = .sha256 → reply.1 = 0 →
    reply.2.size = 32 → meaning request.left reply.2

theorem hashSeen_meaning (meaning : ByteArray → ByteArray → Prop) (events : List (Request × Reply))
    (law : HashReplyContract meaning events) (bytes digest : ByteArray) (seen : HashSeen events bytes digest) :
    meaning bytes digest := by
  rcases seen with ⟨reply, member, zero, payload, size⟩
  have replySize : reply.2.size = 32 := payload ▸ size
  simpa only [payload] using law _ reply member rfl zero replySize

end LeanCage.Host.Artifacts
