import TransportProofs.Framing

namespace LeanCage.Host.Transport

theorem finish_shape (state : State) (result : Result) (accepted : state.finish = .ok result) :
    state.phase = .done ∧ state.terminal = some result.terminal ∧
    state.report? = some result.report ∧ result.frames = state.framesRev.reverse ∧
    result.stored = Result.record? result.frames .stored ∧
    result.stdout = Result.record? result.frames .stdout ∧
    result.stderr = Result.record? result.frames .stderr ∧
    result.manifest = Result.record? result.frames .export ∧
    result.blobs = result.frames.filterMap (fun frame => if frame.header.tag = .blob then
      some ⟨frame.blobKey, frame.blobContent⟩ else none) := by
  unfold State.finish at accepted
  cases error : state.error with
  | some failure => simp [error] at accepted
  | none =>
    rw [error] at accepted
    dsimp only at accepted
    split at accepted
    · cases phase : state.phase <;> cases terminal : state.terminal <;>
        simp only [phase, terminal] at accepted
      all_goals try contradiction
      rename_i value
      cases report : state.report? with
      | none => simp [report] at accepted
      | some bytes =>
        simp only [report, Except.ok.injEq] at accepted
        cases accepted
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · contradiction

private theorem weighted_reverse (weight : Frame → Nat) (frames : List Frame) :
    frames.reverse.foldr (fun frame total => weight frame + total) 0 =
      frames.foldr (fun frame total => weight frame + total) 0 := by
  have first : frames.reverse.foldr (fun frame total => weight frame + total) 0 =
      (frames.reverse.map weight).sum := by simp only [List.sum_eq_foldr, List.foldr_map]
  have second : frames.foldr (fun frame total => weight frame + total) 0 = (frames.map weight).sum := by
    simp only [List.sum_eq_foldr, List.foldr_map]
  rw [first, second, List.map_reverse, List.sum_reverse]

-- §FS-host-boundary.transport: Accepted output is exactly the received wire, not a guessed prefix.
theorem accepted_stream (request bundle : ByteArray) (limits : Limits) (initial : State)
    (initialized : State.init request bundle limits = .ok initial) (events : List Event) (result : Result)
    (accepted : (initial.run events).finish = .ok result) :
    eventsWire events = (identityPrefix request bundle).data.toList ++ frameWire result.frames ∧
    (∀ frame ∈ result.frames, frame.Valid limits) ∧
    frameCost result.frames ≤ retainedBudget limits ∧
    result.frames.length ≤ 6 + limits.inodesMax ∧
    blobBytesOf result.frames ≤ limits.workspaceMax ∧
    ∃ earlier final, result.frames = earlier ++ [final] ∧ final.header.tag = .terminal ∧
      Terminal.parse final.payload = .ok result.terminal := by
  have initialBound := bounded_init request bundle limits initial initialized
  have bound := bounded_run initial initialBound events
  have config := run_config initial events
  rcases init_fields request bundle limits initial initialized with ⟨_, _, _, _, _, rfl⟩
  have configLimits := congrArg Prod.fst config
  have configIdentity := congrArg Prod.snd config
  dsimp only at configLimits configIdentity
  let start : State := { limits, expectedPrefix := identityPrefix request bundle, phase := .prefix 0 }
  have framed := framed_run start (show start.Framed from ⟨rfl, rfl⟩) events
  have shape := finish_shape _ result accepted
  have wire := run_wire start (show start.Framed from ⟨rfl, rfl⟩) events (finish_clean _ _ accepted)
  change (start.run events).wire = [] ++ eventsWire events at wire
  simp only [List.nil_append] at wire
  have completeWire : (start.run events).wire =
      (identityPrefix request bundle).data.toList ++ frameWire result.frames := by
    rw [State.wire, shape.1, shape.2.2.2.1, configIdentity]
  have storage := bounded_storage _ bound
  refine ⟨wire.symm.trans completeWire, ?_, ?_, ?_, ?_, ?_⟩
  · intro frame member
    rw [shape.2.2.2.1] at member
    have valid := bound.frameValid frame (List.mem_reverse.mp member)
    simpa only [configLimits] using valid
  · rw [shape.2.2.2.1]
    have reverse := weighted_reverse (fun frame => frame.header.raw.size + frame.payload.size)
      (start.run events).framesRev
    change _ ≤ _
    rw [frameCost, reverse]
    simpa only [frameCost, configLimits] using storage.1
  · rw [shape.2.2.2.1, List.length_reverse]
    simpa only [configLimits] using storage.2.1
  · rw [shape.2.2.2.1]
    have reverse := weighted_reverse (fun frame => if frame.header.tag = .blob then frame.payload.size - 64 else 0)
      (start.run events).framesRev
    rw [blobBytesOf, reverse]
    simpa only [blobBytesOf, configLimits] using storage.2.2.1
  · have done : (start.run events).phase = .done := shape.1
    simp only [State.Framed, done] at framed
    rcases framed with ⟨final, earlier, terminal, frames, tag, parsed, ended⟩
    have equal : terminal = result.terminal := Option.some.inj (ended.symm.trans shape.2.1)
    subst terminal
    refine ⟨earlier.reverse, final, ?_, tag, parsed⟩
    rw [shape.2.2.2.1, frames, List.reverse_cons]

private theorem byteArray_eq_of_list (first second : ByteArray)
    (equal : first.data.toList = second.data.toList) : first = second := by
  exact ByteArray.ext (Array.toList_inj.mp equal)

-- §FS-host-boundary.transport: The fixed-width headers give a unique complete frame partition.
theorem frameWire_injective (limits : Limits) (first second : List Frame)
    (firstValid : ∀ frame ∈ first, frame.Valid limits)
    (secondValid : ∀ frame ∈ second, frame.Valid limits)
    (equal : frameWire first = frameWire second) : first = second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons frame frames =>
      have rawSize := (header_parse_fields _ _ _ (secondValid frame (by simp)).1).1
      have sizes := congrArg List.length equal
      simp only [frameWire, List.flatMap_nil, List.flatMap_cons, List.length_append,
        Array.length_toList, ByteArray.size_data, rawSize, List.length_nil] at sizes
      omega
  | cons frame frames ih =>
    cases second with
    | nil =>
      have rawSize := (header_parse_fields _ _ _ (firstValid frame (by simp)).1).1
      have sizes := congrArg List.length equal
      simp only [frameWire, List.flatMap_nil, List.flatMap_cons, List.length_append,
        Array.length_toList, ByteArray.size_data, rawSize, List.length_nil] at sizes
      omega
    | cons other others =>
      have firstHeader := (firstValid frame (by simp)).1
      have secondHeader := (secondValid other (by simp)).1
      have firstSize := (header_parse_fields _ _ _ firstHeader).1
      have secondSize := (header_parse_fields _ _ _ secondHeader).1
      have rawLengths : frame.header.raw.data.toList.length = other.header.raw.data.toList.length := by
        simp only [Array.length_toList, ByteArray.size_data, firstSize, secondSize]
      simp only [frameWire, List.flatMap_cons, List.append_assoc] at equal
      change frame.header.raw.data.toList ++ (frame.payload.data.toList ++ frameWire frames) =
        other.header.raw.data.toList ++ (other.payload.data.toList ++ frameWire others) at equal
      have rawList := List.append_inj_left equal rawLengths
      have raw := byteArray_eq_of_list _ _ rawList
      rw [raw] at firstHeader
      have headerEqual : frame.header = other.header := Except.ok.inj (firstHeader.symm.trans secondHeader)
      have remaining := List.append_inj_right equal rawLengths
      have payloadLengths : frame.payload.data.toList.length = other.payload.data.toList.length := by
        simp only [Array.length_toList, ByteArray.size_data]
        rw [(firstValid frame (by simp)).2.1, (secondValid other (by simp)).2.1, headerEqual]
      have payloadList := List.append_inj_left remaining payloadLengths
      have payloadEqual := byteArray_eq_of_list _ _ payloadList
      have frameEqual : frame = other := by
        cases frame
        cases other
        cases headerEqual
        cases payloadEqual
        rfl
      have tails := List.append_inj_right remaining payloadLengths
      have rest : frames = others := ih others
        (fun item member => firstValid item (by simp [member]))
        (fun item member => secondValid item (by simp [member])) tails
      simp only [frameEqual, rest]

theorem record_member (frames : List Frame) (tag : Tag) (bytes : ByteArray)
    (found : Result.record? frames tag = some bytes) :
    ∃ frame ∈ frames, frame.header.tag = tag ∧ frame.payload = bytes := by
  rcases Option.map_eq_some_iff.mp found with ⟨frame, selected, payload⟩
  have test : (frame.header.tag == tag) = true := List.find?_some (p := fun item : Frame => item.header.tag == tag) selected
  exact ⟨frame, List.mem_of_find?_eq_some selected, (tag_beq _ _).mp test, payload⟩

theorem record_bounded (limits : Limits) (frames : List Frame)
    (valid : ∀ frame ∈ frames, frame.Valid limits) (tag : Tag) (bytes : ByteArray)
    (found : Result.record? frames tag = some bytes) : bytes.size ≤ tag.cap limits := by
  rcases record_member frames tag bytes found with ⟨frame, member, sameTag, rfl⟩
  have frameValid := valid frame member
  rw [frameValid.2.1]
  simpa only [sameTag] using (header_parse_fields _ _ _ frameValid.1).2.2.2.2.2

-- §FS-host-boundary.transport: A known controller report survives all subsequent loss/errors.
theorem known_report_byte (state : State) (bytes : ByteArray) (known : state.report? = some bytes)
    (byte : UInt8) : (state.byte byte).report? = some bytes := by
  change (fun frames (_ : Std.TreeSet Nat compare) =>
    (frames.find? (fun frame => frame.header.tag == .report)).map (·.payload) = some bytes)
      (state.byte byte).framesRev (state.byte byte).blobKeys
  refine ledger_byte (fun frames (_ : Std.TreeSet Nat compare) =>
    (frames.find? (fun frame => frame.header.tag == .report)).map (·.payload) = some bytes) state known ?_ byte
  intro header payload terminal _ admitted _ _
  have found : Result.record? state.framesRev .report = some bytes := known
  rcases record_member _ _ _ found with ⟨old, member, tag, _⟩
  have seen : state.seen .report = true := by
    apply List.any_eq_true.mpr
    exact ⟨old, member, (tag_beq _ _).mpr tag⟩
  have other : header.tag ≠ .report := by
    intro equal
    have accepted := (acceptHeader_fields state header admitted).2.2
      (by rw [equal]; decide)
    rw [equal, seen] at accepted
    exact Bool.noConfusion accepted.2
  have absent : (header.tag == .report) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    exact other ((tag_beq _ _).mp equal)
  simpa only [State.append, State.report?, List.find?_cons, absent] using known

theorem known_report_bytes (state : State) (bytes : ByteArray) (known : state.report? = some bytes)
    (input : List UInt8) : (state.bytes input).report? = some bytes := by
  induction input generalizing state with
  | nil => exact known
  | cons byte input ih => exact ih (state.byte byte) (known_report_byte state bytes known byte)

theorem known_report_step (state : State) (bytes : ByteArray) (known : state.report? = some bytes)
    (event : Event) : (state.step event).report? = some bytes := by
  unfold State.step
  split
  · exact known
  · cases event with
    | eof => exact known
    | data input =>
      dsimp only
      split
      · exact known
      · split
        · exact known
        · exact known_report_bytes state bytes known input.data.toList

theorem known_report_run (state : State) (bytes : ByteArray) (known : state.report? = some bytes)
    (events : List Event) : (state.run events).report? = some bytes := by
  induction events generalizing state with
  | nil => exact known
  | cons event events ih => exact ih (state.step event) (known_report_step state bytes known event)

theorem accepted_unique_records (request bundle : ByteArray) (limits : Limits) (initial : State)
    (initialized : State.init request bundle limits = .ok initial) (events : List Event) (result : Result)
    (accepted : (initial.run events).finish = .ok result) :
    result.frames.Pairwise (fun first second => first.header.tag ≠ .blob →
      first.header.tag ≠ second.header.tag) ∧
    result.frames.Pairwise (fun first second => first.header.tag = .blob →
      second.header.tag = .blob → first.blobKey ≠ second.blobKey) := by
  have shape := finish_shape _ result accepted
  have indexed : Indexed (initial.run events).framesRev (initial.run events).blobKeys := by
    apply indexed_run initial
    rcases init_fields request bundle limits initial initialized with ⟨_, _, _, _, _, rfl⟩
    exact indexed_empty
  rw [shape.2.2.2.1]
  constructor
  · apply List.pairwise_reverse.mpr
    apply indexed.uniqueNormal.imp
    intro first second different secondNormal equal
    by_cases firstBlob : first.header.tag = .blob
    · exact secondNormal (equal.trans firstBlob)
    · exact different firstBlob equal.symm
  · apply List.pairwise_reverse.mpr
    apply indexed.uniqueBlob.imp
    intro first second different secondBlob firstBlob equal
    exact different firstBlob secondBlob equal.symm

def blobOutput (frames : List Frame) : List Blob :=
  frames.filterMap (fun frame => if frame.header.tag = .blob then some ⟨frame.blobKey, frame.blobContent⟩ else none)

def blobOutputBytes (blobs : List Blob) : Nat := blobs.foldr (fun blob total => blob.content.size + total) 0

theorem blob_output_count (frames : List Frame) : (blobOutput frames).length = blobCountOf frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    by_cases blob : frame.header.tag = .blob
    · simp only [blobOutput, List.filterMap_cons, blob, ite_true, List.length_cons,
        blobCountOf, List.foldr_cons]
      change (blobOutput frames).length + 1 = 1 + blobCountOf frames
      rw [ih]
      omega
    · simp only [blobOutput, List.filterMap_cons, blob, ite_false, blobCountOf, List.foldr_cons]
      change (blobOutput frames).length = 0 + blobCountOf frames
      simpa only [Nat.zero_add] using ih

theorem blob_output_bytes (frames : List Frame) : blobOutputBytes (blobOutput frames) = blobBytesOf frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    by_cases blob : frame.header.tag = .blob
    · simp only [blobOutput, List.filterMap_cons, blob, ite_true, blobOutputBytes,
        List.foldr_cons, blobBytesOf]
      change frame.blobContent.size + blobOutputBytes (blobOutput frames) =
        (frame.payload.size - 64) + blobBytesOf frames
      simp only [Frame.blobContent, ByteArray.size_extract, Nat.min_self, ih]
    · simp only [blobOutput, List.filterMap_cons, blob, ite_false, blobBytesOf, List.foldr_cons]
      change blobOutputBytes (blobOutput frames) = 0 + blobBytesOf frames
      simpa only [Nat.zero_add] using ih

theorem accepted_blob_bounds (request bundle : ByteArray) (limits : Limits) (initial : State)
    (initialized : State.init request bundle limits = .ok initial) (events : List Event) (result : Result)
    (accepted : (initial.run events).finish = .ok result) :
    result.blobs.length ≤ limits.inodesMax ∧ blobOutputBytes result.blobs ≤ limits.workspaceMax ∧
    ∀ blob ∈ result.blobs, blob.digest.size = 64 ∧ lowerHex blob.digest = true := by
  have bound := bounded_run initial (bounded_init request bundle limits initial initialized) events
  have shape := finish_shape _ result accepted
  have output : result.blobs = blobOutput result.frames := shape.2.2.2.2.2.2.2.2
  have config := congrArg Prod.fst (run_config initial events)
  have initialLimits : initial.limits = limits := by
    rcases init_fields request bundle limits initial initialized with ⟨_, _, _, _, _, rfl⟩
    rfl
  have sameLimits : (initial.run events).limits = limits := config.trans initialLimits
  have frameFacts := (accepted_stream request bundle limits initial initialized events result accepted).2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [output, blob_output_count, shape.2.2.2.1]
    unfold blobCountOf
    rw [weighted_reverse]
    change blobCountOf (initial.run events).framesRev ≤ limits.inodesMax
    rw [bound.blobCount]
    simpa only [sameLimits] using bound.blobBound
  · rw [output, blob_output_bytes]
    exact (accepted_stream request bundle limits initial initialized events result accepted).2.2.2.2.1
  · intro blob member
    rw [output] at member
    rcases List.mem_filterMap.mp member with ⟨frame, frameMember, mapped⟩
    split at mapped
    · rename_i isBlob
      cases mapped
      exact (frameFacts frame frameMember).2.2 isBlob
    · contradiction

-- §FS-host-boundary.transport: Fixed-width digest keys have an injective index encoding.
theorem blob_key_injective (first second : ByteArray) (firstSize : first.size = 64)
    (secondSize : second.size = 64) (equal : fromLittleEndian first = fromLittleEndian second) : first = second := by
  have firstRound := littleEndian_fromLittleEndian first
  have secondRound := littleEndian_fromLittleEndian second
  rw [firstSize] at firstRound
  rw [secondSize] at secondRound
  exact firstRound.symm.trans ((congrArg (littleEndian 64) equal).trans secondRound)

def Phase.activeBytes : Phase → Nat
  | .prefix _ | .done | .failed => 0
  | .header bytes => bytes.size
  | .payload parsed bytes => parsed.raw.size + bytes.size

theorem bounded_active_bytes (state : State) (bound : state.Bounded) :
    state.phase.activeBytes ≤ 16 + activeBudget state.limits := by
  have active := bound.phase
  cases phase : state.phase <;> simp only [phase, Phase.Bounded] at active <;>
    simp only [Phase.activeBytes]
  all_goals omega

-- §FS-host-boundary.transport: The engine receives only raw records within the caller's caps.
theorem accepted_record_bounds (request bundle : ByteArray) (limits : Limits) (initial : State)
    (initialized : State.init request bundle limits = .ok initial) (events : List Event) (result : Result)
    (accepted : (initial.run events).finish = .ok result) :
    result.report.size ≤ reportMax ∧
    (∀ bytes, result.stored = some bytes → bytes.size ≤ reportMax) ∧
    (∀ bytes, result.stdout = some bytes → bytes.size ≤ limits.stdoutMax) ∧
    (∀ bytes, result.stderr = some bytes → bytes.size ≤ limits.stderrMax) ∧
    (∀ bytes, result.manifest = some bytes → bytes.size ≤ manifestMax) := by
  have bound := bounded_run initial (bounded_init request bundle limits initial initialized) events
  rcases finish_shape _ result accepted with ⟨_, _, report, _, stored, stdout, stderr, manifest, _⟩
  have config := congrArg Prod.fst (run_config initial events)
  have initialLimits : initial.limits = limits := by
    rcases init_fields request bundle limits initial initialized with ⟨_, _, _, _, _, rfl⟩
    rfl
  have sameLimits : (initial.run events).limits = limits := config.trans initialLimits
  have valid := (accepted_stream request bundle limits initial initialized events result accepted).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact record_bounded _ _ bound.frameValid .report result.report report
  · intro bytes found
    exact record_bounded _ _ valid .stored bytes (stored.symm.trans found)
  · intro bytes found
    exact record_bounded _ _ valid .stdout bytes (stdout.symm.trans found)
  · intro bytes found
    exact record_bounded _ _ valid .stderr bytes (stderr.symm.trans found)
  · intro bytes found
    exact record_bounded _ _ valid .export bytes (manifest.symm.trans found)

-- §FS-host-boundary.transport: Every finite hostile input prefix has bounded live decoder state.
theorem reachable_invariants (request bundle : ByteArray) (limits : Limits) (initial : State)
    (initialized : State.init request bundle limits = .ok initial) (events : List Event) :
    (initial.run events).Bounded ∧
    Indexed (initial.run events).framesRev (initial.run events).blobKeys ∧
    (initial.run events).Framed ∧ (initial.run events).limits = limits ∧
    (initial.run events).expectedPrefix = identityPrefix request bundle := by
  refine ⟨bounded_run initial (bounded_init request bundle limits initial initialized) events, ?_, ?_, ?_⟩
  · apply indexed_run
    rcases init_fields request bundle limits initial initialized with ⟨_, _, _, _, _, rfl⟩
    exact indexed_empty
  · apply framed_run
    rcases init_fields request bundle limits initial initialized with ⟨_, _, _, _, _, rfl⟩
    exact ⟨rfl, rfl⟩
  · have config := run_config initial events
    rcases init_fields request bundle limits initial initialized with ⟨_, _, _, _, _, rfl⟩
    exact Prod.mk.inj config

theorem data_eof_static (state : State) (bytes : ByteArray) :
    (state.step (.data bytes)).observedEof = state.observedEof := by
  unfold State.step
  split
  · rfl
  · dsimp only
    split
    · rfl
    · split
      · rfl
      · exact congrArg (fun value => value.2.2) (bytes_static state bytes.data.toList)

theorem step_eof_origin (state : State) (event : Event) (observed : (state.step event).observedEof = true) :
    state.observedEof = true ∨ event = .eof := by
  cases event with
  | eof => exact Or.inr rfl
  | data bytes => exact Or.inl ((data_eof_static state bytes).symm.trans observed)

theorem run_eof_origin (state : State) (events : List Event) (observed : (state.run events).observedEof = true) :
    state.observedEof = true ∨ .eof ∈ events := by
  induction events generalizing state with
  | nil => exact Or.inl observed
  | cons event events ih =>
    rcases ih (state.step event) observed with prior | later
    · rcases step_eof_origin state event prior with already | first
      · exact Or.inl already
      · exact Or.inr (List.mem_cons.mpr (Or.inl first.symm))
    · exact Or.inr (List.mem_cons_of_mem event later)

-- §FS-host-boundary.transport: EOF provenance comes from an actual input event.
theorem accepted_has_eof (request bundle : ByteArray) (limits : Limits) (initial : State)
    (initialized : State.init request bundle limits = .ok initial) (events : List Event) (result : Result)
    (accepted : (initial.run events).finish = .ok result) : .eof ∈ events := by
  rcases run_eof_origin initial events (finish_requires_eof _ result accepted) with initialEof | actualEof
  · rcases init_fields request bundle limits initial initialized with ⟨_, _, _, _, _, rfl⟩
    cases initialEof
  · exact actualEof

theorem terminal_parse_fields (bytes : ByteArray) (terminal : Terminal)
    (accepted : Terminal.parse bytes = .ok terminal) : bytes.size = 16 ∧
    terminal.controller = word bytes 0 4 ∧ terminal.retrieved = word bytes 4 4 ∧
    terminal.error = word bytes 8 4 ∧ terminal.extinct = word bytes 12 4 ∧
    terminal.controller ≤ 255 ∧ terminal.retrieved ≤ 255 ∧ terminal.error ≤ 4095 ∧ terminal.extinct ≤ 1 := by
  unfold Terminal.parse at accepted
  split at accepted
  · rename_i size
    dsimp only at accepted
    split at accepted
    · rename_i bounds
      cases accepted
      exact ⟨size, rfl, rfl, rfl, rfl, bounds⟩
    · contradiction
  · contradiction

theorem accepted_terminal_bounds (request bundle : ByteArray) (limits : Limits) (initial : State)
    (initialized : State.init request bundle limits = .ok initial) (events : List Event) (result : Result)
    (accepted : (initial.run events).finish = .ok result) :
    result.terminal.controller ≤ 255 ∧ result.terminal.retrieved ≤ 255 ∧
    result.terminal.error ≤ 4095 ∧ result.terminal.extinct ≤ 1 := by
  rcases (accepted_stream request bundle limits initial initialized events result accepted).2.2.2.2.2 with
    ⟨_, final, _, _, parsed⟩
  exact (terminal_parse_fields final.payload result.terminal parsed).2.2.2.2.2

def blobCopyBytes (blobs : List Blob) : Nat :=
  blobs.foldr (fun blob total => blob.digest.size + blob.content.size + total) 0

private theorem blob_copy_accounting (blobs : List Blob)
    (digests : ∀ blob ∈ blobs, blob.digest.size = 64) :
    blobCopyBytes blobs = 64 * blobs.length + blobOutputBytes blobs := by
  induction blobs with
  | nil => rfl
  | cons blob blobs ih =>
    have size := digests blob (by simp)
    have rest := ih (fun item member => digests item (by simp [member]))
    change blob.digest.size + blob.content.size + blobCopyBytes blobs =
      64 * (blobs.length + 1) + (blob.content.size + blobOutputBytes blobs)
    rw [size, rest, Nat.mul_add]
    omega

-- §FS-host-boundary.transport: The extra digest/content slices made by finish are also bounded.
theorem accepted_output_copies (request bundle : ByteArray) (limits : Limits) (initial : State)
    (initialized : State.init request bundle limits = .ok initial) (events : List Event) (result : Result)
    (accepted : (initial.run events).finish = .ok result) :
    blobCopyBytes result.blobs ≤ 64 * limits.inodesMax + limits.workspaceMax := by
  have bounds := accepted_blob_bounds request bundle limits initial initialized events result accepted
  rw [blob_copy_accounting result.blobs (fun blob member => (bounds.2.2 blob member).1)]
  exact Nat.add_le_add (Nat.mul_le_mul_left 64 bounds.1) bounds.2.1

theorem error_message_bounded (error : Error) : error.message.toUTF8.size ≤ 64 := by
  cases error <;> cbv

end LeanCage.Host.Transport
