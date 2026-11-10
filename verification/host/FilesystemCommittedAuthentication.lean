import FilesystemCryptography
import FilesystemPrimitivePhases
import FilesystemPrimitiveObservations
import FilesystemPublicationHandles
import FilesystemPrimitiveKeyDigest

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: A source commit retains both its actual MAC call and
-- its actual acknowledged marker operation before this raw rename, including reply loss.
structure PrimitiveCommitAuthentication {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (position : Nat) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply)
    (hmac : ByteArray → ByteArray → ByteArray) where
  adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed
  source : HostCommitCall adapter.occurrence.logicalBefore request none
  policyDigest : ByteArray
  key : ByteArray
  tag : ByteArray
  message : ByteArray
  exactMessage : message = Publication.markerWire source.source.effective source.source.commit.display
    source.source.stdoutHash source.source.stderrHash policyDigest source.source.commit.parent source.source.commit.stage
  keyEvents : List (Request × Reply)
  loaded : Retrieval.KeyObservation source.invocation.authenticated.bundle keyEvents key
  macReply : Reply
  mac : PrimitiveObservationAt runtime initial all tick actor engine
    (.filesystem {op := .authenticate, left := message, right := key}) macReply
  macPosition : Nat
  macTick : ActorTick runtime
  macSelected : all[macPosition]? = some macTick
  macAction : macTick.action = .returned actor (.filesystem {op := .authenticate, left := message, right := key}) macReply
  macEarlier : macPosition < position
  tagSize : tag.size = 32
  interpreted : tag = hmac key message
  markerReply : Reply
  marker : PrimitiveObservationAt runtime initial all tick actor engine
    (.filesystem {
      op := .setAttribute
      first := source.source.commit.stage.directory.fd
      left := Publication.attributeName
      right := Publication.marker tag }) markerReply
  markerPosition : Nat
  markerTick : ActorTick runtime
  markerSelected : all[markerPosition]? = some markerTick
  markerAction : markerTick.action = .returned actor
    (.filesystem {
      op := .setAttribute
      first := source.source.commit.stage.directory.fd
      left := Publication.attributeName
      right := Publication.marker tag }) markerReply
  markerEarlier : markerPosition < position
  markerAccepted : markerReply.1 = 0 ∧ markerReply.2 = .empty

-- §FS-host-boundary.publication: Source argument construction and ordering are derived
-- from the real publisher. The crypto premise interprets only its one actual raw MAC call.
theorem primitive_commit_authentication_with_key_digest {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (source : HostCommitCall adapter.occurrence.logicalBefore request none) :
    ∃ receipt : PrimitiveCommitAuthentication runtime initial all position tick actor engine request observed hmac,
      Nonempty (PrimitiveKeyDigestAt runtime initial all tick actor engine
        source.invocation.authenticated.bundle receipt.key sha256) ∧
      HEq receipt.source source ∧
      receipt.source.source.commit.stage = source.source.commit.stage ∧
      receipt.marker.rawAfter = adapter.occurrence.inside.map Program.filesystemPrefixEvent ∧
      ∃ markerInput markerOutput,
        receipt.markerTick.before.actors actor = some markerInput ∧
        receipt.markerTick.after.actors actor = some markerOutput ∧
        receipt.marker.before = receipt.markerTick.before.project markerInput ∧
        receipt.marker.after = receipt.markerTick.after.project markerOutput := by
  obtain ⟨candidate, policyDigest, json, tag, hashing, authenticating, filling, markerReply,
    prepareTrace, hashed, rendered, jsonBound, wireBound, authentication, filled, markerZero, markerEmpty⟩ :=
      Publication.prepare_source _ _ _ _ _ _ _ source.source.commit.prepared
  obtain ⟨bounded, key, keyEvents, macReply, authTrace, loaded, macZero, macPayload, tagSize⟩ := authentication
  let message := Publication.markerWire source.source.effective source.source.commit.display
    source.source.stdoutHash source.source.stderrHash policyDigest source.source.commit.parent source.source.commit.stage
  let markerRequest : Request := {
    op := .setAttribute
    first := source.source.commit.stage.directory.fd
    left := Publication.attributeName
    right := Publication.marker tag }
  let context := source.selectingContext ++ (source.source.commit.selecting ++ source.source.commit.creating ++
    hashing ++ keyEvents).map Program.filesystemEvent
  have macTrace : adapter.occurrence.logicalBefore = context ++
      .returned (.filesystem {op := .authenticate, left := message, right := key}) macReply ::
        (filling ++ [(markerRequest, markerReply)]).map Program.filesystemEvent := by
    have first := commit_parent_trace source
    have mapped := congrArg (fun events : List (Request × Reply) => source.selectingContext ++
      source.source.commit.selecting.map Program.filesystemEvent ++
      (source.source.commit.creating ++ events).map Program.filesystemEvent) prepareTrace
    have inner := congrArg (fun events : List (Request × Reply) => source.selectingContext ++
      source.source.commit.selecting.map Program.filesystemEvent ++
      (source.source.commit.creating ++ (hashing ++ events ++ filling ++ [(markerRequest, markerReply)])).map
        Program.filesystemEvent) authTrace
    exact first.trans (mapped.trans (inner.trans (by
      simp only [context, message, Publication.markerWire, markerRequest, List.map_append, List.map_cons, List.map_nil,
        Program.filesystemEvent, List.cons_append, List.nil_append, List.append_assoc])))
  obtain ⟨mac⟩ := primitive_observation adapter macTrace rfl
  have keyTrace : adapter.occurrence.logicalBefore =
      (source.selectingContext ++ (source.source.commit.selecting ++ source.source.commit.creating ++ hashing).map
        Program.filesystemEvent) ++ keyEvents.map Program.filesystemEvent ++
      .returned (.filesystem {op := .authenticate, left := message, right := key}) macReply ::
        (filling ++ [(markerRequest, markerReply)]).map Program.filesystemEvent := by
    simpa only [context, List.map_append, List.append_assoc] using macTrace
  obtain ⟨keyDigest⟩ := primitive_key_digest_at crypto adapter loaded keyTrace
  have markerTrace : adapter.occurrence.logicalBefore =
      (context ++ [.returned (.filesystem {op := .authenticate, left := message, right := key}) macReply] ++
        filling.map Program.filesystemEvent) ++ .returned (.filesystem markerRequest) markerReply :: [] := by
    exact macTrace.trans (by
      simp only [List.map_append, List.map_cons, List.map_nil, Program.filesystemEvent, List.append_assoc,
        List.cons_append, List.nil_append])
  obtain ⟨marked⟩ := primitive_observation_chunked adapter markerTrace rfl
  let marker := marked.observation
  have markerTail : marker.rawAfter = adapter.occurrence.inside.map Program.filesystemPrefixEvent := by
    have empty : marked.rawTail = [] := by
      have chunks := marked.chunks
      generalize rawEq : marked.rawTail = raw at chunks ⊢
      cases chunks
      rfl
    simpa only [empty, List.nil_append] using marked.suffix
  obtain ⟨macPosition, macTick, macEngine, afterMac, macSelected, macAction, macPresent,
    afterMacPresent, macCount, macBefore, macAfter⟩ := mac.sampled
  obtain ⟨markerPosition, markerTick, markerEngine, afterMarker, markerSelected, markerAction, markerPresent,
    afterMarkerPresent, markerCount, markerBefore, markerAfter⟩ := marker.sampled
  have macLess : macEngine.events.length < engine.events.length := by
    rw [macCount, mac.trace]
    simp only [List.length_append, List.length_cons]
    omega
  have markerLess : markerEngine.events.length < engine.events.length := by
    rw [markerCount, marker.trace]
    simp only [List.length_append, List.length_cons]
    omega
  refine ⟨{
    adapter
    source
    policyDigest
    key
    tag
    message
    exactMessage := rfl
    keyEvents
    loaded
    macReply
    mac
    macPosition
    macTick
    macSelected
    macAction
    macEarlier := source_ordinal_orders_positions journal macSelected selected actor macEngine engine macPresent present macLess
    tagSize
    interpreted := macPayload.symm.trans (crypto.authentication _ _ _ _ mac.actual rfl macZero
      (by simpa only [macPayload] using tagSize))
    markerReply
    marker
    markerPosition
    markerTick
    markerSelected
    markerAction
    markerEarlier := source_ordinal_orders_positions journal markerSelected selected actor markerEngine engine markerPresent present markerLess
    markerAccepted := ⟨markerZero, markerEmpty⟩ }, ⟨keyDigest⟩, HEq.rfl, rfl, markerTail,
      ⟨markerEngine, afterMarker, markerPresent, afterMarkerPresent, markerBefore, markerAfter⟩⟩

-- §AR-host-boundary.interfaces: The old consumer keeps its exact statement; the
-- stronger sibling additionally retains this same publisher's actual key digest.
theorem primitive_commit_authentication_at_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (source : HostCommitCall adapter.occurrence.logicalBefore request none) :
    ∃ receipt : PrimitiveCommitAuthentication runtime initial all position tick actor engine request observed hmac,
      HEq receipt.source source ∧
      receipt.source.source.commit.stage = source.source.commit.stage ∧
      receipt.marker.rawAfter = adapter.occurrence.inside.map Program.filesystemPrefixEvent ∧
      ∃ markerInput markerOutput,
        receipt.markerTick.before.actors actor = some markerInput ∧
        receipt.markerTick.after.actors actor = some markerOutput ∧
        receipt.marker.before = receipt.markerTick.before.project markerInput ∧
        receipt.marker.after = receipt.markerTick.after.project markerOutput := by
  obtain ⟨receipt, _, original⟩ := primitive_commit_authentication_with_key_digest crypto journal selected present adapter source
  exact ⟨receipt, original⟩


-- §AR-host-boundary.interfaces: Keep the original actual-commit authentication consumer.
-- §FS-host-boundary.publication: Source argument construction and ordering are derived
-- from the real publisher. The crypto premise interprets only its one actual raw MAC call.
theorem primitive_commit_authentication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (moving : request.op = .renameNew) :
    Nonempty (PrimitiveCommitAuthentication runtime initial all position tick actor engine request observed hmac) := by
  have primary := PrimitiveFilesystem.filesystem_occurrence_primary adapter.occurrence
    (by intro wrong; rw [moving] at wrong; cases wrong)
    (by intro wrong; rw [moving] at wrong; cases wrong)
    (by intro wrong; rw [moving] at wrong; cases wrong)
  have logical : Program.Prefix Entrypoint.run
      (adapter.occurrence.logicalBefore ++ [Program.filesystemPrefixEvent (request, none)]) := by
    simpa only [← primary, Program.filesystemPrefixEvent] using
      PrimitiveFilesystem.filesystem_occurrence_logical adapter.occurrence
  obtain ⟨source⟩ := entrypoint_commit_call logical moving
  obtain ⟨receipt, sameSource, sameStage, markerTail, markerSample⟩ := primitive_commit_authentication_at_source crypto journal
    selected present adapter source
  exact ⟨receipt⟩
-- §FS-host-boundary.publication: Exposure is an actual committed raw namespace effect,
-- independent of errno/acknowledgement and without assuming lifetime injectivity of inode IDs.
structure CommitExposure (before after : World) (request : Request) (tag : ByteArray) where
  source : Handle
  target : Handle
  object : ObjectId
  sourceReference : before.handles request.first = some source
  targetReference : before.handles request.second = some target
  sourceBinding : before.entries source.object request.left = some object
  absent : before.entries target.object request.right = none
  removed : after.entries source.object request.left = none
  published : after.entries target.object request.right = some object
  marker : after.attributes object Publication.attributeName = some (Publication.marker tag)

-- §AR-host-boundary.primitives: Only an actually exposed committed tag is a public signing
-- query. Private precommit marker writes and internal verification MAC calls are excluded.
structure ExposedSourceQuery {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (hmac : ByteArray → ByteArray → ByteArray)
    (secret message : ByteArray) (before : Nat) where
  position : Nat
  tick : ActorTick runtime
  actor : ActorId
  engine : EngineState
  request : Request
  observed : Option Reply
  selected : all[position]? = some tick
  action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed))
  present : tick.before.actors actor = some engine
  moving : request.op = .renameNew
  receipt : PrimitiveCommitAuthentication runtime initial all position tick actor engine request observed hmac
  exposure : CommitExposure (tick.before.project engine) tick.after.shared request receipt.tag
  key : receipt.key = secret
  bytes : receipt.message = message
  earlier : position < before

def SourceExposed {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (hmac : ByteArray → ByteArray → ByteArray)
    (secret : ByteArray) (before : Nat) (message : ByteArray) : Prop :=
  Nonempty (ExposedSourceQuery runtime initial all hmac secret message before)

-- §FS-host-boundary.publication: The raw committed effect is the only extra observation
-- needed to turn this exact source MAC/marker receipt into a public signing query.
def PrimitiveCommitAuthentication.exposed {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {position : Nat} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {hmac : ByteArray → ByteArray → ByteArray}
    (receipt : PrimitiveCommitAuthentication runtime initial all position tick actor engine request observed hmac)
    (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (moving : request.op = .renameNew)
    (exposure : CommitExposure (tick.before.project engine) tick.after.shared request receipt.tag)
    {limit : Nat} (earlier : position < limit) :
    ExposedSourceQuery runtime initial all hmac receipt.key receipt.message limit := {
  position
  tick
  actor
  engine
  request
  observed
  selected
  action
  present
  moving
  receipt
  exposure
  key := rfl
  bytes := rfl
  earlier }

theorem ExposedSourceQuery.actual_tag {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {hmac : ByteArray → ByteArray → ByteArray}
    {secret message : ByteArray} {limit : Nat}
    (query : ExposedSourceQuery runtime initial all hmac secret message limit) :
    query.tick.after.shared.attributes query.exposure.object Publication.attributeName =
      some (Publication.marker (hmac secret message)) := by
  have tag : query.receipt.tag = hmac secret message := by
    simpa only [query.key, query.bytes] using query.receipt.interpreted
  exact query.exposure.marker.trans (congrArg (fun bytes => some (Publication.marker bytes)) tag)

end LeanCage.Host.Kernel
