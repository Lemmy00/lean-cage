import FilesystemMarkerSources

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Correctness of each actual crypto call is separate from forgery.
structure CryptographicContract (kernel : Contract) (sha256 : ByteArray → ByteArray)
    (hmac : ByteArray → ByteArray → ByteArray) : Prop where
  hashing : ∀ before after request reply,
    kernel.step before request (some reply) after → request.op = .sha256 →
    reply.1 = 0 → reply.2.size = 32 → reply.2 = sha256 request.left
  authentication : ∀ before after request reply,
    kernel.step before request (some reply) after → request.op = .authenticate →
    reply.1 = 0 → reply.2.size = 32 → reply.2 = hmac request.right request.left
  comparison : ∀ before after request reply,
    kernel.step before request (some reply) after → request.op = .equalSecret →
    reply.1 = 1 → reply.2 = .empty → request.left = request.right

structure AuthenticationUse (kernel : Contract) (origin : FilesystemOrigin) (ordinal : Nat)
    (bundle : Validation.Bundle) (wire tag : ByteArray) (hmac : ByteArray → ByteArray → ByteArray)
    (before : World) (events : List (Request × Reply)) (after : World) where
  key : ByteArray
  keyEvents : List (Request × Reply)
  reply : Reply
  loaded : Retrieval.KeyObservation bundle keyEvents key
  shape : events = keyEvents ++ [({ op := .authenticate, left := wire, right := key }, reply)]
  actualBefore : World
  actualAfter : World
  leading : RecordedHistory kernel origin ordinal before keyEvents actualBefore
  operation : kernel.step actualBefore { op := .authenticate, left := wire, right := key } (some reply) actualAfter
  sampled : origin (ordinal + keyEvents.length) { op := .authenticate, left := wire, right := key }
    reply actualBefore actualAfter
  trailing : RecordedHistory kernel origin (ordinal + keyEvents.length + 1) actualAfter [] after
  zero : reply.1 = 0
  payload : reply.2 = tag
  sized : tag.size = 32
  interpreted : tag = hmac key wire

-- §FS-host-boundary.publication: Interpret the exact one MAC call inside this recorded helper.
theorem recorded_authentication {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (laws : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {wire tag : ByteArray}
    {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel origin ordinal (Publication.authenticate bundle wire) before events after (.ok tag)) :
    Nonempty (AuthenticationUse kernel origin ordinal bundle wire tag hmac before events after) := by
  obtain ⟨bounded, key, keyEvents, reply, shape, loaded, zero, payload, sized⟩ :=
    Retrieval.authenticate_source _ _ actual.1
  have history := actual.2
  rw [shape] at history
  obtain ⟨keyAfter, leading, rest⟩ := recorded_history_split keyEvents _ history
  obtain ⟨actualBefore, actualAfter, intervening, operation, sampled, trailing⟩ := recorded_history_head rest
  have leading := recorded_history_append leading intervening
  refine ⟨⟨key, keyEvents, reply, loaded, shape, actualBefore, actualAfter, ?_, operation, sampled,
    trailing, zero, payload, sized, ?_⟩⟩
  · simpa only [List.append_nil] using leading
  · have computed := laws.authentication _ _ _ _ operation rfl zero (by simpa only [payload] using sized)
    exact payload.symm.trans computed

structure RecordedMarkerAuthentication {kernel : Contract} (runtime : ActorRuntime kernel)
    (ticks : List (ActorTick runtime)) (actor : ActorId) (position : Nat) (engine : EngineState)
    (request : Request) (observed : Option Reply) (hmac : ByteArray → ByteArray → ByteArray) where
  source : HostMarkerCall engine.events request observed
  first : World
  last : World
  use : AuthenticationUse kernel (fun index request reply =>
    SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply) source.context.length
    source.invocation.authenticated.bundle
    (Publication.markerWire source.source.effective source.source.source.display source.source.stdoutHash
      source.source.stderrHash source.source.source.marker.policyDigest source.source.source.parent source.source.source.stage)
    source.source.source.marker.tag hmac first source.source.source.marker.authenticating last
  macPosition : Nat
  macTick : ActorTick runtime
  selected : ticks[macPosition]? = some macTick
  action : macTick.action = .returned actor
    (.filesystem {
      op := .authenticate
      left := Publication.markerWire source.source.effective source.source.source.display source.source.stdoutHash
        source.source.stderrHash source.source.source.marker.policyDigest source.source.source.parent source.source.source.stage
      right := use.key }) use.reply
  earlier : macPosition < position

-- §FS-host-boundary.acceptance: The publisher's key/MAC sample precedes this same marker tick.
theorem actual_recorded_marker_authentication {kernel : Contract} {runtime : ActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (laws : CryptographicContract kernel sha256 hmac) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (marked : request.op = .setAttribute) (named : request.left = Publication.attributeName) :
    Nonempty (RecordedMarkerAuthentication runtime ticks actor position engine request observed hmac) := by
  obtain ⟨source⟩ := selected_publisher_marker journal selected action present marked named
  obtain ⟨actorHistory⟩ := actual_selected_actor_history descriptors lifetimes references environment
    journal selected action present
  have history := actorHistory.history
  rw [marker_authentication_trace source] at history
  obtain ⟨first, last, leading, _, authentication, trailing⟩ := recorded_filesystem_phase history
    source.source.source.marker.authenticated
  have actual : RecordedRun kernel (fun index request reply =>
      SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply) source.context.length
      (Publication.authenticate source.invocation.authenticated.bundle
        (Publication.markerWire source.source.effective source.source.source.display source.source.stdoutHash
          source.source.stderrHash source.source.source.marker.policyDigest source.source.source.parent
          source.source.source.stage)) first source.source.source.marker.authenticating last
      (Except.ok source.source.source.marker.tag : Result ByteArray) := by
    exact ⟨source.source.source.marker.authenticated, by simpa only [Nat.zero_add] using authentication⟩
  obtain ⟨use⟩ := recorded_authentication laws actual
  obtain ⟨macPosition, macTick, macEngine, nextEngine, macAt, macAction, macPresent,
    afterPresent, count, beforeShape, afterShape⟩ := use.sampled
  have earlierSource : macEngine.events.length < engine.events.length := by
    rw [marker_authentication_trace source, use.shape]
    simp only [List.length_append, List.length_map, List.length_singleton] at count ⊢
    omega
  exact ⟨⟨source, first, last, use, macPosition, macTick, macAt, macAction,
    source_ordinal_orders_positions journal macAt selected actor macEngine engine macPresent present earlierSource⟩⟩

structure VerificationUse (kernel : Contract) (origin : FilesystemOrigin) (ordinal : Nat)
    (bundle : Validation.Bundle) (wire supplied : ByteArray) (hmac : ByteArray → ByteArray → ByteArray)
    (before : World) (events : List (Request × Reply)) (after : World) where
  tag : ByteArray
  authenticating : List (Request × Reply)
  reply : Reply
  authenticationAfter : World
  authentication : AuthenticationUse kernel origin ordinal bundle wire tag hmac
    before authenticating authenticationAfter
  comparisonBefore : World
  comparisonAfter : World
  leading : RecordedHistory kernel origin (ordinal + authenticating.length)
    authenticationAfter [] comparisonBefore
  operation : kernel.step comparisonBefore {
    op := .equalSecret
    left := Publication.marker tag
    right := supplied } (some reply) comparisonAfter
  sampled : origin (ordinal + authenticating.length) {
    op := .equalSecret
    left := Publication.marker tag
    right := supplied } reply comparisonBefore comparisonAfter
  trailing : RecordedHistory kernel origin (ordinal + authenticating.length + 1) comparisonAfter [] after
  trace : events = authenticating ++ [({
    op := .equalSecret
    left := Publication.marker tag
    right := supplied }, reply)]
  matching : supplied = Publication.marker (hmac authentication.key wire)

-- §FS-host-boundary.publication: An internal comparison is verified without exposing its MAC.
theorem recorded_verification {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (laws : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {wire supplied : ByteArray}
    {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel origin ordinal (Publication.verify bundle wire supplied)
      before events after (.ok ())) :
    Nonempty (VerificationUse kernel origin ordinal bundle wire supplied hmac before events after) := by
  have source := actual.1
  unfold Publication.verify at source
  split at source
  · cases source
  · have stage : RecordedRun kernel origin ordinal _ before events after (.ok () : Result Unit) :=
      ⟨source, actual.2⟩
    obtain ⟨authenticating, result, last, authenticatedAfter, shape, authenticatingRun, rest⟩ :=
      recorded_run_bind_split _ _ stage
    cases result with
    | error => cases rest.1
    | ok tag =>
      obtain ⟨reply, finalEvents, comparedShape, final⟩ := Snapshot.returns_call_split rest.1
      dsimp only [Filesystem.Program.bind] at final
      split at final
      · rename_i accepted
        obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq final
        have fields : reply.1 = 1 ∧ reply.2 = .empty := by
          have checked : reply.1 = 1 ∧ reply.2.isEmpty = true := by
            simpa only [Bool.and_eq_true, beq_iff_eq] using accepted
          exact ⟨checked.1, ByteArray.size_eq_zero_iff.mp
            (by simpa only [ByteArray.isEmpty, beq_iff_eq] using checked.2)⟩
        obtain ⟨authentication⟩ := recorded_authentication laws authenticatingRun
        have history := rest.2
        rw [comparedShape] at history
        obtain ⟨comparisonBefore, comparisonAfter, leading, comparison, comparisonOrigin, trailing⟩ :=
          recorded_history_head history
        have matching := laws.comparison _ _ _ _ comparison rfl fields.1 fields.2
        refine ⟨⟨tag, authenticating, reply, authenticatedAfter, authentication,
          comparisonBefore, comparisonAfter, leading, comparison, comparisonOrigin, trailing, ?_, ?_⟩⟩
        · simpa only [comparedShape] using shape
        · simpa only [authentication.interpreted] using matching.symm
      · split at final <;> cases final

end LeanCage.Host.Kernel
