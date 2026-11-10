import RetrievalProofs.Effects

namespace LeanCage.Host.Retrieval

open Filesystem

def KeyObservation (bundle : Validation.Bundle) (events : List (Request × Reply)) (key : ByteArray) : Prop :=
  ∃ files name expected uid opened fd privateReply copies closing hashes copied digest,
    Validation.bundleFiles bundle.manifest = some files ∧
    files.find? (fun field => field.1 == Publication.keyName) = some (name, .string expected) ∧
    events = [({ op := .euid }, uid), ({
      op := .openAt
      first := cwd
      second := readFlags
      left := (bundle.root ++ "/" ++ Publication.keyName).toUTF8 }, opened),
      ({ op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName }, privateReply)] ++
      copies ++ closing ++ hashes ∧
    nativeError uid = false ∧ uid.2 = .empty ∧ descriptor opened = some fd ∧
    privateReply.1 = 1 ∧ privateReply.2 = PrivateNames.attributeValue ∧
    Snapshot.CopiedObservation fd copies copied ∧
    Returns (closeResult fd (.ok copied)) closing (.ok copied) ∧
    copied.bytes = key ∧ key.size = 32 ∧ copied.stat.uid = uid.1.toNat ∧
    copied.stat.mode &&& 511 = 256 ∧
    Returns (Filesystem.hash key) hashes (.ok digest) ∧ Snapshot.hex digest = expected

-- §FS-host-boundary.publication: Key marking, owner/mode and hashing share one retained descriptor.
theorem key_source (bundle : Validation.Bundle) {events : List (Request × Reply)} {key : ByteArray}
    (run : Returns (Publication.authenticationKey bundle) events (.ok key)) :
    KeyObservation bundle events key := by
  unfold Publication.authenticationKey at run
  split at run
  · rename_i files inventory
    split at run
    · rename_i name expected identified
      obtain ⟨uid, afterEvents, rfl, afterUid⟩ := Snapshot.returns_call_split run
      dsimp only [Filesystem.Program.bind] at afterUid
      split at afterUid
      · cases afterUid
      · rename_i uidValid
        obtain ⟨opened, restEvents, rfl, afterOpen⟩ := Snapshot.returns_call_split afterUid
        dsimp only [Filesystem.Program.bind] at afterOpen
        split at afterOpen
        · rename_i fd descriptorValue
          obtain ⟨privateReply, lastEvents, rfl, afterPrivate⟩ := Snapshot.returns_call_split afterOpen
          dsimp only [Filesystem.Program.bind] at afterPrivate
          split at afterPrivate
          · have impossible := (Snapshot.closeResult_provenance _ _ afterPrivate).1
            cases impossible
          · rename_i privateValid
            obtain ⟨copyEvents, result, tailEvents, copiedRun, afterCopy, copyShape⟩ :=
              Snapshot.returns_bind_split _ _ afterPrivate
            cases result with
            | error => cases afterCopy
            | ok copied =>
              dsimp only at afterCopy
              split at afterCopy
              · cases afterCopy
              · rename_i privateKey
                obtain ⟨hashes, result, last, hashRun, afterHash, hashShape⟩ :=
                  Snapshot.returns_bind_split _ _ afterCopy
                cases result with
                | error => cases afterHash
                | ok digest =>
                  dsimp only at afterHash
                  split at afterHash
                  · cases afterHash
                  · rename_i identity
                    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq afterHash
                    cases same
                    obtain ⟨copies, input, closing, copyRun, closeRun, closeShape⟩ :=
                      Snapshot.returns_bind_split _ _ copiedRun
                    have same := (Snapshot.closeResult_provenance _ _ closeRun).1
                    cases same
                    have observed := (Snapshot.copyOpened_provenance _ _ copyRun).2
                    have uidFields : nativeError uid = false ∧ uid.2 = .empty := by
                      have properties : nativeError uid = false ∧ uid.2.isEmpty = true := by simpa using uidValid
                      exact ⟨properties.1, ByteArray.size_eq_zero_iff.mp
                        (by simpa only [ByteArray.isEmpty, beq_iff_eq] using properties.2)⟩
                    have privateFields : privateReply.1 = 1 ∧ privateReply.2 = PrivateNames.attributeValue := by
                      simpa [Bool.or_eq_true] using privateValid
                    have keyFields : copied.bytes.size = 32 ∧ copied.stat.uid = uid.1.toNat ∧
                        copied.stat.mode &&& 511 = 256 := by simpa [Bool.or_eq_true, and_assoc] using privateKey
                    have digestField : Snapshot.hex digest = expected := by simpa using identity
                    exact ⟨files, name, expected, uid, opened, fd, privateReply, copies, closing,
                      hashes, copied, digest, inventory, identified,
                      by simp only [copyShape, hashShape, closeShape, List.append_nil, List.cons_append,
                        List.nil_append, List.append_assoc],
                      uidFields.1, uidFields.2, descriptorValue, privateFields.1, privateFields.2,
                      observed, closeRun, rfl, keyFields.1, keyFields.2.1, keyFields.2.2, hashRun, digestField⟩
        · cases afterOpen
    · cases run
  · cases run

def AuthenticationObservation (bundle : Validation.Bundle) (wire tag : ByteArray)
    (events : List (Request × Reply)) : Prop :=
  wire.size ≤ Publication.metadataMax ∧ ∃ key keyEvents reply,
    events = keyEvents ++ [({ op := .authenticate, left := wire, right := key }, reply)] ∧
    KeyObservation bundle keyEvents key ∧ reply.1 = 0 ∧ reply.2 = tag ∧ tag.size = 32

theorem authenticate_source (bundle : Validation.Bundle) (wire : ByteArray)
    {events : List (Request × Reply)} {tag : ByteArray}
    (run : Returns (Publication.authenticate bundle wire) events (.ok tag)) :
    AuthenticationObservation bundle wire tag events := by
  unfold Publication.authenticate at run
  split at run
  · cases run
  · rename_i bounded
    obtain ⟨keyEvents, result, tailEvents, keyRun, afterKey, shape⟩ := Snapshot.returns_bind_split _ _ run
    cases result with
    | error => cases afterKey
    | ok key =>
      obtain ⟨reply, lastEvents, tailShape, afterCall⟩ := Snapshot.returns_call_split afterKey
      dsimp only [Filesystem.Program.bind] at afterCall
      split at afterCall
      · rename_i checked
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq afterCall
        cases same
        have fields : reply.1 = 0 ∧ reply.2.size = 32 := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using checked
        exact ⟨by omega, key, keyEvents, reply, by simpa only [tailShape] using shape,
          key_source _ keyRun, fields.1, rfl, fields.2⟩
      · cases afterCall

def VerificationObservation (bundle : Validation.Bundle) (wire supplied : ByteArray)
    (events : List (Request × Reply)) : Prop :=
  supplied.size = Publication.markerMagic.size + 32 ∧ ∃ tag authentication reply,
    events = authentication ++ [({
      op := .equalSecret
      left := Publication.marker tag
      right := supplied }, reply)] ∧
    AuthenticationObservation bundle wire tag authentication ∧ reply.1 = 1 ∧ reply.2 = .empty

-- §FS-host-boundary.publication: Verification records the same MAC and constant-time comparison.
theorem verify_source (bundle : Validation.Bundle) (wire supplied : ByteArray)
    {events : List (Request × Reply)}
    (run : Returns (Publication.verify bundle wire supplied) events (.ok ())) :
    VerificationObservation bundle wire supplied events := by
  unfold Publication.verify at run
  split at run
  · cases run
  · rename_i size
    obtain ⟨authentication, result, last, authenticated, compared, shape⟩ :=
      Snapshot.returns_bind_split _ _ run
    cases result with
    | error => cases compared
    | ok tag =>
      obtain ⟨reply, finalEvents, comparedShape, final⟩ := Snapshot.returns_call_split compared
      dsimp only [Filesystem.Program.bind] at final
      split at final
      · rename_i accepted
        obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq final
        have fields : reply.1 = 1 ∧ reply.2 = .empty := by
          have parts : reply.1 = 1 ∧ reply.2.isEmpty = true := by
            simpa only [Bool.and_eq_true, beq_iff_eq] using accepted
          exact ⟨parts.1, ByteArray.size_eq_zero_iff.mp
            (by simpa only [ByteArray.isEmpty, beq_iff_eq] using parts.2)⟩
        exact ⟨by simpa only [bne_iff_ne, Classical.not_not] using size,
          tag, authentication, reply, by simpa only [comparedShape] using shape,
          authenticate_source _ _ authenticated, fields.1, fields.2⟩
      · split at final <;> cases final

-- §AR-host-boundary.primitives: These laws concern individual actual crypto replies only.
def AuthenticationReplies (hmac : ByteArray → ByteArray → ByteArray)
    (events : List (Request × Reply)) : Prop :=
  ∀ request reply, (request, reply) ∈ events → request.op = .authenticate →
    reply.1 = 0 → reply.2.size = 32 → reply.2 = hmac request.right request.left

def EqualityReplies (events : List (Request × Reply)) : Prop :=
  ∀ request reply, (request, reply) ∈ events → request.op = .equalSecret →
    reply.1 = 1 → reply.2 = .empty → request.left = request.right

theorem verify_authenticated (bundle : Validation.Bundle) (wire supplied : ByteArray)
    (hmac : ByteArray → ByteArray → ByteArray) {events : List (Request × Reply)}
    (run : Returns (Publication.verify bundle wire supplied) events (.ok ()))
    (authentication : AuthenticationReplies hmac events) (equality : EqualityReplies events) :
    ∃ key keyEvents, KeyObservation bundle keyEvents key ∧
      supplied = Publication.marker (hmac key wire) := by
  obtain ⟨_, tag, authEvents, compared, shape, observed, one, empty⟩ := verify_source _ _ _ run
  obtain ⟨_, key, keyEvents, reply, authShape, keyObserved, zero, payload, size⟩ := observed
  have hashed : tag = hmac key wire := by
    have returned := authentication ({ op := .authenticate, left := wire, right := key } : Request)
      reply (by rw [shape, authShape]; simp) rfl zero (by simpa only [payload] using size)
    exact payload.symm.trans returned
  have same : Publication.marker tag = supplied := by
    exact equality ({ op := .equalSecret, left := Publication.marker tag, right := supplied } : Request)
      compared (by rw [shape]; simp) rfl one empty
  exact ⟨key, keyEvents, keyObserved, by simpa only [hashed] using same.symm⟩

end LeanCage.Host.Retrieval
