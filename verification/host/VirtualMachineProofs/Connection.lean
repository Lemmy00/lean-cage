import VirtualMachineProofs.Progress

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §FS-host-boundary.ownership: A stored connection comes from this actual fresh socket/connect
-- pair.
structure Connected (path : ByteArray) (fd : UInt64) (events : List Program.Event) where
  created : Reply
  creation : descriptor created = some fd
  connected : Reply
  success : connected.1 = 0 ∧ connected.2.isEmpty = true
  trace : events = [.returned (.filesystem { op := .socket }) created,
    .returned (.filesystem { op := .connect, first := fd, left := path }) connected]

theorem connect_source (path : ByteArray) (fd : UInt64) {events : List Program.Event}
    (run : Program.Returns (connect path) events (.ok (some fd))) :
    path.size ≤ 107 ∧ rawPathValid path = true ∧ Nonempty (Connected path fd events) := by
  unfold connect at run
  split at run
  · cases run
  · rename_i valid
    have valid : path.size ≤ 107 ∧ rawPathValid path = true := by simpa using valid
    dsimp only [Runtime.perform, Program.liftFilesystem, Filesystem.Program.effect, Program.bind] at run
    cases run with
    | call _ _ created tail _ rest =>
      dsimp only [Program.bind] at rest
      cases creation : descriptor created with
      | none => simp only [creation] at rest; cases rest
      | some actual =>
        simp only [creation] at rest
        try dsimp only [Runtime.perform, Program.liftFilesystem, Filesystem.Program.effect, Program.bind] at rest
        cases rest with
        | call _ _ connected more _ ending =>
          dsimp only [Program.bind] at ending
          split at ending
          · rename_i success
            obtain ⟨rfl, equal⟩ := Program.returns_pure _ ending
            have equal : fd = actual := Option.some.inj (Except.ok.inj equal)
            subst actual
            exact ⟨valid.1, valid.2, ⟨⟨created, creation, connected, by simpa using success, rfl⟩⟩⟩
          · dsimp only [close, Runtime.perform, Program.liftFilesystem,
              Filesystem.Program.effect, Program.bind] at ending
            cases ending with
            | call _ _ closed last _ final =>
              dsimp only [Program.bind] at final
              split at final <;> cases final

theorem connected_fd_bound (path : ByteArray) (fd : UInt64) (events : List Program.Event)
    (connection : Connected path fd events) : fd.toNat ≤ 2147483647 := by
  have creation := connection.creation
  unfold descriptor at creation
  split at creation
  · contradiction
  · rename_i bound
    simp only [Option.some.injEq] at creation
    have bound : nativeError connection.created = false ∧ connection.created.2.isEmpty = true ∧
        connection.created.1.toNat ≤ 2147483647 := by simpa [and_assoc] using bound
    simpa only [creation] using bound.2.2

end LeanCage.Host.VirtualMachine
