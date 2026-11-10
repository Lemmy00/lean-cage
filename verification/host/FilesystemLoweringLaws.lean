import FilesystemApplicationLowering

namespace LeanCage.Host.Filesystem.Program

theorem bind_assoc {α β γ : Type} (first : Program α) (second : α → Program β)
    (third : β → Program γ) :
    (first.bind second).bind third = first.bind (fun value => (second value).bind third) := by
  induction first with
  | pure value => rfl
  | call request next ih =>
    change Program.call request _ = Program.call request _
    exact congrArg (Program.call request) (funext ih)

-- §AR-host-boundary.primitives: Expanding a source bind preserves the exact primitive sequence.
theorem lower_bind {α β : Type} (first : Program α) (second : α → Program β) :
    (first.bind second).lower = first.lower.bind (fun value => (second value).lower) := by
  induction first with
  | pure value => rfl
  | call request next ih =>
    change (guardedCall request).bind (fun reply => ((next reply).bind second).lower) =
      ((guardedCall request).bind (fun reply => (next reply).lower)).bind (fun value => (second value).lower)
    rw [bind_assoc]
    exact congrArg (Program.bind (guardedCall request)) (funext ih)

end LeanCage.Host.Filesystem.Program

namespace LeanCage.Host.Program

theorem lift_filesystem_bind {α β : Type} (first : Filesystem.Program α)
    (second : α → Filesystem.Program β) :
    liftFilesystem (first.bind second) =
      (liftFilesystem first).bind (fun value => liftFilesystem (second value)) := by
  induction first with
  | pure value => rfl
  | call request next ih =>
    change Program.call (.filesystem request) _ = Program.call (.filesystem request) _
    exact congrArg (Program.call (.filesystem request)) (funext ih)

end LeanCage.Host.Program

namespace LeanCage.Host.PrimitiveFilesystem

-- §AR-host-boundary.interfaces: The real mixed interpreter and filesystem helper use one lower.
theorem lower_lift_filesystem {α : Type} (program : Filesystem.Program α) :
    lower (Program.liftFilesystem program) = Program.liftFilesystem program.lower := by
  induction program with
  | pure value => rfl
  | call request next ih =>
    change (Program.liftFilesystem (Filesystem.guardedCall request)).bind
      (fun reply => lower (Program.liftFilesystem (next reply))) =
      Program.liftFilesystem ((Filesystem.guardedCall request).bind (fun reply => (next reply).lower))
    rw [Program.lift_filesystem_bind]
    exact congrArg (Program.bind (Program.liftFilesystem (Filesystem.guardedCall request))) (funext ih)

end LeanCage.Host.PrimitiveFilesystem
