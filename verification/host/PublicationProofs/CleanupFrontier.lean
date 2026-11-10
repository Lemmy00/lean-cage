import PublicationProofs.Frontier

namespace LeanCage.Host.Publication
open Filesystem Kernel

private theorem readonly_no_unlink {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (fun request => request.op ≠ .unlinkAt) program :=
  request_weaken (read_only_namespace_passive source) (fun request passive removing => by
    unfold NamespacePassive at passive
    rw [removing] at passive
    exact passive)

private theorem opening_no_unlink (uid : Nat) (parent : UInt64) (name : String) (create : Bool) :
    RequestProgram (fun request => request.op ≠ .unlinkAt) (childOpening uid parent name create) := by
  cases create with
  | false => exact readonly_no_unlink (Retrieval.openAt_readOnly _ _ _)
  | true =>
    unfold childOpening Directories.ensureAt
    simp only [↓reduceIte]
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    dsimp only [Filesystem.Program.bind]
    repeat' first
      | exact .pure _
      | split
      | exact readonly_no_unlink (Retrieval.openAt_readOnly _ _ _)

-- §FS-host-boundary.ownership: A lost unlink still has the actual completed
-- directory chain and current leaf call. No successful cleanup or future
-- unlink acknowledgement is needed to identify its source-relative authority.
theorem under_unlink_frontier {α : Type} (uid : Nat) (root : UInt64) (names : List String)
    (create : Bool) (action : UInt64 → Filesystem.Program (Result α))
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix (under uid root names create action) (before ++ [(request, observed)]))
    (removing : request.op = .unlinkAt) :
    Nonempty (UnderActionFrontier uid root names create action before request observed) :=
  under_action_frontier uid root names create action (fun request => request.op = .unlinkAt)
    (fun parent name => opening_no_unlink uid parent name create)
    (fun fd value => readonly_no_unlink (Retrieval.readOnly_snapshot (Snapshot.closeResult_input fd value))) active removing

structure RelativeUnlinkFrontier (uid : Nat) (root : UInt64) (components : List String) (directory : Bool)
    (before : List (Request × Option Reply)) (request : Request) (observed : Option Reply) where
  name : String
  named : components.getLast? = some name
  parent : UInt64
  opening : List (Request × Reply)
  inside : List (Request × Option Reply)
  chain : DirectoryChain uid false root components.dropLast opening parent
  active : Prefix (.call {
    op := .unlinkAt, first := parent, second := (if directory then 512 else 0), left := name.toUTF8 }
    (fun reply => if reply.1 == 0 && reply.2.isEmpty then pure (.ok () : Result Unit)
      else pure (.error (failure "stage unlinkat" reply)))) (inside ++ [(request, observed)])
  operation : request = {
    op := .unlinkAt, first := parent, second := (if directory then 512 else 0), left := name.toUTF8 }
  trace : before = completed opening ++ inside

theorem unlink_relative_frontier (uid : Nat) (root : UInt64) (components : List String) (directory : Bool)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix (unlinkRelative uid root components directory) (before ++ [(request, observed)]))
    (removing : request.op = .unlinkAt) :
    Nonempty (RelativeUnlinkFrontier uid root components directory before request observed) := by
  unfold unlinkRelative at active
  split at active
  · rename_i name named
    rcases filesystem_last_bind_split _ _ active with traversing |
        ⟨traversing, result, after, called, following, trace⟩
    · obtain ⟨frontier⟩ := under_unlink_frontier uid root components.dropLast false _ traversing removing
      let requested : Request := {
        op := .unlinkAt
        first := frontier.parent
        second := if directory then 512 else 0
        left := name.toUTF8 }
      have profile : RequestProgram (fun operation => operation = requested)
          (.call requested (fun reply => if reply.1 == 0 && reply.2.isEmpty then pure (.ok () : Result Unit)
            else pure (.error (failure "stage unlinkat" reply)))) := by
        apply RequestProgram.call (allowed := fun operation => operation = requested) rfl
        intro reply
        split <;> exact .pure _
      have operation := request_prefix profile frontier.active (request, observed) (by simp)
      exact ⟨⟨name, named, frontier.parent, frontier.opening, frontier.inside, frontier.chain,
        frontier.active, operation, frontier.trace⟩⟩
    · have length := congrArg List.length (Snapshot.prefix_pure_empty following)
      simp only [List.length_append, List.length_singleton, List.length_nil] at length
      omega
  · have length := congrArg List.length (Snapshot.prefix_pure_empty active)
    simp only [List.length_append, List.length_singleton, List.length_nil] at length
    omega

theorem relative_unlink_component {uid : Nat} {root : UInt64} {components : List String} {directory : Bool}
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : RelativeUnlinkFrontier uid root components directory before request observed)
    (valid : ∀ name ∈ components, Snapshot.ValidComponent name) : Directories.component request.left = true := by
  rw [source.operation]
  have accepted := valid source.name (List.mem_of_getLast? source.named)
  have nonempty : source.name.toUTF8.size ≠ 0 := Nat.ne_of_gt accepted.1
  rcases accepted with ⟨positive, bounded, notDot, notUp, noNul, noSlash⟩
  simp_all [Directories.component, ByteArray.isEmpty]

theorem relative_unlink_inside_empty {uid : Nat} {root : UInt64} {components : List String} {directory : Bool}
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : RelativeUnlinkFrontier uid root components directory before request observed) : source.inside = [] := by
  have bounded : ∀ {events}, Prefix (.call {
        op := .unlinkAt, first := source.parent, second := (if directory then 512 else 0), left := source.name.toUTF8 }
        (fun reply => if reply.1 == 0 && reply.2.isEmpty then pure (.ok () : Result Unit)
          else pure (.error (failure "stage unlinkat" reply)))) events → events.length ≤ 1 := by
    intro events active
    cases active with
    | empty => simp
    | lost => simp
    | returned request next reply events following =>
      have empty : events = [] := by
        dsimp only at following
        split at following <;> exact Snapshot.prefix_pure_empty following
      rw [empty]
      simp
  have length := bounded source.active
  simp only [List.length_append, List.length_singleton] at length
  exact List.length_eq_zero_iff.mp (by omega)

end LeanCage.Host.Publication
