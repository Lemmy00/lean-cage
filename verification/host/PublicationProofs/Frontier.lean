import PublicationProofs.Relative
import FilesystemPublicationSource

namespace LeanCage.Host.Publication
open Filesystem Kernel

def childOpening (uid : Nat) (parent : UInt64) (name : String) (create : Bool) :
    Filesystem.Program (Result Directories.Opened) :=
  if create then Directories.ensureAt uid parent name.toUTF8 else Directories.openAt uid parent name.toUTF8

-- §FS-host-boundary.ownership: This is the real completed chain before a nested
-- source operation; no future child return or independent pathname view is used.
inductive DirectoryChain (uid : Nat) (create : Bool) :
    UInt64 → List String → List (Request × Reply) → UInt64 → Prop where
  | root (parent : UInt64) : DirectoryChain uid create parent [] [] parent
  | child {parent : UInt64} {name : String} {names : List String} {opened : Directories.Opened}
      {opening following : List (Request × Reply)} {last : UInt64}
      (component : Snapshot.ValidComponent name)
      (actual : Returns (childOpening uid parent name create) opening (.ok opened))
      (below : DirectoryChain uid create opened.fd names following last) :
      DirectoryChain uid create parent (name :: names) (opening ++ following) last

structure UnderActionFrontier {α : Type} (uid : Nat) (root : UInt64) (names : List String)
    (create : Bool) (action : UInt64 → Filesystem.Program (Result α))
    (before : List (Request × Option Reply)) (request : Request) (observed : Option Reply) where
  parent : UInt64
  opening : List (Request × Reply)
  inside : List (Request × Option Reply)
  chain : DirectoryChain uid create root names opening parent
  active : Prefix (action parent) (inside ++ [(request, observed)])
  trace : before = completed opening ++ inside

private theorem pure_no_last {α : Type} {value : α} {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

-- §FS-host-boundary.publication: Invert the actual recursive traversal at its
-- selected action. Failed opens, both mkdir outcomes and loss remain source paths;
-- only real earlier acknowledged directory openings extend this chain.
theorem under_action_frontier {α : Type} (uid : Nat) (root : UInt64) (names : List String)
    (create : Bool) (action : UInt64 → Filesystem.Program (Result α))
    (query : Request → Prop)
    (openingQuiet : ∀ parent name, RequestProgram (fun operation => ¬ query operation) (childOpening uid parent name create))
    (closingQuiet : ∀ fd (value : Result α), RequestProgram (fun operation => ¬ query operation) (closeResult fd value))
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix (under uid root names create action) (before ++ [(request, observed)]))
    (selected : query request) :
    Nonempty (UnderActionFrontier uid root names create action before request observed) := by
  induction names generalizing root before with
  | nil => exact ⟨⟨root, [], before, .root root, active, rfl⟩⟩
  | cons name names ih =>
    unfold under at active
    split at active
    · exact False.elim (pure_no_last active)
    · rename_i valid
      let afterOpening : Result Directories.Opened → Filesystem.Program (Result α) := fun result => match result with
        | .error error => .pure (.error error)
        | .ok child => (under uid child.fd names create action).bind (closeResult child.fd)
      have choice : (if create then (Directories.ensureAt uid root name.toUTF8).bind afterOpening
          else (Directories.openAt uid root name.toUTF8).bind afterOpening) =
          (childOpening uid root name create).bind afterOpening := by cases create <;> rfl
      change Prefix (if create then (Directories.ensureAt uid root name.toUTF8).bind afterOpening
        else (Directories.openAt uid root name.toUTF8).bind afterOpening) (before ++ [(request, observed)]) at active
      rw [choice] at active
      rcases filesystem_last_bind_split _ _ active with opening |
          ⟨opening, result, following, opened, afterOpen, shape⟩
      · exact False.elim (request_prefix (openingQuiet root name) opening (request, observed) (by simp) selected)
      · cases result with
        | error error => exact False.elim (pure_no_last afterOpen)
        | ok child =>
          rcases filesystem_last_bind_split _ _ afterOpen with inside |
              ⟨middle, result, closing, called, afterCall, nextShape⟩
          · obtain ⟨frontier⟩ := ih child.fd inside
            exact ⟨{
              parent := frontier.parent
              opening := opening ++ frontier.opening
              inside := frontier.inside
              chain := .child (by simpa using valid) opened frontier.chain
              active := frontier.active
              trace := shape.trans ((congrArg (completed opening ++ ·) frontier.trace).trans (by
                simp only [completed, List.map_append, List.append_assoc])) }⟩
          · exact False.elim (request_prefix (closingQuiet child.fd result) afterCall (request, observed) (by simp) selected)

end LeanCage.Host.Publication
