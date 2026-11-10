import PrefixOrigins

namespace LeanCage.Host.PreparationPrefixCuts
open Filesystem ApplicationProofs

structure Loaded (request : GatewayWire.Request) where
  raw : ByteArray
  loading : List (Request × Reply)
  load : Returns (Validation.loadPolicy request) loading (.ok raw)

def Loaded.events {request} (context : Loaded request) :=
  context.loading.map Program.filesystemEvent

structure Validated (request : GatewayWire.Request) (bundle : Validation.Bundle) where
  loaded : Loaded request
  value : Json.Value
  policy : Policy.Accepted
  validating : List Program.Event
  validate : Program.Returns (Validation.validateCopied bundle loaded.raw) validating (.ok value)
  budgets : Policy.budgets value loaded.raw = .ok policy

def Validated.events {request bundle} (context : Validated request bundle) :=
  context.loaded.events ++ context.validating

structure Bound (request : GatewayWire.Request) (bundle : Validation.Bundle) where
  validated : Validated request bundle
  frozen : Snapshot.Frozen
  policy : Policy.Accepted
  copying : List (Request × Reply)
  snapshot : Returns (Snapshot.freeze (inputWorkspace request) (inputStdin request)
    validated.policy.snapshot) copying (.ok frozen)
  binding : Policy.bind validated.policy frozen = .ok policy

def Bound.events {request bundle} (context : Bound request bundle) :=
  context.validated.events ++ context.copying.map Program.filesystemEvent

-- §FS-host-boundary.snapshot: Interrupted copying and validation keep their real prior inputs.
inductive Cut (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (before : List Program.Event) (event : Program.Event) : Type 1 where
  | loading (active : Program.Prefix
      (Program.liftFilesystem (Validation.loadPolicy request)) (before ++ [event]))
  | validating (context : Loaded request) (inside : List Program.Event)
      (active : Program.Prefix (Validation.validateCopied bundle context.raw) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | copying (context : Validated request bundle) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (Snapshot.freeze
        (inputWorkspace request) (inputStdin request) context.policy.snapshot)) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | revalidating (context : Bound request bundle) (inside : List Program.Event)
      (active : Program.Prefix (Validation.validateCopied bundle context.policy.raw) (inside ++ [event]))
      (trace : before = context.events ++ inside)

-- §FS-host-boundary.acceptance: No successful earlier phase is assumed for a lost current call.
theorem prepare_policy_cut (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix (preparePolicy request bundle).run (before ++ [event])) :
    Nonempty (Cut request bundle before event) := by
  unfold preparePolicy at active
  rcases last_checked_bind _ _ active with loading |
      ⟨loading, raw, afterLoad, load, rest, loadShape⟩
  · exact ⟨.loading loading⟩
  · obtain ⟨loadSource, loadRun, loadEvents⟩ := filesystem_source _ load
    let loaded : Loaded request := ⟨raw, loadSource, loadRun⟩
    have loadedShape : before = loaded.events ++ afterLoad := by
      simpa only [Loaded.events, loaded, loadEvents] using loadShape
    rcases last_checked_bind _ _ rest with validating |
        ⟨validating, value, afterValidate, validate, rest, validateShape⟩
    · exact ⟨.validating loaded afterLoad validating loadedShape⟩
    · rcases last_checked_bind _ _ rest with budgeting |
          ⟨budgeting, policy, afterBudget, budgeted, rest, budgetShape⟩
      · exact False.elim (checked_has_no_last _ _ _ budgeting)
      · obtain ⟨budgets, budgetEmpty⟩ := checked_source _ budgeted
        let validated : Validated request bundle := ⟨loaded, value, policy, validating, validate, budgets⟩
        have validatedShape : before = validated.events ++ afterBudget := by
          simp only [Validated.events, validated, loadedShape, validateShape, budgetShape,
            budgetEmpty, List.nil_append, List.append_assoc]
        rcases last_checked_bind _ _ rest with copying |
            ⟨copying, frozen, afterCopy, snapshot, rest, copyShape⟩
        · exact ⟨.copying validated afterBudget copying validatedShape⟩
        · rcases last_checked_bind _ _ rest with binding |
              ⟨binding, policy, afterBind, bound, rest, bindShape⟩
          · exact False.elim (checked_has_no_last _ _ _ binding)
          · obtain ⟨binding, bindEmpty⟩ := checked_source _ bound
            obtain ⟨copySource, snapshotRun, copyEvents⟩ := filesystem_source _ snapshot
            let bound : Bound request bundle := ⟨validated, frozen, policy, copySource, snapshotRun, binding⟩
            have boundShape : before = bound.events ++ afterBind := by
              simp only [Bound.events, bound, validatedShape, copyShape, bindShape, copyEvents,
                bindEmpty, List.nil_append, List.append_assoc]
            rcases last_checked_bind _ _ rest with revalidating |
                ⟨revalidating, value, afterValidate, revalidate, rest, revalidateShape⟩
            · exact ⟨.revalidating bound afterBind revalidating boundShape⟩
            · dsimp only at rest
              split at rest
              · exact False.elim (Program.pure_has_no_last _ _ _ rest)
              · rcases last_checked_bind _ _ rest with budgeting |
                    ⟨budgeting, final, afterBudget, budgeted, rest, budgetShape⟩
                · exact False.elim (checked_has_no_last _ _ _ budgeting)
                · split at rest <;> exact False.elim (Program.pure_has_no_last _ _ _ rest)

end LeanCage.Host.PreparationPrefixCuts
