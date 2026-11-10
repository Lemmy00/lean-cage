import CallerProofs
import PrefixOrigins

namespace LeanCage.Host.CallerPrefixCuts
open Filesystem ApplicationProofs

structure Selected (request : GatewayWire.Request) where
  bundle : Validation.Bundle
  selecting : List (Request × Reply)
  valid : request.valid = true
  select : Returns (Validation.loadBundle (request.field GatewayWire.bundleSlot).bytes)
    selecting (.ok bundle)

def Selected.events {request} (context : Selected request) :=
  context.selecting.map Program.filesystemEvent

structure CheckedBundle (request : GatewayWire.Request) where
  selected : Selected request
  checking : List (Request × Reply)
  check : Returns (Validation.checkBundle selected.bundle) checking (.ok ())

def CheckedBundle.events {request} (context : CheckedBundle request) :=
  context.selected.events ++ context.checking.map Program.filesystemEvent

structure Identified (request : GatewayWire.Request) where
  checked : CheckedBundle request
  identifying : List (Request × Reply)
  identify : Returns (Validation.checkEngineIdentity checked.selected.bundle) identifying (.ok ())

def Identified.events {request} (context : Identified request) :=
  context.checked.events ++ context.identifying.map Program.filesystemEvent

structure Authenticated (request : GatewayWire.Request) where
  identified : Identified request
  key : ByteArray
  authenticating : List (Request × Reply)
  authenticate : Returns (Publication.authenticationKey identified.checked.selected.bundle)
    authenticating (.ok key)

def Authenticated.bundle {request} (context : Authenticated request) :=
  context.identified.checked.selected.bundle
def Authenticated.events {request} (context : Authenticated request) :=
  context.identified.events ++ context.authenticating.map Program.filesystemEvent

def keyGate (bundle : Validation.Bundle) : Filesystem.Program (Filesystem.Result Unit) := do
  let key ← Publication.authenticationKey bundle
  return key.map (fun _ => ())

-- §FS-host-boundary.caller: Every selected active command retains the actual bootstrap gates.
inductive Cut (request : GatewayWire.Request) (duration : Option Nat)
    (before : List Program.Event) (event : Program.Event) : Type 1 where
  | selecting (active : Program.Prefix (Program.liftFilesystem
      (Validation.loadBundle (request.field GatewayWire.bundleSlot).bytes)) (before ++ [event]))
  | checking (context : Selected request) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (Validation.checkBundle context.bundle))
        (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | identifying (context : CheckedBundle request) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem
        (Validation.checkEngineIdentity context.selected.bundle)) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | authenticating (context : Identified request) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (keyGate context.checked.selected.bundle))
        (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | loadingPolicy (context : Authenticated request) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (Validation.loadPolicy request)) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | validating (context : Authenticated request) (raw : ByteArray)
      (loading : List (Request × Reply))
      (load : Returns (Validation.loadPolicy request) loading (.ok raw)) (inside : List Program.Event)
      (active : Program.Prefix (Validation.validateCopied context.bundle raw) (inside ++ [event]))
      (trace : before = context.events ++ loading.map Program.filesystemEvent ++ inside)
  | executing (context : Authenticated request) (inside : List Program.Event)
      (command : request.command = GatewayWire.runCommand ∨ request.command = GatewayWire.checkCommand)
      (active : Program.Prefix (executeRun request context.bundle duration).run (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | retrieving (context : Authenticated request) (inside : List Program.Event)
      (command : request.command = GatewayWire.reportCommand)
      (active : Program.Prefix (Program.liftFilesystem (Retrieval.report request context.bundle))
        (inside ++ [event]))
      (trace : before = context.events ++ inside)

-- §FS-host-boundary.acceptance: Invalid input cannot reach an operation in any command branch.
theorem execute_checked_cut (request : GatewayWire.Request) (duration : Option Nat)
    {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix (executeChecked request duration).run (before ++ [event])) :
    Nonempty (Cut request duration before event) := by
  unfold executeChecked at active
  rcases last_checked_bind _ _ active with guarding |
      ⟨guarding, guarded, afterGuard, guard, rest, guardShape⟩
  · unfold checkRequest at guarding
    split at guarding <;> exact False.elim (Program.pure_has_no_last _ _ _ guarding)
  · cases guarded
    obtain ⟨valid, _, rfl⟩ := check_request_source request guard
    simp only [List.nil_append] at guardShape
    subst afterGuard
    rcases last_checked_bind _ _ rest with selecting |
        ⟨selecting, bundle, afterSelect, select, rest, selectShape⟩
    · exact ⟨.selecting selecting⟩
    · obtain ⟨selectSource, selectRun, selectEvents⟩ := filesystem_source _ select
      let selected : Selected request := ⟨bundle, selectSource, valid, selectRun⟩
      have selectedShape : before = selected.events ++ afterSelect := by
        simp only [Selected.events, selected, selectShape, selectEvents]
      rcases last_checked_bind _ _ rest with checking |
          ⟨checking, checkedValue, afterCheck, check, rest, checkShape⟩
      · exact ⟨.checking selected afterSelect checking selectedShape⟩
      · cases checkedValue
        obtain ⟨checkSource, checkRun, checkEvents⟩ := filesystem_source _ check
        let checked : CheckedBundle request := ⟨selected, checkSource, checkRun⟩
        have checkedShape : before = checked.events ++ afterCheck := by
          simp only [CheckedBundle.events, checked, selectedShape, checkShape, checkEvents, List.append_assoc]
        rcases last_checked_bind _ _ rest with identifying |
            ⟨identifying, identifiedValue, afterIdentify, identify, rest, identifyShape⟩
        · exact ⟨.identifying checked afterCheck identifying checkedShape⟩
        · cases identifiedValue
          obtain ⟨identifySource, identifyRun, identifyEvents⟩ := filesystem_source _ identify
          let identified : Identified request := ⟨checked, identifySource, identifyRun⟩
          have identifiedShape : before = identified.events ++ afterIdentify := by
            simp only [Identified.events, identified, checkedShape, identifyShape, identifyEvents, List.append_assoc]
          rcases last_checked_bind _ _ rest with authenticating |
              ⟨authenticating, authenticatedValue, afterAuthenticate, authenticate, rest, authenticateShape⟩
          · exact ⟨.authenticating identified afterIdentify authenticating identifiedShape⟩
          · cases authenticatedValue
            obtain ⟨keySource, keyRun, keyEvents⟩ := filesystem_source _ authenticate
            obtain ⟨key, keyRun⟩ := CallerProofs.key_gate_source bundle keyRun
            let authenticated : Authenticated request := ⟨identified, key, keySource, keyRun⟩
            have authenticatedShape : before = authenticated.events ++ afterAuthenticate := by
              simp only [Authenticated.events, authenticated, identifiedShape, authenticateShape,
                keyEvents, List.append_assoc]
            split at rest
            · exact False.elim (Program.pure_has_no_last _ _ _ rest)
            · split at rest
              · rcases last_checked_bind _ _ rest with loading |
                    ⟨loading, raw, afterLoad, load, rest, loadShape⟩
                · exact ⟨.loadingPolicy authenticated afterAuthenticate loading authenticatedShape⟩
                · obtain ⟨loadSource, loadRun, loadEvents⟩ := filesystem_source _ load
                  rcases last_checked_bind _ _ rest with validating |
                      ⟨validating, value, afterValidate, validate, last, validateShape⟩
                  · exact ⟨.validating authenticated raw loadSource loadRun afterLoad validating (by
                      simp only [authenticatedShape, loadShape, loadEvents, List.append_assoc])⟩
                  · exact False.elim (Program.pure_has_no_last _ _ _ last)
              · split at rest
                · rename_i command
                  have command : request.command = GatewayWire.runCommand ∨
                      request.command = GatewayWire.checkCommand := by simpa [Bool.or_eq_true] using command
                  exact ⟨.executing authenticated afterAuthenticate command rest authenticatedShape⟩
                · split at rest
                  · rename_i command
                    exact ⟨.retrieving authenticated afterAuthenticate (by simpa using command)
                      rest authenticatedShape⟩
                  · exact False.elim (Program.pure_has_no_last _ _ _ rest)

end LeanCage.Host.CallerPrefixCuts
