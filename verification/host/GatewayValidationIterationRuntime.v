(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One actual iterator call returns its own borrowed fields and native cursor. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayBuiltinValidation GatewayGraphSnapshots
  GatewayDictionaryIteration GatewayDictionaryIterationLoads GatewayValidationSlots GatewayObjectExecution
  GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads GatewayReturnScope.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationIteration.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (decimal_float : list Z -> Floats.float -> Prop) (detached : val -> mem -> World -> Prop)
    (io : Event -> option gateway_native_io) (stable : World -> block -> Z -> Prop)
    (thread_errno : World -> int) (heap_allocation : block -> Z -> Prop)
    (threads : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    (iteration : gateway_dictionary_iteration_runtime backend python objects).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (original : val) (protected : block -> Z -> Prop) (source : mem) (environment : env).
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.
Let slots saved := fun memory world => base memory world /\ gateway_validation_slot_snapshot environment saved memory world.

Lemma gateway_validation_iteration_slots_closed saved : gateway_ambient_closed backend (slots saved).
Proof.
  intros before world after next [BASE SNAPSHOT] AMBIENT; split.
  - eapply (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured original protected source environment); eassumption.
  - eapply gateway_validation_slots_ambient; [exact threads |exact BASE |exact SNAPSHOT |exact AMBIENT].
Qed.

Theorem gateway_actual_validation_iterator definition dictionary fields position key value cursor before world events result after next :
  gateway_object_api_definition gateway_api_dict_next = Some definition ->
  gateway_object_reachable captured original dictionary ->
  gateway_object_values captured dictionary = Some (gateway_dict_object fields) ->
  environment ! _position = Some (position, tlong) ->
  environment ! _key = Some (key, tptr (Tstruct __object noattr)) ->
  environment ! _value__1 = Some (value, tptr (Tstruct __object noattr)) ->
  position <> key -> position <> value -> key <> value ->
  base before world -> Mem.load Mint64 before position 0 = Some (Vlong cursor) ->
  gateway_steps backend ge
    (gateway_live (Callstate definition [dictionary; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero] Kstop before) world) events
    (gateway_live (Returnstate result Kstop after) next) ->
  (0 < length events)%nat /\ base after next /\
  ((result = Vint Int.zero /\ Mem.load Mint64 after position 0 = Some (Vlong cursor)) \/
   (result = Vint Int.one /\ exists field following_cursor,
     In field fields /\ 0 < Int64.signed following_cursor /\
     Mem.load Mint64 after position 0 = Some (Vlong following_cursor) /\
     Mem.load Mptr after key 0 = Some (gateway_dictionary_key field) /\
     Mem.load Mptr after value 0 = Some (gateway_dictionary_value field))).
Proof.
  intros DEFINITION REACHED FIELDS POSITION KEY VALUE DISTINCT_POSITION_KEY DISTINCT_POSITION_VALUE DISTINCT_KEY_VALUE BASE CURSOR RUN.
  destruct (gateway_actual_object_operation backend ge gateway_api_dict_next definition
    [dictionary; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero] (slots before)
    before world events result after next DEFINITION (gateway_validation_iteration_slots_closed before)
    (conj BASE (Mem.unchanged_on_refl _ _)) RUN)
    as (pending &suffix &called &called_world &changed &changed_world &observed &EVENTS &[CALLED SNAPSHOT] &OPERATION &PREFIX &REST).
  destruct (gateway_validation_reachable_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED REACHED) as [ROOT DESCRIPTION].
  assert (CURRENT : gateway_object_values (objects called_world) dictionary = Some (gateway_dict_object fields)).
  { rewrite (gateway_validation_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED) by exact REACHED; exact FIELDS. }
  assert (PRIVATE : gateway_object_private (objects called_world) dictionary = true).
  { apply (gateway_validation_private _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED).
    eapply gateway_graph_snapshot_forward; [exact (gateway_validation_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED) |exact REACHED]. }
  assert (CALLED_CURSOR : Mem.load Mint64 called position 0 = Some (Vlong cursor)).
  { eapply gateway_validation_saved_slot; [exact BASE |exact SNAPSHOT |exact POSITION |exact CURSOR]. }
  pose proof (gateway_validation_environment _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED) as NATIVE.
  pose proof (gateway_validation_slots _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED) as ACCESS.
  destruct (gateway_runtime_dictionary_next _ _ _ iteration called called_world dictionary fields position key value cursor result changed changed_world observed
    (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED) ROOT CURRENT PRIVATE
    (proj2 (NATIVE _ _ _ POSITION)) (proj2 (NATIVE _ _ _ KEY)) (proj2 (NATIVE _ _ _ VALUE)) CALLED_CURSOR
    (ACCESS _ _ _ POSITION) (ACCESS _ _ _ KEY) (ACCESS _ _ _ VALUE) OPERATION)
    as [borrowed [OBSERVER OUTPUT]].
  pose proof (gateway_validation_context_observer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED OBSERVER) as BORROWED.
  pose proof (gateway_validation_environment _ _ _ _ _ _ _ _ _ _ _ _ _ BORROWED) as BORROWED_NATIVE.
  pose proof (gateway_validation_slots_outside _ _ _ _ _ _ _ _ _ _ _ _ _ BORROWED) as OUTSIDE.
  assert (CHANGED : base changed changed_world).
  { eapply gateway_dictionary_outputs_context; [exact BORROWED |
      exact (proj2 (BORROWED_NATIVE _ _ _ POSITION)) |exact (proj2 (BORROWED_NATIVE _ _ _ KEY)) |
      exact (proj2 (BORROWED_NATIVE _ _ _ VALUE)) |exact (OUTSIDE _ _ _ POSITION) |
      exact (OUTSIDE _ _ _ KEY) |exact (OUTSIDE _ _ _ VALUE) |exact OUTPUT]. }
  destruct (gateway_terminal_return_scope backend ge (slots changed) result
    (gateway_validation_iteration_slots_closed changed) changed changed_world suffix result after next
    (conj CHANGED (Mem.unchanged_on_refl _ _)) REST) as [SAME [FINAL FINAL_SNAPSHOT]].
  split; [rewrite EVENTS, length_app; cbn; lia |split; [exact FINAL |]].
  inversion OUTPUT as [memory |memory after_position after_key final field following_cursor MEMBER RANGE STORE_POSITION STORE_KEY STORE_VALUE]; subst.
  - left; split; [reflexivity |].
    assert (BORROWED_CURSOR : Mem.load Mint64 changed position 0 = Some (Vlong cursor)).
    { eapply gateway_validation_saved_slot; [exact CALLED | |exact POSITION |exact CALLED_CURSOR].
      eapply gateway_validation_slots_observer; [exact CALLED |apply Mem.unchanged_on_refl |exact OBSERVER]. }
    eapply gateway_validation_saved_slot; [exact CHANGED |exact FINAL_SNAPSHOT |exact POSITION |exact BORROWED_CURSOR].
  - right; split; [reflexivity |].
    destruct (gateway_dictionary_next_output_loads fields position key value borrowed changed
      DISTINCT_POSITION_KEY DISTINCT_POSITION_VALUE DISTINCT_KEY_VALUE
      (gateway_dictionary_field_pointer_outputs _ _ _ _ _
        (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ CALLED) ROOT CURRENT) OUTPUT)
      as (actual_field &actual_cursor &ACTUAL_MEMBER &ACTUAL_RANGE &POSITION_LOAD &KEY_LOAD &VALUE_LOAD).
    exists actual_field, actual_cursor; split; [exact ACTUAL_MEMBER |split; [exact ACTUAL_RANGE |split]].
    + eapply gateway_validation_saved_slot; [exact CHANGED |exact FINAL_SNAPSHOT |exact POSITION |exact POSITION_LOAD].
    + split.
      * eapply gateway_validation_saved_slot; [exact CHANGED |exact FINAL_SNAPSHOT |exact KEY |exact KEY_LOAD].
      * eapply gateway_validation_saved_slot; [exact CHANGED |exact FINAL_SNAPSHOT |exact VALUE |exact VALUE_LOAD].
Qed.
End ValidationIteration.
