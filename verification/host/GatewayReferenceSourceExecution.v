(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source operand transfer and SDK release share the physical run. *)
From Stdlib Require Import List String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects GatewayReferences
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceExecution GatewayReferenceOperands.
Import ListNotations.

Definition gateway_reference_decref_definition:Ctypes.fundef Clight.function:=External
  (EF_external "Py_DecRef"(mksignature[Xptr]Xvoid cc_default))
  [tptr(Tstruct __object noattr)]tvoid cc_default.

Lemma gateway_reference_decref_registered:
  gateway_object_api_definition gateway_api_decref=Some gateway_reference_decref_definition.
Proof. reflexivity. Qed.

Definition gateway_reference_operand_select {World Event}:gateway_reference_selector World Event:=
  fun first event last status=>
  match event,first with
  |gateway_source _,gateway_live(State _ (Scall None(Evar callee _)[Etempvar identifier _])continuation _ _ _)_=>
    if Pos.eqb callee _Py_DecRef then
      gateway_reference_move(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
        (gateway_reference_argument(S(gateway_reference_depth continuation))0)
    else gateway_reference_unclassified
  |gateway_primitive _,gateway_live(Callstate(External(EF_external name _) _ _ _)[pointer]continuation _)_
  |gateway_committed_lost _,gateway_live(Callstate(External(EF_external name _) _ _ _)[pointer]continuation _)_=>
    if String.eqb name "Py_DecRef" then
      gateway_reference_release(gateway_reference_argument(gateway_reference_depth continuation)0)pointer
    else gateway_reference_unclassified
  |gateway_source _,gateway_live(Returnstate _ (Kcall None _ _ _ _)_)_=>gateway_reference_keep
  |gateway_source _,gateway_live(State _ Sskip _ _ _ _)_=>gateway_reference_keep
  |gateway_ambient,_|gateway_blocked,_|gateway_lost,_=>gateway_reference_keep
  |_,_=>gateway_reference_unclassified
  end.

Theorem gateway_reference_actual_operand_slice {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects(references:gateway_reference_runtime backend python objects)
    function continuation environment temporaries identifier object offset ledger ticket
    before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    ticket(Vptr object offset)->
  gateway_reference_take(gateway_reference_argument(S(gateway_reference_depth continuation))0)
    (gateway_reference_entries ledger)=None->
  gateway_objects_ready(python world)(objects world)before->gateway_destructible(objects world)(Vptr object offset)->
  gateway_step backend ge
    (gateway_live(State function(gateway_reference_decref_call identifier)continuation environment temporaries before)world)
    (gateway_source E0)
    (gateway_live(Callstate gateway_reference_decref_definition[Vptr object offset]
      (Kcall None function environment temporaries continuation)before)world)->
  gateway_step backend ge
    (gateway_live(Callstate gateway_reference_decref_definition[Vptr object offset]
      (Kcall None function environment temporaries continuation)before)world)
    (gateway_primitive observed)
    (gateway_live(Returnstate result(Kcall None function environment temporaries continuation)after)next)->
  exists final,
    gateway_reference_execution backend ge gateway_reference_operand_select
      (gateway_live(State function(gateway_reference_decref_call identifier)continuation environment temporaries before)world)
      (gateway_reference_valid ledger)[gateway_source E0;gateway_primitive observed]
      (gateway_live(Returnstate result(Kcall None function environment temporaries continuation)after)next)
      (gateway_reference_valid final) /\
    gateway_reference_ledger_well_formed final /\gateway_reference_counts_fit final(python next) /\
    (forall place other pointer,other<>ticket->gateway_reference_owns ledger place other pointer->
      gateway_reference_owns final place other pointer).
Proof.
  intros FORMED FIT OWNED VACANT READY DESTRUCTIBLE SOURCE PRIMITIVE.
  destruct(gateway_reference_move_selected ledger
    (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    (gateway_reference_argument(S(gateway_reference_depth continuation))0)ticket(Vptr object offset)FORMED OWNED)
    as[argument_ledger[MOVE[WELL[ARGUMENT[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    apply(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER);exact OWNER.
  - assert(ARGUMENT_FIT:gateway_reference_counts_fit argument_ledger(python world)).
    { intro pointer;rewrite COUNTS;apply FIT. }
    assert(OPERATION:gateway_object_operation backend gateway_api_decref[Vptr object offset]
      before world result after next observed).
    { eapply gateway_object_operation_actual;[exact gateway_reference_decref_registered|exact PRIMITIVE]. }
    destruct(gateway_reference_actual_decref backend python objects references argument_ledger
      (gateway_reference_argument(S(gateway_reference_depth continuation))0)ticket(Vptr object offset)
      before world result after next observed WELL ARGUMENT_FIT ARGUMENT READY DESTRUCTIBLE OPERATION)
      as[final[RELEASE[FINAL_FORMED[FINAL_FIT[EFFECT FINAL_RETAINED]]]]].
    exists final;split.
    + econstructor;[exact SOURCE|].
      change(gateway_reference_execution backend ge gateway_reference_operand_select
        (gateway_live(Callstate gateway_reference_decref_definition[Vptr object offset]
          (Kcall None function environment temporaries continuation)before)world)
        (gateway_reference_apply(gateway_reference_move
          (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
          (gateway_reference_argument(S(gateway_reference_depth continuation))0))(gateway_reference_valid ledger))
        [gateway_primitive observed]
        (gateway_live(Returnstate result(Kcall None function environment temporaries continuation)after)next)
        (gateway_reference_valid final)).
      rewrite MOVE;econstructor;[exact PRIMITIVE|].
      change(gateway_reference_execution backend ge gateway_reference_operand_select
        (gateway_live(Returnstate result(Kcall None function environment temporaries continuation)after)next)
        (gateway_reference_apply(gateway_reference_release
          (gateway_reference_argument(S(gateway_reference_depth continuation))0)(Vptr object offset))
          (gateway_reference_valid argument_ledger))[]
        (gateway_live(Returnstate result(Kcall None function environment temporaries continuation)after)next)
        (gateway_reference_valid final)).
      rewrite RELEASE;constructor.
    + split;[exact FINAL_FORMED|]. split;[exact FINAL_FIT|].
      intros place other pointer DIFFERENT OLD;apply FINAL_RETAINED;[exact DIFFERENT|].
      apply RETAINED;assumption.
Qed.

Theorem gateway_reference_operand_all_prefixes {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    first events last status:
  gateway_steps backend ge first events last->
  exists final,gateway_reference_execution backend ge gateway_reference_operand_select first status events last final.
Proof. intro PHYSICAL;eapply gateway_reference_execution_covers;exact PHYSICAL. Qed.
