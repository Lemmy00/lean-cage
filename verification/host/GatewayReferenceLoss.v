(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A committed release with a lost return consumes only its actual operand. *)
From Stdlib Require Import List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects GatewayReferences
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceExecution
  GatewayReferenceOperands GatewayReferenceSourceExecution.
Import ListNotations.

Theorem gateway_reference_operand_committed_loss {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects(references:gateway_reference_runtime backend python objects)
    function continuation environment temporaries identifier object offset ledger ticket
    before world after next observed:
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
    (gateway_committed_lost observed)(gateway_dead after next)->
  exists final,
    gateway_reference_execution backend ge gateway_reference_operand_select
      (gateway_live(State function(gateway_reference_decref_call identifier)continuation environment temporaries before)world)
      (gateway_reference_valid ledger)[gateway_source E0;gateway_committed_lost observed]
      (gateway_dead after next)(gateway_reference_valid final) /\
    gateway_reference_ledger_well_formed final /\gateway_reference_counts_fit final(python next) /\
    (forall place other pointer,other<>ticket->gateway_reference_owns ledger place other pointer->
      gateway_reference_owns final place other pointer).
Proof.
  intros FORMED FIT OWNED VACANT READY DESTRUCTIBLE SOURCE LOST.
  destruct(gateway_reference_move_selected ledger
    (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    (gateway_reference_argument(S(gateway_reference_depth continuation))0)ticket(Vptr object offset)FORMED OWNED)
    as[argument_ledger[MOVE[WELL[ARGUMENT[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    apply(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER);exact OWNER.
  - assert(ARGUMENT_FIT:gateway_reference_counts_fit argument_ledger(python world)).
    { intro pointer;rewrite COUNTS;apply FIT. }
    assert(OPERATION:exists returned,gateway_object_operation backend gateway_api_decref[Vptr object offset]
      before world returned after next observed).
    { inversion LOST;subst.
      match goal with REAL:gateway_external _ _ _ _ _ _ _ _ ?returned _ _ _|-_=>
        exists returned;eexists;split;[exact gateway_reference_decref_registered|exact REAL]end. }
    destruct OPERATION as[returned OPERATION].
    destruct(gateway_reference_actual_decref backend python objects references argument_ledger
      (gateway_reference_argument(S(gateway_reference_depth continuation))0)ticket(Vptr object offset)
      before world returned after next observed WELL ARGUMENT_FIT ARGUMENT READY DESTRUCTIBLE OPERATION)
      as[final[RELEASE[FINAL_FORMED[FINAL_FIT[EFFECT FINAL_RETAINED]]]]].
    exists final;split.
    + econstructor;[exact SOURCE|].
      change(gateway_reference_execution backend ge gateway_reference_operand_select
        (gateway_live(Callstate gateway_reference_decref_definition[Vptr object offset]
          (Kcall None function environment temporaries continuation)before)world)
        (gateway_reference_apply(gateway_reference_move
          (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
          (gateway_reference_argument(S(gateway_reference_depth continuation))0))(gateway_reference_valid ledger))
        [gateway_committed_lost observed](gateway_dead after next)(gateway_reference_valid final)).
      rewrite MOVE;econstructor;[exact LOST|].
      change(gateway_reference_execution backend ge gateway_reference_operand_select(gateway_dead after next)
        (gateway_reference_apply(gateway_reference_release
          (gateway_reference_argument(S(gateway_reference_depth continuation))0)(Vptr object offset))
          (gateway_reference_valid argument_ledger))[](gateway_dead after next)(gateway_reference_valid final)).
      rewrite RELEASE;constructor.
    + split;[exact FINAL_FORMED|]. split;[exact FINAL_FIT|].
      intros place other pointer DIFFERENT OLD;apply FINAL_RETAINED;[exact DIFFERENT|].
      apply RETAINED;assumption.
Qed.
