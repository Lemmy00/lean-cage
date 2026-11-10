(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A DecRef consumes the actual source operand's owner place. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRegistry GatewayPython GatewayObjects GatewayReferences
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceExecution.
Import ListNotations.

Definition gateway_reference_decref_call identifier:=
  Scall None(Evar _Py_DecRef(Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default))
    [Etempvar identifier(tptr(Tstruct __object noattr))].

Lemma gateway_reference_decref_call_edge(ge:Clight.genv)function continuation environment temporaries memory
    identifier object offset symbol definition:
  environment!_Py_DecRef=None->temporaries!identifier=Some(Vptr object offset)->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  store_edge ge(State function(gateway_reference_decref_call identifier)continuation environment temporaries memory)
    (Callstate definition[Vptr object offset](Kcall None function environment temporaries continuation)memory).
Proof.
  intros UNSHADOWED VALUE SYMBOL FUNCTION TYPE.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact UNSHADOWED|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr object offset).
    + apply old_expression_value,value_temp;exact VALUE.
    + reflexivity.
    + apply no_argument_values.
  - change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
  - exact TYPE.
Qed.

Theorem gateway_reference_source_operand_move(ge:Clight.genv)function continuation environment temporaries memory
    identifier object offset symbol definition ledger ticket:
  environment!_Py_DecRef=None->temporaries!identifier=Some(Vptr object offset)->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    ticket(Vptr object offset)->
  gateway_reference_take(gateway_reference_argument(S(gateway_reference_depth continuation))0)
    (gateway_reference_entries ledger)=None->
  exists argument_ledger,
    store_edge ge(State function(gateway_reference_decref_call identifier)continuation environment temporaries memory)
      (Callstate definition[Vptr object offset](Kcall None function environment temporaries continuation)memory) /\
    gateway_reference_apply(gateway_reference_move
      (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
      (gateway_reference_argument(S(gateway_reference_depth continuation))0))
      (gateway_reference_valid ledger)=gateway_reference_valid argument_ledger /\
    gateway_reference_ledger_well_formed argument_ledger /\
    gateway_reference_owns argument_ledger(gateway_reference_argument(S(gateway_reference_depth continuation))0)
      ticket(Vptr object offset) /\
    gateway_reference_place_value ge
      (State function(gateway_reference_decref_call identifier)continuation environment temporaries memory)
      (gateway_reference_temporary(gateway_reference_depth continuation)identifier)(Vptr object offset) /\
    gateway_reference_place_value ge
      (Callstate definition[Vptr object offset](Kcall None function environment temporaries continuation)memory)
      (gateway_reference_argument(S(gateway_reference_depth continuation))0)(Vptr object offset) /\
    (forall pointer,gateway_reference_count argument_ledger pointer=gateway_reference_count ledger pointer).
Proof.
  intros UNSHADOWED VALUE SYMBOL FUNCTION TYPE FORMED OWNED VACANT.
  destruct(gateway_reference_move_selected ledger
    (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    (gateway_reference_argument(S(gateway_reference_depth continuation))0)ticket(Vptr object offset)FORMED OWNED)
    as[argument_ledger[APPLY[WELL[ARGUMENT[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    apply(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER);exact OWNER.
  - exists argument_ledger;split.
    + eapply gateway_reference_decref_call_edge;eassumption.
    + split;[exact APPLY|]. split;[exact WELL|]. split;[exact ARGUMENT|]. split.
      * apply gateway_reference_temporary_binding;exact VALUE.
      * split;[split;reflexivity|exact COUNTS].
Qed.

Theorem gateway_reference_actual_operand_release {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects(references:gateway_reference_runtime backend python objects)
    function continuation environment temporaries identifier object offset symbol definition ledger ticket
    before world result after next observed:
  environment!_Py_DecRef=None->temporaries!identifier=Some(Vptr object offset)->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  gateway_object_api_definition gateway_api_decref=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    ticket(Vptr object offset)->
  gateway_reference_take(gateway_reference_argument(S(gateway_reference_depth continuation))0)
    (gateway_reference_entries ledger)=None->
  gateway_objects_ready(python world)(objects world)before->gateway_destructible(objects world)(Vptr object offset)->
  gateway_step backend ge
    (gateway_live(Callstate definition[Vptr object offset](Kcall None function environment temporaries continuation)before)world)
    (gateway_primitive observed)
    (gateway_live(Returnstate result(Kcall None function environment temporaries continuation)after)next)->
  exists argument_ledger final,
    gateway_reference_apply(gateway_reference_move
      (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
      (gateway_reference_argument(S(gateway_reference_depth continuation))0))
      (gateway_reference_valid ledger)=gateway_reference_valid argument_ledger /\
    gateway_reference_apply(gateway_reference_release
      (gateway_reference_argument(S(gateway_reference_depth continuation))0)(Vptr object offset))
      (gateway_reference_valid argument_ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_counts_fit final(python next) /\
    (forall place other pointer,other<>ticket->gateway_reference_owns ledger place other pointer->
      gateway_reference_owns final place other pointer).
Proof.
  intros UNSHADOWED VALUE SYMBOL FUNCTION DEFINITION TYPE FORMED FIT OWNED VACANT READY DESTRUCTIBLE STEP.
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
    { unfold gateway_object_api_definition in DEFINITION.
      destruct(gateway_program_definition _Py_DecRef global_definitions)as[global|]eqn:GLOBAL;[|discriminate].
      destruct global as[callee|variable];[|discriminate].
      destruct callee as[callee|external types result_type convention];[discriminate|].
      inversion DEFINITION;subst definition.
      eapply gateway_object_operation_actual;[exact DEFINITION|exact STEP]. }
    destruct(gateway_reference_actual_decref backend python objects references argument_ledger
      (gateway_reference_argument(S(gateway_reference_depth continuation))0)ticket(Vptr object offset)
      before world result after next observed WELL ARGUMENT_FIT ARGUMENT READY DESTRUCTIBLE OPERATION)
      as[final[RELEASE[FINAL_FORMED[FINAL_FIT[EFFECT FINAL_RETAINED]]]]].
    exists argument_ledger,final;split;[exact MOVE|]. split;[exact RELEASE|].
    split;[exact FINAL_FORMED|]. split;[exact FINAL_FIT|].
    intros place other pointer DIFFERENT OLD;apply FINAL_RETAINED;[exact DIFFERENT|].
    apply RETAINED;assumption.
Qed.
