(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A new key credit follows the real SDK return and source assignment. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeGetterSource GatewayRuntimeCuts
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceFrames GatewayReferenceExecution
  GatewayReferencePlaces GatewayFramedRuntime.
Import ListNotations.

Definition gateway_observation_key_return_tail:=
  Kseq(Sset _key(Etempvar _t'1(tptr(Tstruct __object noattr))))(Kseq gateway_observation_key_tail Kstop).
Definition gateway_observation_returned_key_parameters (parameters:temp_env) (key:Values.val):=PTree.set _t'1 key parameters.
Definition gateway_observation_stored_key_parameters parameters key:=
  PTree.set _key key(gateway_observation_returned_key_parameters parameters key).

Theorem gateway_actual_observation_key_storage {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters key before world events value after next ledger ticket:
  gateway_ambient_closed backend property->property before world->
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger(gateway_reference_result 1)ticket key->
  gateway_reference_take(gateway_reference_temporary 0 _t'1)(gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_temporary 0 _key)(gateway_reference_entries ledger)=None->
  gateway_steps backend ge(gateway_live(Returnstate key(gateway_observation_key_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists returned stored prefix pending waiting suffix first first_world second second_world third third_world,
    events=prefix++gateway_source E0::pending++gateway_source E0::waiting++gateway_source E0::suffix /\
    Forall(fun event=>event=gateway_ambient)prefix /\
    Forall(fun event=>event=gateway_ambient)pending /\
    Forall(fun event=>event=gateway_ambient)waiting /\
    gateway_steps backend ge(gateway_live(Returnstate key(gateway_observation_key_cont parameters)before)world)prefix
      (gateway_live(Returnstate key(gateway_observation_key_cont parameters)first)first_world) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_observation Sskip gateway_observation_key_return_tail empty_env
        (gateway_observation_returned_key_parameters parameters key)first)first_world)pending
      (gateway_live(State f_host_outcome_observation Sskip gateway_observation_key_return_tail empty_env
        (gateway_observation_returned_key_parameters parameters key)second)second_world) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_observation(Sset _key(Etempvar _t'1(tptr(Tstruct __object noattr))))
        (Kseq gateway_observation_key_tail Kstop)empty_env(gateway_observation_returned_key_parameters parameters key)second)second_world)waiting
      (gateway_live(State f_host_outcome_observation(Sset _key(Etempvar _t'1(tptr(Tstruct __object noattr))))
        (Kseq gateway_observation_key_tail Kstop)empty_env(gateway_observation_returned_key_parameters parameters key)third)third_world) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_observation Sskip(Kseq gateway_observation_key_tail Kstop)empty_env
        (gateway_observation_stored_key_parameters parameters key)third)third_world)suffix
      (gateway_live(Returnstate value Kstop after)next) /\property third third_world /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(Returnstate key(gateway_observation_key_cont parameters)first)first_world)
      (gateway_reference_valid ledger)[gateway_source E0]
      (gateway_live(State f_host_outcome_observation Sskip gateway_observation_key_return_tail empty_env
        (gateway_observation_returned_key_parameters parameters key)first)first_world)(gateway_reference_valid returned) /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(State f_host_outcome_observation(Sset _key(Etempvar _t'1(tptr(Tstruct __object noattr))))
        (Kseq gateway_observation_key_tail Kstop)empty_env(gateway_observation_returned_key_parameters parameters key)third)third_world)
      (gateway_reference_valid returned)[gateway_source E0]
      (gateway_live(State f_host_outcome_observation Sskip(Kseq gateway_observation_key_tail Kstop)empty_env
        (gateway_observation_stored_key_parameters parameters key)third)third_world)(gateway_reference_valid stored) /\
    gateway_reference_ledger_well_formed stored /\gateway_reference_owns stored(gateway_reference_temporary 0 _key)ticket key /\
    (forall pointer,gateway_reference_count stored pointer=gateway_reference_count ledger pointer).
Proof.
  intros CLOSED INPUT WELL OWNED RETURN_VACANT KEY_VACANT RUN.
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (Returnstate key(gateway_observation_key_cont parameters)before)
    (State f_host_outcome_observation Sskip gateway_observation_key_return_tail empty_env
      (gateway_observation_returned_key_parameters parameters key)before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)INPUT RUN)
    as(prefix &rest &first &first_world &EVENTS &AMBIENT &PREFIX &FIRST &REST).
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (State f_host_outcome_observation Sskip gateway_observation_key_return_tail empty_env
      (gateway_observation_returned_key_parameters parameters key)first)
    (State f_host_outcome_observation(Sset _key(Etempvar _t'1(tptr(Tstruct __object noattr))))
      (Kseq gateway_observation_key_tail Kstop)empty_env(gateway_observation_returned_key_parameters parameters key)first)
    first first_world rest value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)FIRST REST)
    as(pending &later &second &second_world &REST_EVENTS &PENDING &PENDING_RUN &SECOND &LATER).
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (State f_host_outcome_observation(Sset _key(Etempvar _t'1(tptr(Tstruct __object noattr))))
      (Kseq gateway_observation_key_tail Kstop)empty_env(gateway_observation_returned_key_parameters parameters key)second)
    (State f_host_outcome_observation Sskip(Kseq gateway_observation_key_tail Kstop)empty_env
      (gateway_observation_stored_key_parameters parameters key)second)
    second second_world later value after next ltac:(cbn;tauto)
    ltac:(intros;apply certified_set_edge,old_expression_value,value_temp,PTree.gss)SECOND LATER)
    as(waiting &suffix &third &third_world &LATER_EVENTS &WAITING &WAITING_RUN &THIRD &SUFFIX).
  destruct(gateway_reference_returned_owner backend ge f_host_outcome_observation _t'1 empty_env parameters
    gateway_observation_key_return_tail key first first_world ledger ticket WELL OWNED RETURN_VACANT)
    as(returned &RETURN_EXECUTION &RETURNED_WELL &RETURNED_OWNER &RETURNED_BINDING &RETURN_COUNTS).
  assert(RETURN_MOVE:gateway_reference_apply(gateway_reference_move(gateway_reference_result 1)
    (gateway_reference_temporary 0 _t'1))(gateway_reference_valid ledger)=gateway_reference_valid returned).
  { inversion RETURN_EXECUTION as[|a b c d e f g HEAD TAIL];subst.
    inversion TAIL;reflexivity. }
  assert(STORED_VACANT:gateway_reference_take(gateway_reference_temporary 0 _key)(gateway_reference_entries returned)=None).
  { eapply(gateway_reference_move_keeps_vacant ledger(gateway_reference_result 1)
      (gateway_reference_temporary 0 _t'1)(gateway_reference_temporary 0 _key)returned);
      [exact KEY_VACANT|discriminate|exact RETURN_MOVE]. }
  assert(ASSIGN:gateway_step backend ge
    (gateway_live(State f_host_outcome_observation(Sset _key(Etempvar _t'1(tptr(Tstruct __object noattr))))
      (Kseq gateway_observation_key_tail Kstop)empty_env(gateway_observation_returned_key_parameters parameters key)third)third_world)
    (gateway_source E0)
    (gateway_live(State f_host_outcome_observation Sskip(Kseq gateway_observation_key_tail Kstop)empty_env
      (gateway_observation_stored_key_parameters parameters key)third)third_world)).
  { apply gateway_internal;[exact I|]. apply step_set.
    constructor;apply PTree.gss. }
  destruct(gateway_reference_assigned_owner backend ge f_host_outcome_observation _key _t'1
    (Etempvar _t'1(tptr(Tstruct __object noattr)))(Kseq gateway_observation_key_tail Kstop)empty_env
    (gateway_observation_returned_key_parameters parameters key)key third third_world third returned ticket
    eq_refl RETURNED_WELL RETURNED_OWNER STORED_VACANT ASSIGN)
    as(stored &STORE_EXECUTION &STORED_WELL &STORED_OWNER &STORED_BINDING &STORE_COUNTS).
  exists returned,stored,prefix,pending,waiting,suffix,first,first_world,second,second_world,third,third_world.
  split;[rewrite EVENTS,REST_EVENTS,LATER_EVENTS;reflexivity|].
  split;[exact AMBIENT|]. split;[exact PENDING|]. split;[exact WAITING|].
  split;[exact PREFIX|]. split;[exact PENDING_RUN|]. split;[exact WAITING_RUN|].
  split;[exact SUFFIX|]. split;[exact THIRD|]. split;[exact RETURN_EXECUTION|].
  split;[exact STORE_EXECUTION|]. split;[exact STORED_WELL|]. split;[exact STORED_OWNER|].
  intro pointer;rewrite STORE_COUNTS,RETURN_COUNTS;reflexivity.
Qed.
