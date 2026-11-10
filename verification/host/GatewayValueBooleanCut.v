(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Boolean construction comes from the same actual tag dispatch. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayValueTag
  GatewayValueNull GatewayValueDispatch GatewayValueBoolean GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_boolean_call {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:Memory.mem->World->Prop)flag slots arguments initial before world events value after next symbol definition :
  gateway_ambient_closed backend property ->
  (forall memory current,property memory current ->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(gateway_value_boolean_tag flag))) ->
  Genv.find_symbol ge _PyBool_FromLong=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tlong](tptr(Tstruct __object noattr))cc_default ->property before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  exists prefix reference suffix called called_world result returned returned_world,
    events=prefix++reference++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)prefix
      (gateway_live(Callstate definition[gateway_value_boolean_argument flag]
        (gateway_value_boolean_cont flag slots arguments initial)called)called_world) /\property called called_world /\
    gateway_steps backend ge(gateway_live(Callstate definition[gateway_value_boolean_argument flag]Kstop called)called_world)
      reference(gateway_live(Returnstate result Kstop returned)returned_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate result(gateway_value_boolean_cont flag slots arguments initial)returned)returned_world)
      suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED LOADED SYMBOL FUNCTION TYPE GOOD RUN.
  assert(NONZERO:gateway_value_boolean_tag flag<>Int64.zero)by(destruct flag;discriminate).
  assert(PATH:gateway_source_path backend ge definition[gateway_value_boolean_argument flag]
    (gateway_value_boolean_cont flag slots arguments initial)property
    (Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)property).
  { eapply gateway_segment_then_call.
    - exact(gateway_value_nonzero_tag_segment backend ge property slots arguments initial before
        (gateway_value_boolean_tag flag)CLOSED NONZERO LOADED).
    - exact(gateway_value_boolean_call_path backend ge property flag slots arguments initial before symbol definition
        CLOSED LOADED SYMBOL FUNCTION TYPE). }
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next GOOD RUN)
    as(prefix &rest &called &called_world &EVENTS &QUIET &PREFIX &READY &FROM_CALL).
  destruct(gateway_return_cut backend ge definition[gateway_value_boolean_argument flag]
    (gateway_value_boolean_cont flag slots arguments initial)called called_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_CALL)
    as(reference &suffix &result &returned &returned_world &REST_EVENTS &REFERENCE &REST).
  exists prefix,reference,suffix,called,called_world,result,returned,returned_world.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact PREFIX|].
  split;[exact READY|]. split;assumption.
Qed.
