(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The selected zero-tag source run contains its real reference operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFrames GatewayValueEntry GatewayValueTag
  GatewayValueNull GatewaySourcePaths GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_null_reference {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots arguments initial before world events value after next
    none_symbol reference_symbol definition :
  gateway_ambient_closed backend property ->
  (forall memory current,property memory current->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong Int64.zero)) ->
  Genv.find_symbol ge __Py_NoneStruct=Some none_symbol ->Genv.find_symbol ge _Py_IncRef=Some reference_symbol ->
  Genv.find_funct_ptr ge reference_symbol=Some definition ->
  type_of_fundef definition=Tfunction[Ctypesdefs.tptr(Tstruct __object noattr)]Ctypesdefs.tvoid cc_default ->
  property before world ->
  gateway_steps backend ge(gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->
  exists prefix reference suffix called called_world result returned returned_world,
    events=prefix++reference++suffix /\value=Vptr none_symbol Ptrofs.zero /\
    Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)prefix
      (gateway_live(Callstate definition[Vptr none_symbol Ptrofs.zero](gateway_value_none_cont slots arguments initial)called)
        called_world) /\property called called_world /\
    gateway_steps backend ge(gateway_live(Callstate definition[Vptr none_symbol Ptrofs.zero]Kstop called)called_world)
      reference(gateway_live(Returnstate result Kstop returned)returned_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate result(gateway_value_none_cont slots arguments initial)returned)returned_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED LOADED NONE_SYMBOL REFERENCE_SYMBOL FUNCTION TYPE GOOD RUN.
  pose proof(gateway_value_zero_tag_path backend ge property slots arguments initial before none_symbol reference_symbol definition
    CLOSED LOADED NONE_SYMBOL REFERENCE_SYMBOL FUNCTION TYPE)as PATH.
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next GOOD RUN)
    as(prefix &rest &called &called_world &EVENTS &QUIET &TO_CALL &CALL_READY &FROM_CALL).
  destruct(gateway_return_cut backend ge definition[Vptr none_symbol Ptrofs.zero]
    (gateway_value_none_cont slots arguments initial)called called_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_CALL)
    as(reference &suffix &result &returned &returned_world &REFERENCE_EVENTS &REFERENCE &REST).
  assert(VALUE:value=Vptr none_symbol Ptrofs.zero).
  { eapply gateway_value_none_returned;[exact NONE_SYMBOL|exact REST]. }
  exists prefix,reference,suffix,called,called_world,result,returned,returned_world.
  split;[rewrite EVENTS,REFERENCE_EVENTS;reflexivity|]. split;[exact VALUE|].
  split;[exact QUIET|]. split;[exact TO_CALL|]. split;[exact CALL_READY|]. split;assumption.
Qed.
