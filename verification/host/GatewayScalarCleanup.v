(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Scalar cleanup returns the same constructor result after its actual free. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarLength GatewayScalarBytesPath
  GatewaySourceDynamic GatewaySourcePaths GatewayFramedRuntime GatewayContexts GatewayRuntimeCuts GatewayReturnIdentity
  GatewayReturns GatewayMemoryBindings GatewayNativeMemory.
Import ListNotations.

Definition gateway_scalar_return:=match gateway_scalar_cleanup with Ssequence _ returning=>returning|_=>Sskip end.
Definition gateway_scalar_free_cont slots parameters:=Kcall None f_host_value(gateway_value_environment slots)parameters
  (Kseq gateway_scalar_return(Kseq gateway_value_after_scalar Kstop)).

Theorem gateway_scalar_cleanup_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:Memory.mem->World->Prop)identifier slots parameters object returned memory symbol :
  gateway_ambient_closed backend property ->identifier<>_bytes ->parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  Genv.find_symbol ge _free=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(External EF_free[tptr tvoid]tvoid cc_default) ->
  exists called_parameters,gateway_source_path backend ge(External EF_free[tptr tvoid]tvoid cc_default)[Vptr object Ptrofs.zero]
    (gateway_scalar_free_cont slots called_parameters)property
    (Returnstate returned(gateway_scalar_constructor_cont identifier slots parameters)memory)property /\
    called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\called_parameters!_value=Some returned.
Proof.
  intros CLOSED DISTINCT BUFFER_PARAMETER SYMBOL FUNCTION.
  eexists;split.
  - gateway_source_dynamic_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    lazymatch goal with |-gateway_source_path _ _ ?definition ?values ?continuation _ _ _=>
      eapply gateway_source_same with(target:=Callstate definition values continuation memory)end.
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr object Ptrofs.zero).
        -- apply old_expression_value,value_temp;unfold set_opttemp;
             repeat rewrite PTree.gso by(first[discriminate|congruence]);exact BUFFER_PARAMETER.
        -- reflexivity.
        -- apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some(External EF_free[tptr tvoid]tvoid cc_default));exact FUNCTION.
      * reflexivity.
    + apply gateway_source_reached;auto.
  - split;unfold set_opttemp;
      [repeat rewrite PTree.gso by(first[discriminate|congruence]);exact BUFFER_PARAMETER|apply PTree.gss].
Qed.

Theorem gateway_actual_scalar_final_return {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    slots parameters selected returned before world events value after next :
  parameters!_value=Some selected ->
  gateway_steps backend ge(gateway_live(Returnstate returned(gateway_scalar_free_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=selected.
Proof.
  intros SELECTED RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (Returnstate returned(gateway_scalar_free_cont slots parameters)before)
    (State f_host_value Sskip(Kseq gateway_scalar_return(Kseq gateway_value_after_scalar Kstop))
      (gateway_value_environment slots)parameters before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)I RUN)
    as(prefix &rest &middle &current &EVENTS &AMBIENT &PREFIX &READY &REST).
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (State f_host_value Sskip(Kseq gateway_scalar_return(Kseq gateway_value_after_scalar Kstop))
      (gateway_value_environment slots)parameters middle)
    (State f_host_value gateway_scalar_return(Kseq gateway_value_after_scalar Kstop)
      (gateway_value_environment slots)parameters middle)
    middle current rest value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)I REST)
    as(pending &suffix &return_memory &return_world &REST_EVENTS &WAITING &TO_RETURN &RETURN_READY &FROM_RETURN).
  eapply(gateway_return_expression_identity backend ge f_host_value(Etempvar _value(tptr(Tstruct __object noattr)))
    (Kseq gateway_value_after_scalar Kstop)(gateway_value_environment slots)parameters return_memory return_world selected suffix value after next);
    [reflexivity| | |exact FROM_RETURN].
  - intros;apply old_expression_value,value_temp;exact SELECTED.
  - intros memory converted CAST.
    eapply(gateway_pointer_cast_identity memory(tptr(Tstruct __object noattr))(tptr(Tstruct __object noattr))selected converted);
      [eexists;reflexivity|eexists;reflexivity|exact CAST].
Qed.

Theorem gateway_actual_scalar_cleanup_cut {World Event}(backend:gateway_backend World Event)
    identifier slots parameters object before world events returned value after next :
  identifier<>_bytes ->parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate returned(gateway_scalar_constructor_cont identifier slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  value=returned /\exists called_parameters prefix freeing suffix free_before free_world free_after free_next free_value,
    events=prefix++freeing++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_value=Some returned /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(External EF_free[tptr tvoid]tvoid cc_default)[Vptr object Ptrofs.zero]Kstop free_before)free_world)
      freeing(gateway_live(Returnstate free_value Kstop free_after)free_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate free_value(gateway_scalar_free_cont slots called_parameters)free_after)free_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros DISTINCT BUFFER RUN.
  destruct(gateway_actual_memory_binding gateway_free_api)as[definition[DEFINITION[symbol[SYMBOL FUNCTION]]]].
  destruct gateway_native_memory_actual_abis as[_[FREE _]].
  rewrite FREE in DEFINITION;inversion DEFINITION;subst definition.
  destruct(gateway_scalar_cleanup_path backend(Clight.globalenv prog)(fun _ _=>True)identifier slots parameters object returned before symbol
    ltac:(unfold gateway_ambient_closed;intros;exact I)DISTINCT BUFFER SYMBOL FUNCTION)as(called_parameters &PATH &CALLED_BUFFER &SELECTED).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next I RUN)
    as(prefix &rest &free_before &free_world &EVENTS &QUIET &PREFIX &READY &FROM_FREE).
  destruct(gateway_return_cut backend(Clight.globalenv prog)(External EF_free[tptr tvoid]tvoid cc_default)[Vptr object Ptrofs.zero]
    (gateway_scalar_free_cont slots called_parameters)free_before free_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_FREE)
    as(freeing &suffix &free_value &free_after &free_next &REST_EVENTS &FREE_RUN &REST).
  split;[exact(gateway_actual_scalar_final_return backend(Clight.globalenv prog)slots called_parameters returned free_value free_after
    free_next suffix value after next SELECTED REST)|].
  exists called_parameters,prefix,freeing,suffix,free_before,free_world,free_after,free_next,free_value.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact SELECTED|]. split;assumption.
Qed.
