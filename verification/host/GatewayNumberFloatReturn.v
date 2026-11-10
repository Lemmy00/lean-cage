(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The float helper's final source return has no native memory
   writes or local frees, and retains the same coupled storage/reference context. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberFloatSource GatewayNumberConstruction GatewayJsonNumberSource
  GatewayPure GatewayReadonly GatewayValueReturns GatewayFramedRuntime GatewayContexts GatewaySourcePaths GatewayOperations.
Import ListNotations.

Theorem gateway_number_float_return_path ge parameters selected ignored memory:
  parameters!_value=Some selected->gateway_object_pointer_value selected->
  gateway_pure_path ge(Returnstate ignored(gateway_number_text_release_cont parameters)memory)selected.
Proof.
  intros SELECTED POINTER.
  eapply gateway_pure_next with(next:=State f_host_json_number Sskip
    (Kseq gateway_number_float_return(Kseq json_number_integer_construction Kstop))empty_env parameters memory).
  - cbn;tauto.
  - intros;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_pure_next with(next:=State f_host_json_number gateway_number_float_return
      (Kseq json_number_integer_construction Kstop)empty_env parameters memory).
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_pure_next with(next:=Returnstate selected Kstop memory).
      * cbn;tauto.
      * intros;apply unchanged_store_edge;eapply edge_return with(v:=selected).
        -- apply value_temp;exact SELECTED.
        -- destruct POINTER as[NULL|[object[offset SAME]]];subst selected;reflexivity.
      * constructor.
Qed.

Theorem gateway_number_after_float_identity {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters text returned before world events value after next symbol definition:
  parameters!_text=Some text->gateway_object_pointer_value text->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_steps backend ge(gateway_live(Returnstate returned(gateway_number_float_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=returned.
Proof.
  intros TEXT POINTER SYMBOL FUNCTION TYPE RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_number_text_release_source_path backend ge(fun _ _=>True)parameters text returned before symbol definition
    CLOSED TEXT POINTER SYMBOL FUNCTION TYPE)as(called_parameters &PATH &SELECTED &UNCHANGED).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as(prefix &rest &called &called_world &EVENTS &QUIET &PREFIX &READY &FROM_RELEASE).
  destruct(gateway_return_cut backend ge definition[text](gateway_number_text_release_cont called_parameters)
    called called_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &suffix &ignored &changed &following &REST_EVENTS &RELEASE &REST).
  exact(gateway_number_float_return_identity backend ge called_parameters returned ignored changed following suffix value after next SELECTED REST).
Qed.

Theorem gateway_number_float_return_ready {World Event}(backend:gateway_backend World Event)ge
    side(discipline:gateway_runtime_discipline backend side)parameters selected ignored before world events value after next:
  parameters!_value=Some selected->gateway_object_pointer_value selected->side before world->
  gateway_steps backend ge(gateway_live(Returnstate ignored(gateway_number_text_release_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  value=selected /\side after next /\Forall gateway_quiet_event events.
Proof.
  intros SELECTED POINTER SIDE RUN.
  eapply gateway_pure_path_ready_return;[exact discipline|eapply gateway_number_float_return_path;eassumption|exact SIDE|exact RUN].
Qed.
