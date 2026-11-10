(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful append reaches the real selected child release and
   returns to the same bounded source loop. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayContainerLoopSource
  GatewayContainerArraySource GatewayContainerArrayStatus GatewaySourceDynamic GatewaySourcePaths
  GatewaySourceSegments GatewayFramedRuntime GatewayNumber.
Import ListNotations.

Lemma gateway_container_append_release_owned_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters status child child_offset memory symbol definition:
  gateway_ambient_closed backend property->parameters!_first=Some(Vptr child child_offset)->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists called_parameters,gateway_source_path backend ge definition[Vptr child child_offset]
    (gateway_container_array_release_cont slots called_parameters)property
    (Returnstate(Vint status)(gateway_container_append_cont slots parameters)memory)property /\
    called_parameters!_result=Some(Vint status) /\
    called_parameters!_container=parameters!_container /\called_parameters!_first=parameters!_first /\
    called_parameters!_stream=parameters!_stream /\called_parameters!_depth=parameters!_depth /\
    called_parameters!_index__1=parameters!_index__1.
Proof.
  intros CLOSED CHILD SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_source_dynamic_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr child child_offset]
      (gateway_container_array_release_cont slots _)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr child child_offset).
        -- gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|reflexivity].
Qed.

Definition gateway_array_next_parameters index parameters:=PTree.set _index__1(Vlong(Int64.add index Int64.one))parameters.

Ltac gateway_array_next_segment closed :=
  tryif solve[apply gateway_segment_here]then idtac else(
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (Returnstate ?returned ?saved ?memory) _ _=>
    let call:=eval hnf in saved in lazymatch call with
    |Kcall ?destination ?function ?environment ?parameters ?continuation=>
      eapply gateway_segment_same with(next:=State function Sskip continuation environment(set_opttemp destination returned parameters)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|gateway_array_next_segment closed]
    end
  | |-gateway_source_segment _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory) _ _=>
    let statement:=eval hnf in body in lazymatch statement with
    |Ssequence ?first ?rest=>eapply gateway_segment_same with(next:=State function first(Kseq rest continuation)environment parameters memory);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|gateway_array_next_segment closed]
    |Sskip=>lazymatch continuation with
      |Kseq ?following ?rest=>eapply gateway_segment_same with(next:=State function following rest environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|gateway_array_next_segment closed]
      |Kloop1 ?body ?increment ?rest=>eapply gateway_segment_same with(next:=State function increment(Kloop2 body increment rest)environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop1|gateway_array_next_segment closed]
      |Kloop2 ?body ?increment ?rest=>eapply gateway_segment_same with(next:=State function(Sloop body increment)rest environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|gateway_array_next_segment closed]
      end
    |_=>idtac
    end
  end).

Theorem gateway_container_array_next_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters released index memory:
  gateway_ambient_closed backend property->parameters!_result=Some(Vint Int.zero)->
  parameters!_index__1=Some(Vlong index)->
  gateway_source_segment backend ge property
    (Returnstate released(gateway_container_array_release_cont slots parameters)memory)
    (State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)
      (gateway_array_next_parameters index parameters)memory)property.
Proof.
  intros CLOSED STATUS INDEX.
  gateway_array_next_segment CLOSED.
  eapply gateway_segment_same with(next:=State f_host_value Sskip
    (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)
    (gateway_value_environment slots)parameters memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(b:=false).
    + apply old_expression_value,value_temp;exact STATUS.
    + reflexivity.
  - gateway_array_next_segment CLOSED.
    eapply gateway_segment_same with(next:=State f_host_value Sskip
      (Kloop2 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)
      (gateway_value_environment slots)(gateway_array_next_parameters index parameters)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;apply certified_set_edge.
      eapply binary_expression_value with(v:=Vlong index)(w:=Vint Int.one).
      * apply old_expression_value,value_temp;exact INDEX.
      * apply old_expression_value;constructor.
      * change (Some(Vlong(Int64.add index(Int64.repr(Int.signed Int.one))))=
          Some(Vlong(Int64.add index Int64.one)));reflexivity.
    + gateway_array_next_segment CLOSED.
Qed.
