(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The owned constructor result reaches its actual zero-index loop. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContainerAllocation GatewayContainerLoopSource GatewayValueEntry
  GatewaySourceDynamic GatewaySourceSegments GatewayFramedRuntime GatewayUnaryExpressions.

Definition gateway_container_setup_parameters container object offset parameters:=
  PTree.set _index__1(Vlong Int64.zero)(PTree.set _container(Vptr object offset)
    (PTree.set _t'29(Vptr object offset)
      (set_opttemp(Some(gateway_container_constructor_destination container))(Vptr object offset)parameters))).

Ltac gateway_container_setup_source closed pointer :=
  tryif solve[apply gateway_segment_here]then idtac else(
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (Returnstate ?value ?saved ?memory) _ _=>
    let call:=eval hnf in saved in lazymatch call with
    |Kcall ?destination ?function ?environment ?parameters ?continuation=>
      eapply gateway_segment_same with(next:=State function Sskip continuation environment(set_opttemp destination value parameters)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|gateway_container_setup_source closed pointer]
    end
  | |-gateway_source_segment _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory) _ _=>
    let statement:=eval hnf in body in lazymatch statement with
    |Ssequence ?first ?rest=>eapply gateway_segment_same with(next:=State function first(Kseq rest continuation)environment parameters memory);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|gateway_container_setup_source closed pointer]
    |Sskip=>lazymatch continuation with
      |Kseq ?following ?rest=>eapply gateway_segment_same with(next:=State function following rest environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|gateway_container_setup_source closed pointer]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_segment_same with(next:=State function Sskip continuation environment(PTree.set identifier result parameters)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;
          gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|gateway_container_setup_source closed pointer]
    |Sifthenelse ?expression ?yes ?no=>
      eapply gateway_segment_same with(next:=State function no continuation environment parameters memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge with(b:=false);
          [eapply gateway_unary_expression_value with(result:=Vint Int.zero);
            [gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|pointer ()]|reflexivity]|
          gateway_container_setup_source closed pointer]
    end
  end).

Theorem gateway_container_setup_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)container slots parameters object offset memory:
  gateway_ambient_closed backend property ->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true) ->
  gateway_source_segment backend ge property
    (Returnstate(Vptr object offset)(gateway_container_constructor_cont container slots parameters)memory)
    (State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)
      (gateway_container_setup_parameters container object offset parameters)memory)property.
Proof.
  intros CLOSED POINTER;destruct container;gateway_container_setup_source CLOSED ltac:(fun _=>
    match goal with GOOD:property ?current ?world|-_=>
      change(option_map(fun flag=>Val.of_bool(negb flag))
        (if Mem.weak_valid_pointer current object(Ptrofs.unsigned offset)then Some true else None)=Some(Vint Int.zero));
      rewrite(POINTER current world GOOD);reflexivity end).
Qed.
