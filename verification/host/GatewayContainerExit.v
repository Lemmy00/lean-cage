(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual exhausted count guard reaches the selected container
   return without another child or SDK operation. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueExpressions
  GatewayScalarContext GatewayContainerLength GatewayContainerLoopSource GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime.
Import ListNotations.

Definition gateway_container_exit_parameters size parameters:=PTree.set _t'45(Vlong size)parameters.
Definition gateway_container_return_expression:=Etempvar _container(tptr(Tstruct __object noattr)).

Theorem actual_container_return_expression:
  gateway_container_return=Sreturn(Some gateway_container_return_expression).
Proof. reflexivity. Qed.

Ltac gateway_container_exit_structural closed :=
  tryif solve[apply gateway_segment_here]then idtac else(
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory) _ _=>
    let statement:=eval hnf in body in lazymatch statement with
    |Sloop ?body ?increment=>
      eapply gateway_segment_same with(next:=State function body(Kloop1 body increment continuation)environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|gateway_container_exit_structural closed]
    |Ssequence ?first ?rest=>
      eapply gateway_segment_same with(next:=State function first(Kseq rest continuation)environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|gateway_container_exit_structural closed]
    |Sskip=>let saved:=eval hnf in continuation in lazymatch saved with
      |Kseq ?following ?rest=>
        eapply gateway_segment_same with(next:=State function following rest environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|gateway_container_exit_structural closed]
      end
    |Sbreak=>let saved:=eval hnf in continuation in lazymatch saved with
      |Kseq _ ?rest=>
        eapply gateway_segment_same with(next:=State function Sbreak rest environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_break_seq|gateway_container_exit_structural closed]
      |Kloop1 _ _ ?rest=>
        eapply gateway_segment_same with(next:=State function Sskip rest environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_break_loop1|gateway_container_exit_structural closed]
      end
    |_=>idtac
    end
  end).

Theorem gateway_container_loop_exit_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters index size memory:
  gateway_ambient_closed backend property->parameters!_index__1=Some(Vlong index)->Int64.ltu index size=false->
  (forall memory current,property memory current->Mem.loadv Mint64 memory
    (Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong size))->
  gateway_source_segment backend ge property
    (State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)parameters memory)
    (State f_host_value(Sreturn(Some gateway_container_return_expression))(Kseq gateway_value_after_container Kstop)
      (gateway_value_environment slots)(gateway_container_exit_parameters size parameters)memory)property.
Proof.
  intros CLOSED INDEX DONE LOADED.
  gateway_container_exit_structural CLOSED.
  eapply gateway_segment_same with(next:=State f_host_value Sskip
    (Kseq gateway_container_loop_guard(Kseq gateway_container_iteration
      (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)))
    (gateway_value_environment slots)(gateway_container_exit_parameters size parameters)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;apply certified_set_edge;apply gateway_value_size_expression;eapply LOADED;eassumption.
  - gateway_container_exit_structural CLOSED.
    eapply gateway_segment_same with(next:=State f_host_value Sbreak
      (Kseq gateway_container_iteration(Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont))
      (gateway_value_environment slots)(gateway_container_exit_parameters size parameters)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_if_edge with(b:=false).
      * apply old_expression_value;eapply value_binary with(v:=Vlong index)(w:=Vlong size)(result:=Vint Int.zero).
        -- apply value_temp;unfold gateway_container_exit_parameters;rewrite PTree.gso by discriminate;exact INDEX.
        -- apply value_temp;apply PTree.gss.
        -- change(Some(Val.of_bool(Int64.ltu index size))=Some(Vint Int.zero));rewrite DONE;reflexivity.
      * reflexivity.
    + gateway_container_exit_structural CLOSED.
Qed.
