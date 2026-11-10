(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each recursive child call follows the actual source loop guard. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarContext GatewayContainerAllocation
  GatewayContainerLength GatewaySourceDynamic GatewaySourcePaths GatewaySourceTactics GatewayFramedRuntime GatewayValueReturns.
Import ListNotations.

Definition gateway_container_after_null:=match gateway_container_after_allocate with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_loop_setup:=match gateway_container_after_null with Ssequence first _=>first|_=>Sskip end.
Definition gateway_container_return:=match gateway_container_after_null with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_loop:=match gateway_container_loop_setup with Ssequence _ loop=>loop|_=>Sskip end.
Definition gateway_container_loop_body:=match gateway_container_loop with Sloop body _=>body|_=>Sskip end.
Definition gateway_container_loop_increment:=match gateway_container_loop with Sloop _ increment=>increment|_=>Sskip end.
Definition gateway_container_loop_test:=match gateway_container_loop_body with Ssequence first _=>first|_=>Sskip end.
Definition gateway_container_loop_guard:=match gateway_container_loop_test with Ssequence _ guard=>guard|_=>Sskip end.
Definition gateway_container_iteration:=match gateway_container_loop_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_first_group:=match gateway_container_iteration with Ssequence first _=>first|_=>Sskip end.
Definition gateway_container_after_first:=match gateway_container_iteration with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_assign_first:=match gateway_container_first_group with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_loop_cont:=Kseq gateway_container_return(Kseq gateway_value_after_container Kstop).
Definition gateway_container_first_cont slots parameters:=
  Kcall(Some _t'32)f_host_value(gateway_value_environment slots)parameters
    (Kseq gateway_container_assign_first(Kseq gateway_container_after_first
      (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont))).

Ltac gateway_container_loop_expressions loads :=
  gateway_source_dynamic_expression loads
    ltac:(fun _=>cbn -[Int64.ltu Int64.unsigned Int64.sub];
      repeat match goal with LT:Int64.ltu _ _=true|-_=>progress(rewrite LT)end;reflexivity).

Theorem gateway_container_next_child_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters stream depth index size memory symbol :
  gateway_ambient_closed backend property ->gateway_object_pointer_value stream ->parameters!_stream=Some stream ->parameters!_depth=Some(Vint depth) ->
  parameters!_index__1=Some(Vlong index) ->Int64.ltu index size=true ->
  (forall memory world,property memory world ->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong size)) ->
  Genv.find_symbol ge _host_value=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_value) ->
  exists called_parameters,gateway_source_path backend ge(Internal f_host_value)[stream;Vint(Int.sub depth Int.one)]
    (gateway_container_first_cont slots called_parameters)property
    (State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)parameters memory)property /\
    called_parameters!_stream=Some stream /\called_parameters!_depth=Some(Vint depth) /\
    called_parameters!_container=parameters!_container /\called_parameters!_index__1=Some(Vlong index).
Proof.
  intros CLOSED POINTER STREAM DEPTH INDEX LT LOADED SYMBOL FUNCTION;eexists;split.
  - change gateway_container_loop with(Sloop gateway_container_loop_body gateway_container_loop_increment).
    eapply gateway_source_same with(target:=State f_host_value gateway_container_loop_body
      (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)
      (gateway_value_environment slots)parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
    change gateway_container_loop_body with(Ssequence gateway_container_loop_test gateway_container_iteration).
    gateway_path_seq CLOSED.
    change gateway_container_loop_test with(Ssequence(Sset _t'45(Evar _size tulong))gateway_container_loop_guard).
    gateway_path_seq CLOSED.
    eapply gateway_source_same with(target:=State f_host_value Sskip
      (Kseq gateway_container_loop_guard(Kseq gateway_container_iteration
        (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)))
      (gateway_value_environment slots)(PTree.set _t'45(Vlong size)parameters)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;apply certified_set_edge,gateway_value_size_expression;eapply LOADED;eassumption.
    + gateway_path_skip CLOSED.
      eapply gateway_source_same with(target:=State f_host_value Sskip
        (Kseq gateway_container_iteration(Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont))
        (gateway_value_environment slots)(PTree.set _t'45(Vlong size)parameters)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros;eapply certified_if_edge with(b:=true).
        -- apply old_expression_value;eapply value_binary with(v:=Vlong index)(w:=Vlong size)(result:=Vint Int.one).
           ++ apply value_temp;rewrite PTree.gso by discriminate;exact INDEX.
           ++ apply value_temp;apply PTree.gss.
           ++ change(Some(Val.of_bool(Int64.ltu index size))=Some(Vint Int.one));rewrite LT;reflexivity.
        -- reflexivity.
      * gateway_path_skip CLOSED.
        gateway_source_dynamic_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        eapply gateway_source_same with(target:=Callstate(Internal f_host_value)[stream;Vint(Int.sub depth Int.one)]
          (gateway_container_first_cont slots _)memory).
        { exact CLOSED. }
        { cbn;tauto. }
        { intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
          - reflexivity.
          - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
          - apply cons_argument_values with(v:=stream).
            + gateway_container_loop_expressions ltac:(fun _=>fail).
            + destruct POINTER as[NULL|[object[offset SAME]]];subst stream;reflexivity.
            + apply cons_argument_values with(v:=Vint(Int.sub depth Int.one)).
              * apply old_expression_value;eapply value_binary with(v:=Vint depth)(w:=Vint Int.one)(result:=Vint(Int.sub depth Int.one)).
                -- apply value_temp;rewrite PTree.gso by discriminate;exact DEPTH.
                -- constructor.
                -- reflexivity.
              * reflexivity.
              * apply no_argument_values.
          - change(Genv.find_funct_ptr ge symbol=Some(Internal f_host_value));exact FUNCTION.
          - reflexivity. }
        { apply gateway_source_reached;auto. }
  - repeat split;unfold set_opttemp;repeat rewrite PTree.gso by discriminate;assumption||reflexivity.
Qed.
