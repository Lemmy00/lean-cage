(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A returned array child is passed to its actual builtin append call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueExpressions GatewayContainerLoopSource
  GatewaySourceDynamic GatewaySourcePaths GatewayFramedRuntime GatewayUnaryExpressions.
Import ListNotations.

Definition gateway_container_after_first_guard:=match gateway_container_after_first with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_tag_guard:=match gateway_container_after_first_guard with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_array_branch:=match gateway_container_tag_guard with Sifthenelse _ first _=>first|_=>Sskip end.
Definition gateway_container_append_group:=match gateway_container_array_branch with Ssequence first _=>first|_=>Sskip end.
Definition gateway_container_after_append:=match gateway_container_array_branch with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_append_status:=match gateway_container_append_group with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_append_cont slots parameters:=Kcall(Some _t'33)f_host_value(gateway_value_environment slots)parameters
  (Kseq gateway_container_append_status(Kseq gateway_container_after_append
    (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont))).

Theorem gateway_container_array_append_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters parent parent_offset child child_offset memory symbol definition:
  gateway_ambient_closed backend property ->parameters!_container=Some(Vptr parent parent_offset) ->
  (forall memory world,property memory world ->Mem.weak_valid_pointer memory child(Ptrofs.unsigned child_offset)=true) ->
  (forall memory world,property memory world ->Mem.loadv Mint64 memory(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=
    Some(Vlong(Int64.repr 7))) ->
  Genv.find_symbol ge _PyList_Append=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default ->
  exists called_parameters,gateway_source_path backend ge definition[Vptr parent parent_offset;Vptr child child_offset]
    (gateway_container_append_cont slots called_parameters)property
    (Returnstate(Vptr child child_offset)(gateway_container_first_cont slots parameters)memory)property /\
    called_parameters!_container=Some(Vptr parent parent_offset) /\called_parameters!_first=Some(Vptr child child_offset) /\
    called_parameters!_stream=parameters!_stream /\called_parameters!_depth=parameters!_depth /\
    called_parameters!_index__1=parameters!_index__1.
Proof.
  intros CLOSED PARENT POINTER LOADED SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_source_dynamic_call CLOSED
      ltac:(fun _=>first[apply gateway_value_tag_expression;eapply LOADED;eassumption|
        eapply gateway_unary_expression_value with(value:=Vptr child child_offset)(result:=Vint Int.zero);
          [gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
            match goal with GOOD:property ?current ?world|-_=>
              change(option_map(fun flag=>Val.of_bool(negb flag))
                (if Mem.weak_valid_pointer current child(Ptrofs.unsigned child_offset)then Some true else None)=Some(Vint Int.zero));
              rewrite(POINTER current world GOOD);reflexivity end]])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr parent parent_offset;Vptr child child_offset]
      (gateway_container_append_cont slots _)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr parent parent_offset).
        -- gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr child child_offset).
           ++ gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
           ++ reflexivity.
           ++ apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - repeat split;unfold set_opttemp;repeat rewrite PTree.gso by discriminate;first[assumption|apply PTree.gss|reflexivity].
Qed.
