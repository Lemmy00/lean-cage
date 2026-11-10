(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Boolean tags construct the corresponding value through the actual builtin call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayPure GatewayValueEntry GatewayValueNull
  GatewayValueDispatch GatewayValueExpressions GatewaySourcePaths GatewaySourceSegments GatewaySourceTactics GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_value_boolean_test:=match gateway_value_after_null with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_after_boolean:=match gateway_value_after_null with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_boolean_check:=match gateway_value_boolean_test with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_boolean_guard:=match gateway_value_boolean_test with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_boolean_first_read:=match gateway_value_boolean_check with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_boolean_first_guard:=match gateway_value_boolean_check with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_boolean_second:=match gateway_value_boolean_first_guard with Sifthenelse _ _ rest=>rest|_=>Sskip end.
Definition gateway_value_boolean_second_read:=match gateway_value_boolean_second with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_boolean_second_set:=match gateway_value_boolean_second with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_boolean_branch:=match gateway_value_boolean_guard with Sifthenelse _ first _=>first|_=>Sskip end.
Definition gateway_value_boolean_body:=match gateway_value_boolean_branch with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_boolean_return:=match gateway_value_boolean_branch with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_boolean_read:=match gateway_value_boolean_body with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_boolean_call:=match gateway_value_boolean_body with Ssequence _ rest=>rest|_=>Sskip end.

Definition gateway_value_boolean_tag(flag:bool):=if flag then Int64.repr 2 else Int64.one.
Definition gateway_value_boolean_argument(flag:bool):=Vlong(if flag then Int64.one else Int64.zero).
Definition gateway_value_boolean_first_parameters(flag:bool)arguments initial:=
  PTree.set _t'91(Vlong(gateway_value_boolean_tag flag))
    (gateway_value_nonzero_tag_parameters arguments initial(gateway_value_boolean_tag flag)).
Definition gateway_value_boolean_control_parameters(flag:bool)arguments initial:=
  PTree.set _t'4(Vint Int.one)
    (if flag then PTree.set _t'92(Vlong(gateway_value_boolean_tag flag))
      (gateway_value_boolean_first_parameters flag arguments initial)
     else gateway_value_boolean_first_parameters flag arguments initial).
Definition gateway_value_boolean_parameters(flag:bool)arguments initial:=
  PTree.set _t'90(Vlong(gateway_value_boolean_tag flag))(gateway_value_boolean_control_parameters flag arguments initial).
Definition gateway_value_boolean_cont(flag:bool)slots arguments initial:=
  Kcall(Some _t'3)f_host_value(gateway_value_environment slots)(gateway_value_boolean_parameters flag arguments initial)
    (Kseq gateway_value_boolean_return(Kseq gateway_value_after_boolean Kstop)).

Theorem gateway_value_boolean_selector {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)flag slots arguments initial memory :
  gateway_ambient_closed backend property ->
  (forall memory world,property memory world->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(gateway_value_boolean_tag flag))) ->
  gateway_source_segment backend ge property
    (State f_host_value gateway_value_boolean_first_guard
      (Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop))(gateway_value_environment slots)
      (gateway_value_boolean_first_parameters flag arguments initial)memory)
    (State f_host_value Sskip(Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop))
      (gateway_value_environment slots)(gateway_value_boolean_control_parameters flag arguments initial)memory)property.
Proof.
  intros CLOSED LOADED;destruct flag.
  - eapply gateway_segment_same with(next:=State f_host_value gateway_value_boolean_second
      (Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop))(gateway_value_environment slots)
      (gateway_value_boolean_first_parameters true arguments initial)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_if_edge with(b:=false).
      * apply old_expression_value;eapply value_binary;[apply value_temp;apply PTree.gss|constructor|reflexivity].
      * reflexivity.
    + change gateway_value_boolean_second with(Ssequence gateway_value_boolean_second_read gateway_value_boolean_second_set).
      gateway_segment_seq CLOSED.
      eapply gateway_segment_same with(next:=State f_host_value Sskip
        (Kseq gateway_value_boolean_second_set(Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop)))
        (gateway_value_environment slots)
        (PTree.set _t'92(Vlong(gateway_value_boolean_tag true))
          (gateway_value_boolean_first_parameters true arguments initial))memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros current world GOOD;apply certified_set_edge,gateway_value_tag_expression.
        apply LOADED with(world:=world);exact GOOD.
      * gateway_segment_skip CLOSED.
        eapply gateway_segment_same with(next:=State f_host_value Sskip
          (Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop))(gateway_value_environment slots)
          (gateway_value_boolean_control_parameters true arguments initial)memory).
        -- exact CLOSED.
        -- cbn;tauto.
        -- intros;apply certified_set_edge,old_expression_value;eapply value_cast.
           ++ eapply value_binary;[apply value_temp;apply PTree.gss|constructor|reflexivity].
           ++ reflexivity.
        -- apply gateway_segment_here.
  - eapply gateway_segment_same with(next:=State f_host_value(Sset _t'4(Econst_int Int.one tint))
      (Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop))(gateway_value_environment slots)
      (gateway_value_boolean_first_parameters false arguments initial)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_if_edge with(b:=true).
      * apply old_expression_value;eapply value_binary;[apply value_temp;apply PTree.gss|constructor|reflexivity].
      * reflexivity.
    + eapply gateway_segment_same with(next:=State f_host_value Sskip
        (Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop))(gateway_value_environment slots)
        (gateway_value_boolean_control_parameters false arguments initial)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros;apply unchanged_store_edge,edge_set;constructor.
      * apply gateway_segment_here.
Qed.

Theorem gateway_value_boolean_call_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)flag slots arguments initial memory symbol definition :
  gateway_ambient_closed backend property ->
  (forall memory world,property memory world->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(gateway_value_boolean_tag flag))) ->
  Genv.find_symbol ge _PyBool_FromLong=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tlong](tptr(Tstruct __object noattr))cc_default ->
  gateway_source_path backend ge definition[gateway_value_boolean_argument flag]
    (gateway_value_boolean_cont flag slots arguments initial)property
    (State f_host_value gateway_value_after_null Kstop(gateway_value_environment slots)
      (gateway_value_nonzero_tag_parameters arguments initial(gateway_value_boolean_tag flag))memory)property.
Proof.
  intros CLOSED LOADED SYMBOL FUNCTION TYPE.
  change gateway_value_after_null with(Ssequence gateway_value_boolean_test gateway_value_after_boolean).
  gateway_path_seq CLOSED.
  change gateway_value_boolean_test with(Ssequence gateway_value_boolean_check gateway_value_boolean_guard).
  gateway_path_seq CLOSED.
  change gateway_value_boolean_check with(Ssequence gateway_value_boolean_first_read gateway_value_boolean_first_guard).
  gateway_path_seq CLOSED.
  eapply gateway_source_same with(target:=State f_host_value Sskip
    (Kseq gateway_value_boolean_first_guard(Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop)))
    (gateway_value_environment slots)(gateway_value_boolean_first_parameters flag arguments initial)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros current world GOOD;apply certified_set_edge,gateway_value_tag_expression.
    apply LOADED with(world:=world);exact GOOD.
  - gateway_path_skip CLOSED.
    eapply gateway_segment_then_call;[exact(gateway_value_boolean_selector backend ge property flag slots arguments initial memory CLOSED LOADED)|].
    gateway_path_skip CLOSED.
    eapply gateway_source_same with(target:=State f_host_value gateway_value_boolean_branch
      (Kseq gateway_value_after_boolean Kstop)(gateway_value_environment slots)
      (gateway_value_boolean_control_parameters flag arguments initial)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_if_edge with(b:=true).
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
    + change gateway_value_boolean_branch with(Ssequence gateway_value_boolean_body gateway_value_boolean_return).
      gateway_path_seq CLOSED.
      change gateway_value_boolean_body with(Ssequence gateway_value_boolean_read gateway_value_boolean_call).
      gateway_path_seq CLOSED.
      eapply gateway_source_same with(target:=State f_host_value Sskip
        (Kseq gateway_value_boolean_call(Kseq gateway_value_boolean_return(Kseq gateway_value_after_boolean Kstop)))
        (gateway_value_environment slots)(gateway_value_boolean_parameters flag arguments initial)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros current world GOOD;apply certified_set_edge,gateway_value_tag_expression.
        apply LOADED with(world:=world);exact GOOD.
      * gateway_path_skip CLOSED.
        eapply gateway_source_same with(target:=Callstate definition[gateway_value_boolean_argument flag]
          (gateway_value_boolean_cont flag slots arguments initial)memory).
        -- exact CLOSED.
        -- cbn;tauto.
        -- intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
           ++ reflexivity.
           ++ apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
           ++ destruct flag.
              ** apply cons_argument_values with(v:=Vint Int.one).
                 --- apply old_expression_value;eapply value_binary;[apply value_temp;apply PTree.gss|constructor|reflexivity].
                 --- reflexivity.
                 --- apply no_argument_values.
              ** apply cons_argument_values with(v:=Vint Int.zero).
                 --- apply old_expression_value;eapply value_binary;[apply value_temp;apply PTree.gss|constructor|reflexivity].
                 --- reflexivity.
                 --- apply no_argument_values.
           ++ change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
           ++ exact TYPE.
        -- apply gateway_source_reached;auto.
Qed.
