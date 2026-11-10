(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Exhausted decoder depth takes the real NULL-return failure path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFailurePaths GatewayValueEntry
  GatewayFunctionEntry GatewayFrames GatewayPure.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_value_depth_check:=
  match fn_body f_host_value with Ssequence(Ssequence first _) _=>first|_=>Sskip end.
Definition gateway_value_after_check:=match fn_body f_host_value with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_guard:=
  match fn_body f_host_value with Ssequence(Ssequence _ second) _=>second|_=>Sskip end.
Definition gateway_value_guard_failure:=
  match gateway_value_guard with Sifthenelse _ failure _=>failure|_=>Sskip end.

Lemma gateway_value_body_guard_shape :fn_body f_host_value=
  Ssequence(Ssequence gateway_value_depth_check gateway_value_guard)gateway_value_after_check.
Proof. reflexivity. Qed.

Lemma gateway_value_guard_failure_profile :gateway_must_null gateway_value_guard_failure.
Proof. right;split;[reflexivity|reflexivity]. Qed.
Lemma gateway_value_pointer_return:gateway_pointer_return f_host_value.
Proof. exists(Tstruct __object noattr),noattr;reflexivity. Qed.

Lemma gateway_value_zero_depth_expression ge environment temporaries memory :
  temporaries!_depth=Some(Vint Int.zero) ->
  expression_value ge environment temporaries memory(Eunop Onotbool(Etempvar _depth tuint)tint)(Vint Int.one).
Proof.
  intro DEPTH;apply old_expression_value;eapply value_unary;[apply value_temp;exact DEPTH|reflexivity].
Qed.

Theorem gateway_value_zero_depth_fails {World Event}(backend:gateway_backend World Event)ge
    slots arguments memory :gateway_value_depth arguments=Int.zero ->
  gateway_failure_result backend ge(State f_host_value(fn_body f_host_value)Kstop
    (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
Proof.
  intro ZERO;rewrite gateway_value_body_guard_shape.
  eapply gateway_failure_edge with(target:=State f_host_value
    (Ssequence gateway_value_depth_check gateway_value_guard)(Kseq gateway_value_after_check Kstop)
    (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_seq.
  - eapply gateway_failure_edge with(target:=State f_host_value gateway_value_depth_check
      (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))
      (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_seq.
    + eapply gateway_failure_edge with(target:=State f_host_value
        (Sset _t'1(Econst_int Int.one tint))(Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))
        (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
      * cbn;tauto.
      * intro another;eapply certified_if_edge with(b:=true).
        -- apply gateway_value_zero_depth_expression.
           unfold gateway_value_parameters;rewrite PTree.gss,ZERO;reflexivity.
        -- reflexivity.
      * eapply gateway_failure_edge with(target:=State f_host_value Sskip
          (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))(gateway_value_environment slots)
          (PTree.set _t'1(Vint Int.one)(gateway_value_parameters arguments))memory).
        -- cbn;tauto.
        -- intro another;apply unchanged_store_edge,edge_set;constructor.
        -- eapply gateway_failure_edge with(target:=State f_host_value gateway_value_guard
            (Kseq gateway_value_after_check Kstop)(gateway_value_environment slots)
            (PTree.set _t'1(Vint Int.one)(gateway_value_parameters arguments))memory).
           ++ cbn;tauto.
           ++ intro another;apply unchanged_store_edge,edge_skip_seq.
           ++ eapply gateway_failure_edge with(target:=State f_host_value gateway_value_guard_failure
                (Kseq gateway_value_after_check Kstop)(gateway_value_environment slots)
                (PTree.set _t'1(Vint Int.one)(gateway_value_parameters arguments))memory).
              ** cbn;tauto.
              ** intro another;eapply certified_if_edge with(b:=true).
                 --- apply old_expression_value,value_temp;apply PTree.gss.
                 --- reflexivity.
              ** apply gateway_failure_selected;[exact gateway_value_pointer_return|
                   exact gateway_value_guard_failure_profile|reflexivity].
Qed.

(* The success condition is a real caller pointer result, independent of any
   decoded-value premise. Nested effects, waits and loss remain in the wide run. *)
Theorem gateway_actual_value_success_depth {World Event}(backend:gateway_backend World Event)ge
    arguments before world events value after next :
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->0<Int.unsigned(gateway_value_depth arguments).
Proof.
  intros RUN NONNULL;destruct(Int.eq_dec(gateway_value_depth arguments)Int.zero)as[ZERO|NONZERO].
  - destruct(actual_gateway_function_entry backend ge f_host_value(gateway_value_arguments_list arguments)Kstop
      before world events value Kstop after next RUN)
      as(prefix &suffix &entry_memory &entry_world &environment &temporaries &allocated &EVENTS &PREFIX &ENTRY &BODY).
    destruct(gateway_actual_value_entry ge entry_memory arguments environment temporaries allocated ENTRY)
      as(slots &ENV &TEMPS &ALLOC &FRAME &REST);subst environment temporaries.
    exfalso;apply NONNULL;eapply(gateway_value_zero_depth_fails backend ge slots arguments allocated ZERO);exact BODY.
  - pose proof(Int.unsigned_range(gateway_value_depth arguments))as RANGE.
    assert(UNSIGNED:Int.unsigned(gateway_value_depth arguments)<>0).
    { intro ZERO;apply NONZERO;rewrite<-(Int.repr_unsigned(gateway_value_depth arguments)),ZERO;reflexivity. }
    lia.
Qed.
