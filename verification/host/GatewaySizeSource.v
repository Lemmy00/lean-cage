(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Every actual native guard return satisfies the shared bound. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPure GatewayControl.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Ltac pure_sequence :=
  lazymatch goal with
  | |-gateway_pure_path ?ge(State ?f(Ssequence ?a ?b)?k ?e ?le ?m)?value=>
    eapply gateway_pure_next with(next:=State f a(Kseq b k)e le m);
    [cbn;tauto|intro memory;apply unchanged_store_edge,edge_seq|]
  | |-gateway_pure_path ?ge(State ?f Sskip(Kseq ?b ?k)?e ?le ?m)?value=>
    eapply gateway_pure_next with(next:=State f b k e le m);
    [cbn;tauto|intro memory;apply unchanged_store_edge,edge_skip_seq|]
  end.

Lemma size_body_pure_accepts ge m size maximum :
  0<=size<=maximum ->maximum<=Int64.max_signed ->
  gateway_pure_path ge
    (State f_host_gateway_size(fn_body f_host_gateway_size)Kstop empty_env
      (size_bindings size maximum)m)(Vint Int.zero).
Proof.
  intros BOUNDS MAXIMUM.
  unfold f_host_gateway_size;cbn[fn_body].
  pure_sequence.
  eapply gateway_pure_next with(next:=State f_host_gateway_size Sskip
    (Kseq _ Kstop)empty_env(size_bindings size maximum)m).
  - cbn;tauto.
  - intro memory;apply unchanged_store_edge;eapply edge_if with(b:=false).
    + apply size_nonnegative with(size:=size);[lia|reflexivity].
    + reflexivity.
  - pure_sequence;pure_sequence.
    eapply gateway_pure_next with(next:=State f_host_gateway_size Sskip
      (Kseq _ Kstop)empty_env(size_bindings size maximum)m).
    + cbn;tauto.
    + intro memory;apply unchanged_store_edge;eapply edge_if with(b:=false).
      * pose proof(size_comparison ge(size_bindings size maximum)memory size maximum
          ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(reflexivity))as VALUE.
        rewrite zlt_false in VALUE by lia;exact VALUE.
      * reflexivity.
    + pure_sequence.
      eapply gateway_pure_next with(next:=Returnstate(Vint Int.zero)Kstop m).
      * cbn;tauto.
      * intro memory;apply unchanged_store_edge;eapply edge_return;[constructor|reflexivity].
      * constructor.
Qed.

Lemma size_body_pure_rejects_large ge m size maximum :
  0<=maximum<size ->size<=Int64.max_signed ->
  gateway_pure_path ge
    (State f_host_gateway_size(fn_body f_host_gateway_size)Kstop empty_env
      (size_bindings size maximum)m)(Vint(Int.neg Int.one)).
Proof.
  intros BOUNDS SIZE.
  unfold f_host_gateway_size;cbn[fn_body].
  pure_sequence.
  eapply gateway_pure_next with(next:=State f_host_gateway_size Sskip
    (Kseq _ Kstop)empty_env(size_bindings size maximum)m).
  - cbn;tauto.
  - intro memory;apply unchanged_store_edge;eapply edge_if with(b:=false).
    + apply size_nonnegative with(size:=size);[lia|reflexivity].
    + reflexivity.
  - pure_sequence;pure_sequence.
    eapply gateway_pure_next with(next:=State f_host_gateway_size
      (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))
      (Kseq _ Kstop)empty_env(size_bindings size maximum)m).
    + cbn;tauto.
    + intro memory;apply unchanged_store_edge;eapply edge_if with(b:=true).
      * pose proof(size_comparison ge(size_bindings size maximum)memory size maximum
          ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(reflexivity))as VALUE.
        rewrite zlt_true in VALUE by lia;exact VALUE.
      * reflexivity.
    + eapply gateway_pure_next with(next:=Returnstate(Vint(Int.neg Int.one))Kstop m).
      * cbn;tauto.
      * intro memory;apply unchanged_store_edge;eapply edge_return;
          [eapply value_unary;[constructor|reflexivity]|reflexivity].
      * constructor.
Qed.

Lemma size_call_pure_rejects_large ge m size maximum :
  0<=maximum<size ->size<=Int64.max_signed ->
  gateway_pure_path ge
    (Callstate(Internal f_host_gateway_size)
      [Vlong(Int64.repr size);Vlong(Int64.repr maximum)]Kstop m)(Vint(Int.neg Int.one)).
Proof.
  intros BOUNDS SIZE.
  eapply gateway_pure_next with(next:=State f_host_gateway_size(fn_body f_host_gateway_size)
    Kstop empty_env(size_bindings size maximum)m).
  - cbn;tauto.
  - intro memory;apply function_entry_source_edge,actual_size_function_entry.
  - apply size_body_pure_rejects_large;assumption.
Qed.

Theorem actual_native_guard_zero_is_bounded {World Event}(backend:gateway_backend World Event)ge
    size maximum before world events after final_world :
  0<=size<=Int64.max_signed ->0<=maximum<=Int64.max_signed ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_gateway_size)
      [Vlong(Int64.repr size);Vlong(Int64.repr maximum)]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)final_world) ->
  checked_native_bound size maximum.
Proof.
  intros SIZE MAXIMUM RUN.
  destruct(Z_le_dec size maximum)as[BOUNDED|LARGE].
  - constructor;apply shared_native_bound_accepts;lia.
  - pose proof(size_call_pure_rejects_large ge before size maximum ltac:(lia)ltac:(lia))as SCRIPT.
    pose proof(gateway_pure_path_return backend ge _ _ before _ _ _ _ _ SCRIPT RUN)as BAD.
    inversion BAD.
Qed.
