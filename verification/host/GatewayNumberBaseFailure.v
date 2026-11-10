(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A failed base allocation forces the actual integer setup
   cleanup even if the earlier zero object has no usable Boolean pointer observation. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberConstruction GatewayNumberIntegerStructure GatewayNumberFloatSource
  GatewayConditionalFailure GatewayFailurePaths GatewaySourceCuts GatewaySourceBoundCalls GatewayNumberFailures
  GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_number_null_base_denied {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)parameters memory:
  gateway_failure_result backend ge(Returnstate Vnullptr(gateway_number_base_cont parameters)memory).
Proof.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(FAILURE:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_number_base_cont parameters)memory)).
  { eapply gateway_failure_when_same with(target:=State f_host_json_number Sskip
      (Kseq gateway_number_base_assign(Kseq gateway_number_after_base Kstop))empty_env(PTree.set _t'16 Vnullptr parameters)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
    eapply gateway_failure_when_same with(target:=State f_host_json_number gateway_number_base_assign
      (Kseq gateway_number_after_base Kstop)empty_env(PTree.set _t'16 Vnullptr parameters)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    set(saved:=PTree.set _base Vnullptr(PTree.set _t'16 Vnullptr parameters)).
    eapply gateway_failure_when_same with(target:=State f_host_json_number Sskip(Kseq gateway_number_after_base Kstop)empty_env saved memory);
      [exact CLOSED|cbn;tauto|intros;apply certified_set_edge;apply old_expression_value,value_temp;apply PTree.gss|].
    eapply gateway_failure_when_same with(target:=State f_host_json_number gateway_number_after_base Kstop empty_env saved memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_failure_when_same with(target:=State f_host_json_number number_integer_guard_group
      (Kseq number_integer_after_guard Kstop)empty_env saved memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_failure_when_same with(target:=State f_host_json_number number_integer_short_guard
      (Kseq number_integer_failure_guard(Kseq number_integer_after_guard Kstop))empty_env saved memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_failure_when_conditional;[exact CLOSED| |].
    all:gateway_bound_null_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [apply old_expression_value,value_temp;unfold saved;repeat rewrite PTree.gso by discriminate;apply PTree.gss|reflexivity])
      ltac:(fun _=>reflexivity)gateway_number_float_pointer_return. }
  intros before world events value after next RUN;exact(FAILURE before world events value after next I RUN).
Qed.
