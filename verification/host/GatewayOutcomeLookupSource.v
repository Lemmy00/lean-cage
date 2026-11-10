(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Failed required lookups select the real error return before argument use. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewaySourceCuts GatewaySourcePaths
  GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFailurePaths GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_after_files_lookup:=gateway_outcome_right_suffix 5(fn_body f_host_outcome_from).
Definition gateway_outcome_files_lookup_cont environment parameters:=
  Kcall(Some _t'14)f_host_outcome_from environment parameters
    (Kseq(Sset _files(Etempvar _t'14(tptr(Tstruct __object noattr))))(Kseq gateway_outcome_after_files_lookup Kstop)).
Definition gateway_outcome_required_output_guard:=
  match gateway_outcome_right_suffix 11(fn_body f_host_outcome_from)with Ssequence guard _=>guard|_=>Sskip end.
Definition gateway_outcome_after_output_guard:=gateway_outcome_right_suffix 12(fn_body f_host_outcome_from).

Theorem gateway_actual_outcome_missing_files_returns_null {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters before world events value after next:
  gateway_steps backend ge
    (gateway_live(Returnstate Vnullptr(gateway_outcome_files_lookup_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intro RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(POINTER_RETURN:gateway_pointer_return f_host_outcome_from)by(repeat eexists).
  assert(PATH:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_outcome_files_lookup_cont environment parameters)before)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity])
      ltac:(fun _=>reflexivity)POINTER_RETURN. }
  exact(PATH before world events value after next I RUN).
Qed.

Theorem gateway_actual_outcome_missing_output_returns_null {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters output before world events value after next:
  gateway_ambient_closed backend property->environment!_output=Some(output,tptr(Tstruct __object noattr))->
  (forall memory current,property memory current->Mem.load Mptr memory output 0=Some Vnullptr)->
  property before world->
  gateway_steps backend ge
    (gateway_live(State f_host_outcome_from gateway_outcome_required_output_guard
      (Kseq gateway_outcome_after_output_guard Kstop)environment parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intros CLOSED OUTPUT LOAD INPUT RUN.
  assert(POINTER_RETURN:gateway_pointer_return f_host_outcome_from)by(repeat eexists).
  assert(PATH:gateway_failure_when backend ge property
    (State f_host_outcome_from gateway_outcome_required_output_guard
      (Kseq gateway_outcome_after_output_guard Kstop)environment parameters before)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>first[
        eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity]|
        eapply location_read_value with(b:=output)(ofs:=Ptrofs.zero);
          [apply local_location_value;exact OUTPUT|
           eapply deref_loc_value;[reflexivity|
             match goal with GOOD:property ?memory ?current|-_=>exact(LOAD memory current GOOD)end]]])
      ltac:(fun _=>reflexivity)POINTER_RETURN. }
  exact(PATH before world events value after next INPUT RUN).
Qed.
