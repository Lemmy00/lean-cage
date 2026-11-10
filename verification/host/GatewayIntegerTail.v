(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real numeric flag selects the actual decimal constructor;
   a rejected lexical form retains null through all real error and cleanup callbacks. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueReturns GatewayValueGuards GatewayValueExpressions GatewayScalarContext
  GatewayScalarLength GatewayScalarBytesPath GatewayScalarTerminate GatewayIntegerLoop GatewayIntegerPrefixSource GatewaySourcePaths GatewaySourceSegments
  GatewaySourceDynamic GatewaySourceBoundCalls GatewayTempNull GatewayFramedRuntime.
Import ListNotations.

Definition gateway_integer_rejected:=match gateway_integer_after_loop with Sifthenelse _ _ rejected=>rejected|_=>Sskip end.
Definition gateway_integer_tail_cont:=Kseq gateway_scalar_cleanup(Kseq gateway_value_after_scalar Kstop).

Theorem gateway_integer_constructor_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters object memory symbol definition:
  gateway_ambient_closed backend property->parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!_valid=Some(Vint Int.one)->
  Genv.find_symbol ge _PyLong_FromString=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr tschar;tptr(tptr tschar);tint](tptr(Tstruct __object noattr))cc_default->
  gateway_source_path backend ge definition[Vptr object Ptrofs.zero;Vnullptr;Vint(Int.repr 10)]
    (gateway_scalar_constructor_cont _t'19 slots parameters)property
    (State f_host_value Sskip gateway_integer_loop_cont(gateway_value_environment slots)parameters memory)property.
Proof.
  intros CLOSED BYTES VALID SYMBOL FUNCTION TYPE.
  unfold gateway_integer_loop_cont.
  gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
  eapply gateway_source_same with(target:=Callstate definition[Vptr object Ptrofs.zero;Vnullptr;Vint(Int.repr 10)]
    (gateway_scalar_constructor_cont _t'19 slots parameters)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
    + apply cons_argument_values with(v:=Vptr object Ptrofs.zero).
      * apply old_expression_value,value_temp;exact BYTES.
      * reflexivity.
      * apply cons_argument_values with(v:=Vnullptr).
        -- eapply cast_expression_value with(v:=Vint Int.zero);[apply old_expression_value,value_int|reflexivity].
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vint(Int.repr 10));
            [apply old_expression_value,value_int|reflexivity|apply no_argument_values].
    + exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached;auto.
Qed.

Theorem gateway_integer_rejected_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters memory:
  gateway_ambient_closed backend property->parameters!_valid=Some(Vint Int.zero)->
  gateway_source_segment backend ge property
    (State f_host_value Sskip gateway_integer_loop_cont(gateway_value_environment slots)parameters memory)
    (State f_host_value gateway_integer_rejected gateway_integer_tail_cont(gateway_value_environment slots)parameters memory)property.
Proof.
  intros CLOSED VALID.
  eapply gateway_segment_same with(next:=State f_host_value gateway_integer_after_loop gateway_integer_tail_cont
    (gateway_value_environment slots)parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_segment_same with(next:=State f_host_value gateway_integer_rejected gateway_integer_tail_cont
    (gateway_value_environment slots)parameters memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(b:=false);[apply old_expression_value,value_temp;exact VALID|reflexivity].
  - apply gateway_segment_here.
Qed.

Theorem gateway_integer_rejected_is_null {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    slots parameters before world events value after next:
  parameters!_value=Some Vnullptr->
  gateway_steps backend ge
    (gateway_live(State f_host_value gateway_integer_rejected gateway_integer_tail_cont(gateway_value_environment slots)parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intros NULL RUN;eapply(gateway_actual_temp_null backend _value ge _ world events value after next);[|exact RUN].
  left;split;[apply gateway_value_pointer_return|]. split;[exact NULL|]. split;[reflexivity|]. right;split;[reflexivity|].
  cbn[gateway_integer_tail_cont gateway_temp_barrier gateway_no_temp_return gateway_must_temp gateway_temp_pointer].
  left;split;[|reflexivity]. right;split;[reflexivity|].
  exists(Tstruct __object noattr),noattr;reflexivity.
Qed.
