(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: JSON-number construction frontiers retain the actual source
   continuations and operand temporaries, including independently owned cached aliases. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewaySourcePaths GatewaySourceBoundCalls
  GatewayBindings GatewayObjects GatewayFramedRuntime.
Import ListNotations.

Definition gateway_number_zero_group:=json_number_first json_number_integer_construction.
Definition gateway_number_zero_assign:=json_number_rest gateway_number_zero_group.
Definition gateway_number_after_zero:=json_number_rest json_number_integer_construction.
Definition gateway_number_base_group:=json_number_first gateway_number_after_zero.
Definition gateway_number_base_assign:=json_number_rest gateway_number_base_group.
Definition gateway_number_after_base:=json_number_rest gateway_number_after_zero.
Definition gateway_number_zero_cont parameters:=Kcall(Some _t'15)f_host_json_number empty_env parameters
  (Kseq gateway_number_zero_assign(Kseq gateway_number_after_zero Kstop)).
Definition gateway_number_base_cont parameters:=Kcall(Some _t'16)f_host_json_number empty_env parameters
  (Kseq gateway_number_base_assign(Kseq gateway_number_after_base Kstop)).
Definition gateway_number_decode_group:=json_number_first json_number_float_construction.
Definition gateway_number_decode_assign:=json_number_rest gateway_number_decode_group.
Definition gateway_number_after_decode:=json_number_rest json_number_float_construction.
Definition gateway_number_decode_cont parameters:=Kcall(Some _t'13)f_host_json_number empty_env parameters
  (Kseq gateway_number_decode_assign(Kseq gateway_number_after_decode(Kseq json_number_integer_construction Kstop))).

Theorem gateway_actual_number_constructor_bindings:
  (exists definition,gateway_object_api_definition gateway_api_long_signed=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyLong_FromLong definition /\
    type_of_fundef definition=Tfunction[tlong](tptr(Tstruct __object noattr))cc_default) /\
  (exists definition,gateway_object_api_definition gateway_api_long_unsigned=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyLong_FromUnsignedLong definition /\
    type_of_fundef definition=Tfunction[tulong](tptr(Tstruct __object noattr))cc_default).
Proof.
  split;eexists;split;[reflexivity| |reflexivity|];split;
    first[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.

Lemma gateway_number_long_literal ge environment parameters memory number ty:
  expression_value ge environment parameters memory(Econst_long number ty)(Vlong number).
Proof. split;[apply eval_Econst_long|]. intros other EVAL;inversion EVAL;subst;try reflexivity.
  match goal with LOCATION:eval_lvalue _ _ _ _ (Econst_long _ _) _ _ _|-_=>inversion LOCATION end. Qed.

Theorem gateway_number_base_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters zero memory symbol definition:
  gateway_ambient_closed backend property->
  Genv.find_symbol ge _PyLong_FromUnsignedLong=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tulong](tptr(Tstruct __object noattr))cc_default->
  exists called_parameters,
    gateway_source_path backend ge definition[Vlong(Int64.repr 1000000000)](gateway_number_base_cont called_parameters)property
      (Returnstate zero(gateway_number_zero_cont parameters)memory)property /\
    called_parameters!_value__1=Some zero /\
    (forall identifier,identifier<>_value__1->identifier<>_t'15->called_parameters!identifier=parameters!identifier).
Proof.
  intros CLOSED SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vlong(Int64.repr 1000000000)](gateway_number_base_cont _)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vlong(Int64.repr 1000000000));
          [apply gateway_number_long_literal|reflexivity|apply no_argument_values].
      * exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - split;[apply PTree.gss|]. intros identifier A B;unfold set_opttemp;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.
