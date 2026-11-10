(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Both real entry checks call Get then GetID on that same result. *)
From Stdlib Require Import ZArith List Lia String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRegistry GatewayBindings GatewaySourceBoundCalls
  GatewaySourcePaths GatewaySourceCuts GatewaySourceSegmentAutomation GatewayFailurePaths GatewayFramedRuntime
  GatewayInitializationSource GatewayInitializationBootstrap GatewayValueGuards.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_interpreter_owner (guarded : bool) := if guarded then f_PyInit__host else f_host_initialize.
Definition gateway_interpreter_prefix guarded := match fn_body (gateway_interpreter_owner guarded) with
  Ssequence first _ => first | _ => Sskip end.
Definition gateway_interpreter_rest guarded := match fn_body (gateway_interpreter_owner guarded) with
  Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_interpreter_calls guarded := match gateway_interpreter_prefix guarded with
  Ssequence calls _ => calls | _ => Sskip end.
Definition gateway_interpreter_get_call guarded := match gateway_interpreter_calls guarded with
  Ssequence first _ => first | _ => Sskip end.
Definition gateway_interpreter_id_call guarded := match gateway_interpreter_calls guarded with
  Ssequence _ second => second | _ => Sskip end.
Definition gateway_interpreter_guard guarded := match gateway_interpreter_prefix guarded with
  Ssequence _ guard => guard | _ => Sskip end.
Definition gateway_interpreter_get_cont guarded parameters :=
  Kcall (Some _t'1) (gateway_interpreter_owner guarded) empty_env parameters
    (Kseq (gateway_interpreter_id_call guarded)
      (Kseq (gateway_interpreter_guard guarded) (Kseq (gateway_interpreter_rest guarded) Kstop))).
Definition gateway_interpreter_id_cont guarded parameters :=
  Kcall (Some _t'2) (gateway_interpreter_owner guarded) empty_env parameters
    (Kseq (gateway_interpreter_guard guarded) (Kseq (gateway_interpreter_rest guarded) Kstop)).
Definition gateway_interpreter_get_definition : Ctypes.fundef Clight.function :=
  External (EF_external "PyInterpreterState_Get"%string (mksignature [] Xptr cc_default)) []
    (tptr (Tstruct __is noattr)) cc_default.
Definition gateway_interpreter_id_definition : Ctypes.fundef Clight.function :=
  External (EF_external "PyInterpreterState_GetID"%string (mksignature [Xptr] Xlong cc_default))
    [tptr (Tstruct __is noattr)] tlong cc_default.

Theorem gateway_actual_interpreter_bindings :
  gateway_function_binding (Clight.globalenv prog) _PyInterpreterState_Get gateway_interpreter_get_definition /\
  gateway_function_binding (Clight.globalenv prog) _PyInterpreterState_GetID gateway_interpreter_id_definition.
Proof. split; apply gateway_actual_function_binding; vm_compute; reflexivity. Qed.

Theorem gateway_interpreter_get_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv) (guarded : bool)
    (property : mem -> World -> Prop) parameters memory symbol :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _PyInterpreterState_Get = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_interpreter_get_definition ->
  gateway_source_path backend ge gateway_interpreter_get_definition [] (gateway_interpreter_get_cont guarded parameters)
    property (State (gateway_interpreter_owner guarded) (fn_body (gateway_interpreter_owner guarded)) Kstop empty_env parameters memory) property.
Proof.
  intros CLOSED SYMBOL FUNCTION; destruct guarded.
  all: gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  all: (eapply gateway_source_same with (target := Callstate gateway_interpreter_get_definition [] (gateway_interpreter_get_cont _ parameters) memory);
    [exact CLOSED |cbn; tauto | |apply gateway_source_reached; auto]).
  all: intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero);
    [reflexivity |apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity] |
      apply no_argument_values |change (Genv.find_funct_ptr ge symbol = Some gateway_interpreter_get_definition); exact FUNCTION |reflexivity].
Qed.

Theorem gateway_interpreter_id_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv) (guarded : bool)
    (property : mem -> World -> Prop) parameters memory object offset symbol :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _PyInterpreterState_GetID = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_interpreter_id_definition ->
  gateway_source_path backend ge gateway_interpreter_id_definition [Vptr object offset]
    (gateway_interpreter_id_cont guarded (PTree.set _t'1 (Vptr object offset) parameters)) property
    (Returnstate (Vptr object offset) (gateway_interpreter_get_cont guarded parameters) memory) property.
Proof.
  intros CLOSED SYMBOL FUNCTION; destruct guarded.
  all: gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  all: (eapply gateway_source_same with (target := Callstate gateway_interpreter_id_definition [Vptr object offset]
      (gateway_interpreter_id_cont _ (PTree.set _t'1 (Vptr object offset) parameters)) memory);
    [exact CLOSED |cbn; tauto | |apply gateway_source_reached; auto]).
  all: intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero);
    [reflexivity |apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity] | |
      change (Genv.find_funct_ptr ge symbol = Some gateway_interpreter_id_definition); exact FUNCTION |reflexivity].
  all: apply cons_argument_values with (v := Vptr object offset);
    [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |apply no_argument_values].
Qed.

Theorem gateway_interpreter_nonzero_denied {World Event} (backend : gateway_backend World Event) (ge : Clight.genv) (guarded : bool)
    parameters memory identifier :
  identifier <> Int64.zero -> gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate (Vlong identifier) (gateway_interpreter_id_cont guarded parameters) memory).
Proof.
  intro NONZERO.
  assert (ZERO : Int64.eq identifier Int64.zero = false) by (apply Int64.eq_false; exact NONZERO).
  pose proof ZERO as ZERO_REPR; change (Int64.eq identifier (Int64.repr 0) = false) in ZERO_REPR.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True))
    by (unfold gateway_ambient_closed; intros; exact I).
  assert (POINTER : gateway_pointer_return (gateway_interpreter_owner guarded))
    by (destruct guarded; repeat eexists; reflexivity).
  destruct guarded.
  all: gateway_bound_source_failure CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => cbn -[Int64.eq];
        change (Int64.repr (Int.signed (Int.repr 0))) with Int64.zero;
        rewrite ?ZERO, ?ZERO_REPR; reflexivity)
      POINTER.
Qed.

Theorem gateway_actual_interpreter_zero {World Event} (backend : gateway_backend World Event) (ge : Clight.genv) (guarded : bool)
    parameters before world events identifier value after next :
  gateway_steps backend ge
    (gateway_live (Returnstate (Vlong identifier) (gateway_interpreter_id_cont guarded parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr -> identifier = Int64.zero.
Proof.
  intros RUN NONNULL; destruct (Int64.eq_dec identifier Int64.zero) as [ZERO |NONZERO]; [exact ZERO |].
  exfalso; apply NONNULL.
  exact (gateway_interpreter_nonzero_denied backend ge guarded parameters before identifier NONZERO before world events value after next I RUN).
Qed.
