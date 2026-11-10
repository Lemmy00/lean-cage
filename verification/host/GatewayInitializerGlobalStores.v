(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Class publication is the actual C pointer store. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine LocalAccess ClightSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInstructions.
Import ListNotations.
Open Scope Z_scope.

Definition initializer_pointer_assignment global temporary :=
  Sassign (Evar global (tptr (Tstruct __object noattr)))
    (Etempvar temporary (tptr (Tstruct __object noattr))).

Theorem gateway_initializer_pointer_store (ge : Clight.genv) global temporary symbol value
    parameters before continuation trace target :
  Genv.find_symbol ge global = Some symbol -> parameters ! temporary = Some value ->
  step2 ge (State f_host_initialize (initializer_pointer_assignment global temporary)
    continuation empty_env parameters before) trace target ->
  exists changed,
    trace = E0 /\ target = State f_host_initialize Sskip continuation empty_env parameters changed /\
    Mem.store Mptr before symbol 0 value = Some changed.
Proof.
  intros SYMBOL VALUE STEP; inversion STEP; subst;
    try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  match goal with LOCATION : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (proj2 (global_location_value ge empty_env parameters before global
      (tptr (Tstruct __object noattr)) symbol eq_refl SYMBOL) _ _ _ LOCATION)
      as [OBJECT [OFFSET FIELD]]; subst end.
  match goal with EXPR : eval_expr _ _ _ _ _ _ |- _ =>
    pose proof (proj2 (old_expression_value ge empty_env parameters before
      (Etempvar temporary (tptr (Tstruct __object noattr))) value (value_temp _ _ _ _ _ _ _ VALUE))
      _ EXPR) as SAME; subst end.
  cbn [initializer_pointer_assignment typeof Cop.sem_cast Cop.classify_cast] in *.
  assert (v = value).
  { destruct value; vm_compute in H10; congruence. }
  subst v.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst end;
    cbn [access_mode Mem.storev] in *; try discriminate.
  assert (chunk = Mptr) by (change (By_value Mptr = By_value chunk) in H; congruence).
  subst chunk; change (Mem.store Mptr before symbol 0 value = Some m') in H0.
  exists m'; repeat split; try reflexivity; exact H0.
Qed.

Theorem gateway_actual_initializer_pointer_store {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) global temporary symbol value parameters before world continuation
    events returned after next :
  Genv.find_symbol ge global = Some symbol -> parameters ! temporary = Some value ->
  gateway_steps backend ge
    (gateway_live (State f_host_initialize (initializer_pointer_assignment global temporary)
      continuation empty_env parameters before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix memory owner changed,
    events = prefix ++ gateway_source E0 :: suffix /\
    Forall (fun event => event = gateway_ambient) prefix /\
    gateway_steps backend ge
      (gateway_live (State f_host_initialize (initializer_pointer_assignment global temporary)
        continuation empty_env parameters before) world) prefix
      (gateway_live (State f_host_initialize (initializer_pointer_assignment global temporary)
        continuation empty_env parameters memory) owner) /\
    Mem.store Mptr memory symbol 0 value = Some changed /\
    gateway_steps backend ge
      (gateway_live (State f_host_initialize Sskip continuation empty_env parameters changed) owner) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros SYMBOL VALUE RUN.
  destruct (gateway_source_instruction_occurrence backend ge f_host_initialize
    (initializer_pointer_assignment global temporary) continuation empty_env parameters before world
    events returned after next ltac:(cbn; tauto) RUN)
    as (prefix & suffix & memory & owner & trace & target & EVENTS & QUIET & PREFIX & STEP & SUFFIX).
  destruct (gateway_initializer_pointer_store ge global temporary symbol value parameters memory continuation
    trace target SYMBOL VALUE STEP) as (changed & TRACE & TARGET & STORE); subst trace target.
  exists prefix, suffix, memory, owner, changed; repeat split; assumption.
Qed.
