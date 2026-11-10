(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real required/optional checks preserve the same received graph on success. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayValue GatewayGraphSnapshots GatewayOutcomeValidationContext GatewayObjectInstances GatewayBuiltinTypeSource
  GatewayTypeLiteralSource GatewayTypeOptionalSource GatewayBuiltinValidation GatewayFramedRuntime GatewayThreadRuntime
  GatewayStreamInterface GatewayLocalRuntime GatewayObjectThreads GatewayObjectDiscipline GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationChecks.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (decimal_float : list Z -> Floats.float -> Prop) (detached : val -> mem -> World -> Prop)
    (io : Event -> option gateway_native_io) (stable : World -> block -> Z -> Prop)
    (thread_errno : World -> int) (heap_allocation : block -> Z -> Prop) (leases : World -> nat -> val -> Prop)
    (threads : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    (instances : gateway_instance_runtime backend ge python objects leases).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (original : val) (protected : block -> Z -> Prop) (source : mem) (environment : env).
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.
Context (extra : mem -> World -> Prop)
  (extra_ambient : forall before world after next, base before world -> extra before world ->
    gateway_interference backend before world after next -> extra after next)
  (extra_observer : forall before world after next, base before world -> extra before world ->
    gateway_observer_return (python world) (objects world) before (python next) (objects next) after -> extra after next).
Let context := fun memory world => base memory world /\ extra memory world.

Lemma gateway_validation_check_closed : gateway_ambient_closed backend context.
Proof.
  intros before world after next [BASE EXTRA] AMBIENT; split.
  - eapply (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured original protected source environment); eassumption.
  - eapply extra_ambient; eassumption.
Qed.

Definition gateway_validation_check_post expected kind status memory world : Prop :=
  status = Int.neg Int.one \/
    (context memory world /\ status = (if gateway_builtin_accepts expected kind then Int.one else Int.zero)).

Lemma gateway_validation_check_post_closed expected kind status :
  gateway_ambient_closed backend (gateway_validation_check_post expected kind status).
Proof.
  intros memory world changed following [ERROR |[GOOD MATCH]] INTERFERENCE; [left; exact ERROR |right; split; [|exact MATCH]].
  eapply gateway_validation_check_closed; eassumption.
Qed.

Lemma gateway_validation_instance_post object offset description kind expected class class_offset
    memory world result changed following observed :
  gateway_object_reachable captured original (Vptr object offset) ->
  gateway_object_values captured (Vptr object offset) = Some description -> gateway_object_kind description = Some kind ->
  gateway_builtin_type_address ge expected (Vptr class class_offset) -> context memory world ->
  gateway_object_operation backend gateway_api_is_instance [Vptr object offset; Vptr class class_offset]
    memory world result changed following observed ->
  exists status, result = Vint status /\ gateway_validation_check_post expected kind status changed following.
Proof.
  intros REACHED DESCRIPTION KIND CLASS GOOD OPERATION.
  destruct (gateway_validation_reachable_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 GOOD) REACHED)
    as [ROOT [actual_description [actual_kind [actual_object [actual_offset [VALUE [ACTUAL_KIND [SAME POINTER]]]]]]]].
  assert (EXACT_VALUE : gateway_object_values (objects world) (Vptr object offset) = Some description).
  { rewrite (gateway_validation_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 GOOD)) by exact REACHED; exact DESCRIPTION. }
  destruct (gateway_builtin_instance_operation _ _ _ _ _ instances memory world (Vptr object offset) description kind expected
    (Vptr class class_offset) result changed following observed
    (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 GOOD)) ROOT EXACT_VALUE KIND CLASS OPERATION)
    as [status [RESULT [CHECK [LEASES OBSERVER]]]].
  exists status; split; [exact RESULT |].
  destruct (Int.eq_dec status (Int.neg Int.one)) as [ERROR |NONERROR]; [left; exact ERROR |right; split].
  - split.
    + eapply gateway_validation_context_observer; [exact (proj1 GOOD) |apply OBSERVER; exact NONERROR].
    + eapply extra_observer; [exact (proj1 GOOD) |exact (proj2 GOOD) |apply OBSERVER; exact NONERROR].
  - destruct (gateway_known_instance_result _ _ _ _ _ _ EXACT_VALUE KIND CHECK) as [MATCH |ERROR]; [exact MATCH |contradiction].
Qed.

Theorem gateway_actual_validation_type_check object offset description kind expected class class_offset none optional
    before world events value after next symbol definition :
  context before world -> gateway_object_reachable captured original (Vptr object offset) ->
  gateway_object_values captured (Vptr object offset) = Some description -> gateway_object_kind description = Some kind ->
  gateway_builtin_type_address ge expected (Vptr class class_offset) ->
  (optional = Int.zero \/ optional = Int.one) -> Genv.find_symbol ge __Py_NoneStruct = Some none ->
  Genv.find_symbol ge _PyObject_IsInstance = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  gateway_object_api_definition gateway_api_is_instance = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_has_type) [Vptr object offset; Vptr class class_offset; Vint optional] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists status, value = Vint status /\ (0 < Int.signed status -> context after next /\ status = Int.one /\
    ((optional = Int.one /\ Vptr object offset = Vptr none Ptrofs.zero) \/ gateway_builtin_accepts expected kind = true)).
Proof.
  intros CONTEXT REACHED DESCRIPTION KIND CLASS OPTIONAL NONE SYMBOL FUNCTION DEFINITION TYPE RUN.
  assert (POINTER : forall memory current, context memory current -> Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) = true).
  { intros memory current GOOD.
    destruct (gateway_validation_reachable_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 GOOD) REACHED)
      as [ROOT [actual_description [actual_kind [actual_object [actual_offset [VALUE [ACTUAL_KIND [SAME LIVE]]]]]]]].
    inversion SAME; subst; exact LIVE. }
  destruct OPTIONAL as [ZERO |ONE]; subst optional.
  - assert (RESULT : exists status, value = Vint status /\ gateway_validation_check_post expected kind status after next).
    { destruct (gateway_actual_required_type_check backend ge context (gateway_validation_check_post expected kind)
        object offset class class_offset before world events value after next symbol definition
        gateway_validation_check_closed (gateway_validation_check_post_closed expected kind) CONTEXT POINTER SYMBOL FUNCTION DEFINITION TYPE
        ltac:(intros; eapply gateway_validation_instance_post; eassumption) RUN)
        as (prefix &suffix &called &owner &changed &following &status &observed &parameters &EVENTS &SAME &POST &REST).
      exists status; auto. }
    destruct RESULT as [status [SAME POST]]; exists status; split; [exact SAME |].
    intros POSITIVE; destruct POST as [ERROR |[GOOD MATCH]].
    + rewrite ERROR in POSITIVE; change (0 < -1) in POSITIVE; lia.
    + destruct (gateway_builtin_accepts expected kind) eqn:ACCEPT; [exact (conj GOOD (conj MATCH (or_intror eq_refl))) |].
      rewrite MATCH in POSITIVE; change (0 < 0) in POSITIVE; lia.
  - destruct (Val.eq (Vptr object offset) (Vptr none Ptrofs.zero)) as [SAME |OTHER].
    + inversion SAME; subst object offset.
      destruct (gateway_actual_none_type_check backend ge context (Vptr class class_offset) none before world events value after next
        gateway_validation_check_closed CONTEXT NONE POINTER RUN) as [VALUE GOOD].
      exists Int.one; split; [exact VALUE |intros; exact (conj GOOD (conj eq_refl (or_introl (conj eq_refl eq_refl))))].
    + destruct (gateway_actual_optional_type_check backend ge context (gateway_validation_check_post expected kind)
        object offset class class_offset none before world events value after next symbol definition
        gateway_validation_check_closed (gateway_validation_check_post_closed expected kind) CONTEXT OTHER POINTER NONE SYMBOL FUNCTION DEFINITION TYPE
        ltac:(intros; eapply gateway_validation_instance_post; eassumption) RUN) as [status [SAME POST]].
      exists status; split; [exact SAME |intros POSITIVE].
      destruct POST as [ERROR |[GOOD MATCH]].
      * rewrite ERROR in POSITIVE; change (0 < -1) in POSITIVE; lia.
      * destruct (gateway_builtin_accepts expected kind) eqn:ACCEPT; [exact (conj GOOD (conj MATCH (or_intror eq_refl))) |].
        rewrite MATCH in POSITIVE; change (0 < 0) in POSITIVE; lia.
Qed.
End ValidationChecks.
