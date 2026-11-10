(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual validation observes the independently known received builtin graph. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayValue GatewayValueOwnership GatewayGraphSnapshots GatewayOutcomeValidationContext GatewayObjectInstances GatewayBuiltinTypeSource
  GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayObjectThreads
  GatewayObjectDiscipline GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_validation_reachable_builtin {World} python objects decimal_float ledger held reserved captured original protected source environment
    memory world pointer :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment memory world ->
  gateway_object_reachable captured original pointer ->
  gateway_rooted (python world) (objects world) pointer /\
    exists description kind object offset,
      gateway_object_values (objects world) pointer = Some description /\ gateway_object_kind description = Some kind /\
      pointer = Vptr object offset /\ Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) = true.
Proof.
  intros CONTEXT REACHED.
  pose proof (gateway_graph_snapshot_forward _ _ _
    (gateway_validation_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) pointer REACHED) as CURRENT.
  assert (ROOT : gateway_rooted (python world) (objects world) original).
  { constructor; exact (gateway_validation_credit _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT). }
  assert (POINTER_ROOT : gateway_rooted (python world) (objects world) pointer).
  { eapply gateway_reachable_rooted; eassumption. }
  split; [exact POINTER_ROOT |].
  destruct (gateway_validation_destructible _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT pointer CURRENT)
    as [description [kind [VALUE [KIND DESTROY]]]].
  destruct (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) as [[VALID [LIVE [BYTES [DICT ADDRESS]]]] REST].
  destruct (ADDRESS pointer POINTER_ROOT) as [object [offset [SAME WEAK]]].
  exists description, kind, object, offset; auto.
Qed.

Theorem gateway_validation_lookup_context {World Event} (backend : gateway_backend World Event)
    python objects decimal_float ledger held reserved captured original protected source environment
    (runtime : gateway_container_runtime backend python objects)
    fields before world name characters result after next observed :
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_object_values captured original = Some (gateway_dict_object fields) ->
  gateway_object_name before name characters ->
  gateway_object_operation backend gateway_api_dict_get_string [original; name] before world result after next observed ->
  result <> Vnullptr ->
  exists field,
    gateway_dictionary_lookup characters fields = Some field /\ result = gateway_dictionary_value field /\
    gateway_object_reachable captured original result /\
    gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment after next.
Proof.
  intros CONTEXT FIELDS NAME OPERATION NONNULL.
  assert (ROOT : gateway_rooted (python world) (objects world) original)
    by (constructor; exact (gateway_validation_credit _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT)).
  assert (CURRENT : gateway_object_values (objects world) original = Some (gateway_dict_object fields)).
  { rewrite (gateway_validation_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) by constructor; exact FIELDS. }
  destruct (gateway_runtime_dict_lookup _ _ _ runtime before world original fields name characters result after next observed
    (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) ROOT CURRENT NAME OPERATION NONNULL)
    as [field [LOOKUP [VALUE OBSERVER]]].
  exists field; split; [exact LOOKUP |split; [exact VALUE |split]].
  - rewrite VALUE; eapply gateway_reachable_child; [constructor |exact FIELDS |].
    unfold gateway_object_children, gateway_dictionary_children; apply in_flat_map; exists field; split.
    + exact (proj1 (gateway_dictionary_lookup_member _ _ _ LOOKUP)).
    + cbn; auto.
  - eapply gateway_validation_context_observer; eassumption.
Qed.

(* The SDK's exception result need not retain normal readiness. Its actual
   nonpositive source barrier prevents that result from reaching a Copy call. *)
Theorem gateway_actual_positive_required_known_builtin {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation leases
    (threads : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    (instances : gateway_instance_runtime backend ge python objects leases)
    ledger held reserved captured original protected source environment object offset description kind expected class class_offset
    before world events status after next symbol definition :
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_object_reachable captured original (Vptr object offset) ->
  gateway_object_values captured (Vptr object offset) = Some description -> gateway_object_kind description = Some kind ->
  gateway_builtin_type_address ge expected (Vptr class class_offset) ->
  Genv.find_symbol ge _PyObject_IsInstance = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  gateway_object_api_definition gateway_api_is_instance = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_has_type) [Vptr object offset; Vptr class class_offset; Vint Int.zero] Kstop before) world) events
    (gateway_live (Returnstate (Vint status) Kstop after) next) -> 0 < Int.signed status ->
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment after next /\
    gateway_builtin_accepts expected kind = true /\ status = Int.one.
Proof.
  intros CONTEXT REACHED DESCRIPTION KIND CLASS SYMBOL FUNCTION DEFINITION TYPE RUN POSITIVE.
  set (property := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment).
  assert (CLOSED : gateway_ambient_closed backend property).
  { exact (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured original protected source environment). }
  set (post := fun returned memory current => returned = Int.neg Int.one \/
    (property memory current /\ returned = (if gateway_builtin_accepts expected kind then Int.one else Int.zero))).
  assert (POST_CLOSED : forall returned, gateway_ambient_closed backend (post returned)).
  { intros returned memory current changed following [ERROR |[GOOD MATCH]] INTERFERENCE;
      [left; exact ERROR |right; split; [eapply CLOSED; eassumption |exact MATCH]]. }
  destruct (gateway_actual_required_type_check backend ge property post object offset class class_offset before world events
    (Vint status) after next symbol definition CLOSED POST_CLOSED CONTEXT
    ltac:(intros memory current GOOD;
      destruct (gateway_validation_reachable_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD REACHED)
        as [ROOT [actual_description [actual_kind [actual_object [actual_offset [VALUE [ACTUAL_KIND [SAME POINTER]]]]]]]];
      inversion SAME; subst; exact POINTER)
    SYMBOL FUNCTION DEFINITION TYPE) as (prefix &suffix &called &owner &changed &following &returned &observed &parameters &
      EVENTS &SAME &POST &CALLED &TO_CALL &OPERATION &REST).
  - intros memory current result changed following observed GOOD OPERATION.
    destruct (gateway_validation_reachable_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD REACHED)
      as [ROOT [actual_description [actual_kind [actual_object [actual_offset [VALUE [ACTUAL_KIND [SAME POINTER]]]]]]]].
    assert (EXACT_VALUE : gateway_object_values (objects current) (Vptr object offset) = Some description).
    { rewrite (gateway_validation_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD) by exact REACHED; exact DESCRIPTION. }
    destruct (gateway_builtin_instance_operation _ _ _ _ _ instances memory current (Vptr object offset) description kind expected
      (Vptr class class_offset) result changed following observed
      (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD) ROOT EXACT_VALUE KIND CLASS OPERATION)
      as [returned [RESULT [CHECK [LEASES OBSERVER]]]].
    exists returned; split; [exact RESULT |].
    destruct (Int.eq_dec returned (Int.neg Int.one)) as [ERROR |NONERROR]; [left; exact ERROR |right].
    split.
    + eapply gateway_validation_context_observer; [exact GOOD |apply OBSERVER; exact NONERROR].
    + destruct (gateway_known_instance_result _ _ _ _ _ _ EXACT_VALUE KIND CHECK) as [MATCH |ERROR];
        [exact MATCH |contradiction].
  - exact RUN.
  - inversion SAME; subst returned; destruct POST as [ERROR |[GOOD MATCH]].
    + rewrite ERROR in POSITIVE; change (0 < -1) in POSITIVE; lia.
    + destruct (gateway_builtin_accepts expected kind) eqn:ACCEPT.
      * exact (conj GOOD (conj eq_refl MATCH)).
      * rewrite MATCH in POSITIVE; change (0 < 0) in POSITIVE; lia.
Qed.
