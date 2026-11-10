(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A selected real container constructor mints one source ticket and
   keeps the guarded count and earlier private graphs. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayImport GatewayValue GatewayValueOwnership GatewayValueFrame GatewayObjectThreads GatewayObjectDiscipline
  GatewayContainerLength GatewayContainerGuards GatewayContainerAllocation GatewayContainerMemory
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceConstructors GatewayReferenceContainerScope GatewayOperations GatewayObjectExecution GatewayReadonly
  GatewayReturnRuntime GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_container_empty_value container:=
  match container with gateway_container_array=>gateway_list_object[]|gateway_container_object=>gateway_dict_object[]end.
Definition gateway_container_empty_wire container:=
  match container with
  |gateway_container_array=>LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values[])
  |gateway_container_object=>LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields[])
  end.
Definition gateway_container_builtin_kind container:=
  match container with gateway_container_array=>gateway_list_kind|gateway_container_object=>gateway_dict_kind end.

Lemma gateway_container_empty_request decimal_float heap memory container:
  gateway_constructor_request decimal_float heap memory(gateway_container_api container)
    (gateway_container_constructor_values container)(gateway_container_empty_value container).
Proof. destruct container;constructor. Qed.
Lemma gateway_container_empty_semantics decimal_float heap pointer container:
  gateway_object_values heap pointer=Some(gateway_container_empty_value container)->
  gateway_value_heap decimal_float heap pointer(gateway_container_empty_wire container).
Proof.
  destruct container;intro LOOKUP;[apply gateway_heap_array with(objects:=[])|apply gateway_heap_dictionary with(fields:=[])];
    [exact LOOKUP|constructor|exact LOOKUP|constructor].
Qed.

Theorem gateway_reference_actual_container_allocation {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    ledger owner held container definition slots stream_block stream_offset initial readonly original size
    before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_object_api_definition(gateway_container_api container)=Some definition->
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original size before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_steps backend ge(gateway_live(Callstate definition(gateway_container_constructor_values container)Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_wire_capture(gateway_reference_next ledger)result(gateway_container_empty_wire container)])next /\
    gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original size after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    (forall captured,In captured held->~gateway_object_reachable(objects next)(gateway_held_object captured)result).
Proof.
  intros FORMED VACANT SCOPE DEFINITION INPUT READONLY RUN NONNULL.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(counted:=gateway_container_counted native stable base container slots stream_block stream_offset initial readonly original size).
  set(input:=fun memory current=>counted memory current /\gateway_reference_scope python objects decimal_float ledger held current /\
    (forall candidate position,readonly candidate position->native current candidate)).
  pose proof(gateway_container_counted_ambient backend io native stable base thread_errno runtime container slots stream_block stream_offset
    initial readonly original size)as COUNTED_CLOSED.
  assert(INPUT_CLOSED:gateway_ambient_closed backend input).
  { intros first current last following[COUNTED[HOLD NATIVE]]INTERFERENCE;split.
    - eapply COUNTED_CLOSED;eassumption.
    - split.
      + eapply gateway_reference_scope_thread_effect;[exact HOLD|].
        eapply gateway_reference_thread_ambient;[exact reference_threads|ltac:(eapply gateway_container_counted_side;exact COUNTED)|exact INTERFERENCE].
      + intros candidate position READ.
        pose proof(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ ltac:(eapply gateway_container_counted_side;exact COUNTED)INTERFERENCE)as[SIDE[[RETAIN STABLE]FRAME]].
        apply RETAIN;[|apply NATIVE with(position:=position);exact READ].
        eapply gateway_container_counted_readonly_live;[exact COUNTED|exact READ]. }
  destruct(gateway_actual_object_operation backend ge(gateway_container_api container)definition
    (gateway_container_constructor_values container)input before world events result after next DEFINITION INPUT_CLOSED
    (conj INPUT(conj SCOPE READONLY))RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[CALLED[HELD NATIVE]]&OPERATION &PREFIX &SUFFIX).
  assert(READY:base None called called_world)by(eapply gateway_container_counted_side;exact CALLED).
  assert(REQUEST:gateway_constructor_request decimal_float(objects called_world)called(gateway_container_api container)
    (gateway_container_constructor_values container)(gateway_container_empty_value container))by(apply gateway_container_empty_request).
  assert(ROOTS:gateway_constructor_roots(python called_world)(objects called_world)(gateway_container_api container)
    (gateway_container_constructor_values container))by(destruct container;exact I).
  pose proof(gateway_runtime_constructor _ _ _ _ constructors _ _ _ _ _ _ _ _ _ READY REQUEST ROOTS OPERATION NONNULL)as RETURN.
  destruct(gateway_reference_constructed_held python objects decimal_float ledger owner held called called_world result changed changed_world
    (gateway_container_empty_value container)(gateway_container_builtin_kind container)FORMED(proj1 HELD)VACANT(proj2 HELD)RETURN
    ltac:(destruct container;reflexivity)ltac:(destruct container;reflexivity)
    ltac:(destruct container;unfold gateway_destructor_kind;auto 9))
    as[final[MINT[WELL[FIT[OWNED[CAPTURED DISTINCT]]]]]].
  assert(OLD_HELD:gateway_reference_scope python objects decimal_float final held changed_world).
  { split;[exact FIT|]. apply Forall_app in CAPTURED;exact(proj1 CAPTURED). }
  assert(PRIVATE:gateway_private_tree(objects changed_world)result).
  { eapply gateway_leaf_private;[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|destruct container;reflexivity|
      exact(gateway_constructor_private _ _ _ _ _ _ _ _ RETURN)]. }
  assert(DESTROY:gateway_destructible(objects changed_world)result).
  { eapply gateway_leaf_destructible with(kind:=gateway_container_builtin_kind container);[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|destruct container;reflexivity|
      destruct container;reflexivity|destruct container;unfold gateway_destructor_kind;auto 9]. }
  set(captured:=gateway_reference_wire_capture(gateway_reference_next ledger)result(gateway_container_empty_wire container)).
  assert(HELD_AFTER:gateway_reference_scope python objects decimal_float final(held++[captured])changed_world).
  { eapply gateway_reference_add_wire_capture;[exact OLD_HELD|exact OWNED|exact PRIVATE|exact DESTROY|].
    apply gateway_container_empty_semantics;exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN). }
  assert(OUTSIDE:forall previous,In previous held->~gateway_object_reachable(objects changed_world)(gateway_held_object previous)result).
  { intros previous MEMBER REACHED.
    destruct(gateway_reference_capture_member _ _ _ _ _ _ _ HELD MEMBER)as[[place OLD_OWNED][OLD_PRIVATE[OLD_DESTROY OLD_VALUE]]].
    assert(OLD_ROOT:gateway_rooted(python called_world)(objects called_world)(gateway_held_object previous)).
    { eapply gateway_reference_owned_rooted;[exact(proj1 HELD)|exact OLD_OWNED]. }
    destruct(gateway_constructor_all_private_frames _ _ _ _ _ _ _ _ RETURN)as[FRAME PRIVACY].
    assert(NEXT_ROOT:gateway_rooted(python changed_world)(objects changed_world)(gateway_held_object previous)).
    { destruct(gateway_reference_capture_member _ _ _ _ _ _ _ OLD_HELD MEMBER)as[[next_place NEXT_OWNED]REST].
      eapply gateway_reference_owned_rooted;[exact FIT|exact NEXT_OWNED]. }
    apply(gateway_new_container_outside_old_graph _ _ _ _ _ _ _ _ _ RETURN READY
      ltac:(destruct container;exact I)OLD_ROOT).
    eapply gateway_private_tree_reachable_back;[exact OLD_PRIVATE|exact OLD_DESTROY|exact OLD_ROOT|exact NEXT_ROOT|exact FRAME|exact PRIVACY|exact REACHED]. }
  destruct(gateway_container_constructor_retains backend python objects detached io stable thread_errno runtime container slots stream_block stream_offset
    initial readonly original size called called_world result changed changed_world(gateway_container_empty_value container)CALLED NATIVE RETURN)
    as[COUNTED_AFTER NATIVE_AFTER].
  set(output:=fun memory current=>counted memory current /\
    gateway_reference_scope python objects decimal_float final(held++[captured])current /\
    (forall candidate position,readonly candidate position->native current candidate) /\
    (forall previous,In previous held->~gateway_object_reachable(objects current)(gateway_held_object previous)result)).
  assert(OUTPUT_CLOSED:gateway_ambient_closed backend output).
  { intros first current last following[COUNTED[HOLD[NATIVE0 OUTSIDE0]]]INTERFERENCE.
    pose proof(gateway_reference_thread_ambient _ _ _ _ _ _ _ reference_threads None first current last following
      ltac:(eapply gateway_container_counted_side;exact COUNTED)INTERFERENCE)as EFFECT.
    split;[eapply COUNTED_CLOSED;eassumption|]. split;[eapply gateway_reference_scope_thread_effect;eassumption|]. split.
    - pose proof(INPUT_CLOSED first current last following)as RETAIN.
      intros candidate position READ.
      pose proof(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ ltac:(eapply gateway_container_counted_side;exact COUNTED)INTERFERENCE)
        as[SIDE[[NATIVE_RETAIN STABLE]FRAME]].
      apply NATIVE_RETAIN;[|apply NATIVE0 with(position:=position);exact READ].
      eapply gateway_container_counted_readonly_live;[exact COUNTED|exact READ].
    - intros previous MEMBER;eapply gateway_reference_thread_keeps_graph_exclusion;
        [exact HOLD|apply in_or_app;left;exact MEMBER|apply OUTSIDE0;exact MEMBER|exact EFFECT]. }
  pose proof(gateway_readonly_run_side backend ge output OUTPUT_CLOSED(Returnstate result Kstop changed)changed_world
    suffix result after next I(conj COUNTED_AFTER(conj HELD_AFTER(conj NATIVE_AFTER OUTSIDE)))SUFFIX)
    as[FINAL_COUNTED[FINAL_SCOPE[FINAL_NATIVE FINAL_OUTSIDE]]].
  exists final;exact(conj MINT(conj WELL(conj OWNED(conj FINAL_SCOPE(conj FINAL_COUNTED(conj FINAL_NATIVE FINAL_OUTSIDE)))))).
Qed.
