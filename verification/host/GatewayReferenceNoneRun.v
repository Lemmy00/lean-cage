(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real singleton call creates its selected retained reference. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectConstants
  GatewayObjectDiscipline GatewayObjectThreads GatewayObjectExecution GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceIncref GatewayReturnRuntime GatewayReadonly
  GatewayLocalRuntime GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_none_run {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation decimal_float
    (runtime:gateway_thread_runtime backend io(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger owner held none environment before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_held python objects decimal_float ledger held world->
  gateway_none_runtime python objects none->
  gateway_return_environment(fun world object=>gateway_native_private(python world)object)
    (gateway_python_discipline python objects detached)None environment before world->
  gateway_steps backend ge(gateway_live(Callstate python_incref_definition[none]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner none)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)none /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=none;
        gateway_held_view:=gateway_held_scalar_value gateway_none_object|}])next /\
    gateway_return_environment(fun world object=>gateway_native_private(python world)object)
      (gateway_python_discipline python objects detached)None environment after next.
Proof.
  intros FORMED FIT VACANT HELD CONSTANTS ENV RUN.
  set(native:=fun world object=>gateway_native_private(python world)object).
  set(base:=gateway_python_discipline python objects detached).
  set(ready:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_reference_scope python objects decimal_float ledger held current).
  assert(CLOSED:gateway_ambient_closed backend ready).
  { intros first current last following[[SIDE OWNED]SCOPE]INTERFERENCE;split.
    - eapply gateway_return_environment_ambient;[exact runtime|exact(conj SIDE OWNED)|exact INTERFERENCE].
    - eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
      eapply gateway_reference_thread_ambient;[exact reference_threads|exact SIDE|exact INTERFERENCE]. }
  destruct(gateway_actual_object_operation backend ge gateway_api_incref python_incref_definition[none]ready before world events
    result after next eq_refl CLOSED(conj ENV(conj FIT HELD))RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &READY &OPERATION &PREFIX &SUFFIX).
  destruct READY as[[SIDE OWNED][CALLED_FIT CALLED_HELD]].
  destruct(gateway_none_identity _ _ _ CONSTANTS _ _ SIDE)as[LIVE[VALUE PRIVATE]].
  destruct(gateway_reference_incref_held backend python objects decimal_float references ledger owner held none gateway_none_object
    gateway_none_kind called called_world result changed changed_world observed FORMED CALLED_FIT VACANT CALLED_HELD
    SIDE LIVE VALUE PRIVATE eq_refl eq_refl ltac:(left;reflexivity)OPERATION)
    as[final[MINT[WELL[COUNTS[CAPTURED[AFTER_HELD[AFTER_READY RETURN]]]]]]].
  assert(ENVIRONMENT:gateway_native_environment native changed_world changed environment).
  { intros identifier object ty LOOK;destruct(OWNED identifier object ty LOOK)as[VALID NATIVE];split.
    - eapply Mem.valid_block_unchanged_on;
        [eapply gateway_incref_native_frame;[exact SIDE|exact RETURN]|exact VALID].
    - unfold native,gateway_native_private in *;rewrite(python_incref_heap _ _ _ _ _ RETURN);exact NATIVE. }
  set(captured:={|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=none;
    gateway_held_view:=gateway_held_scalar_value gateway_none_object|}).
  set(final_ready:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_reference_scope python objects decimal_float final(held++[captured])current).
  assert(FINAL_CLOSED:gateway_ambient_closed backend final_ready).
  { intros first current last following[[SIDE_NOW ENV_NOW]SCOPE]INTERFERENCE;split.
    - eapply gateway_return_environment_ambient;[exact runtime|exact(conj SIDE_NOW ENV_NOW)|exact INTERFERENCE].
    - eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
      eapply gateway_reference_thread_ambient;[exact reference_threads|exact SIDE_NOW|exact INTERFERENCE]. }
  assert(FINAL:final_ready after next).
  { eapply(gateway_readonly_run_side backend ge final_ready FINAL_CLOSED(Returnstate result Kstop changed)changed_world
      suffix result after next);[exact I|exact(conj(conj AFTER_READY ENVIRONMENT)(conj COUNTS AFTER_HELD))|exact SUFFIX]. }
  exists final;exact(conj MINT(conj WELL(conj CAPTURED(conj(proj2 FINAL)(proj1 FINAL))))).
Qed.
