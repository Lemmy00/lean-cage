(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: The allocation-identity ABI never regrants an old cell;
   application source, bytes, errors, revocation, blocked calls and loss remain explicit. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayPermissionScopes GatewayPermissionSurvival.
Import ListNotations.

Record gateway_allocation_lifetime_runtime {World Event}(backend:gateway_backend World Event):Prop:={
  gateway_lifetime_external:forall ef types result_type convention arguments before world result after next observed,
    gateway_external backend ef types result_type convention arguments before world result after next observed->
    gateway_permission_survival before after;
  gateway_lifetime_builtin:forall ef types arguments before world result after next observed,
    gateway_builtin backend ef types arguments before world result after next observed->
    gateway_permission_survival before after;
  gateway_lifetime_ambient:forall before world after next,
    gateway_interference backend before world after next->gateway_permission_survival before after
}.

Definition gateway_state_memory {World}(state:gateway_state World):mem:=
  match state with gateway_live source _=>memory_of source|gateway_dead memory _=>memory end.

Theorem gateway_actual_step_permissions {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (runtime:gateway_allocation_lifetime_runtime backend)first observed last:
  gateway_step backend ge first observed last->
  gateway_permission_survival(gateway_state_memory first)(gateway_state_memory last).
Proof.
  intro STEP;inversion STEP;subst;cbn[gateway_state_memory memory_of].
  - eapply gateway_internal_permission_survival;eassumption.
  - eapply gateway_lifetime_external;[exact runtime|eassumption].
  - eapply gateway_lifetime_builtin;[exact runtime|eassumption].
  - destruct source;cbn[gateway_replace_memory memory_of];eapply gateway_lifetime_ambient;eauto.
  - apply gateway_survival_refl.
  - apply gateway_survival_refl.
  - eapply gateway_lifetime_external;[exact runtime|eassumption].
  - eapply gateway_lifetime_builtin;[exact runtime|eassumption].
Qed.

Theorem gateway_actual_run_permissions {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (runtime:gateway_allocation_lifetime_runtime backend)first events last:
  gateway_steps backend ge first events last->
  gateway_permission_survival(gateway_state_memory first)(gateway_state_memory last).
Proof.
  intro RUN;induction RUN;[apply gateway_survival_refl|].
  eapply gateway_survival_trans;[eapply gateway_actual_step_permissions;[exact runtime|exact H]|exact IHRUN].
Qed.

Theorem gateway_actual_return_permissions {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (runtime:gateway_allocation_lifetime_runtime backend)source world events value after next protected:
  gateway_steps backend ge(gateway_live source world)events(gateway_live(Returnstate value Kstop after)next)->
  (forall object position,protected object position->exists kind permission,Mem.perm after object position kind permission)->
  gateway_permission_frame protected(memory_of source)after.
Proof.
  intros RUN OBSERVED;eapply gateway_survival_observed_permissions;[|exact OBSERVED].
  exact(gateway_actual_run_permissions backend ge runtime _ _ _ RUN).
Qed.
