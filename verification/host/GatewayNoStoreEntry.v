(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual local-free entry retains the same source guard. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayNoStoreControl GatewayNoLocalEntry GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_nostore_local_free_entry {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) function arguments memory :
  fn_vars function = [] -> gateway_ambient_closed backend property ->
  (forall parameters memory, gateway_nostore_control backend ge property
    (State function (fn_body function) Kstop empty_env parameters memory)) ->
  gateway_nostore_control backend ge property (Callstate (Internal function) arguments Kstop memory).
Proof.
  intros LOCALS CLOSED BODY; apply gateway_nostore_source; [exact CLOSED |cbn; tauto |exact I |].
  intros before world observed target READY STEP; inversion STEP; subst.
  match goal with ENTRY : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (gateway_no_local_entry _ _ _ _ _ _ _ LOCALS ENTRY) as [ENVIRONMENT ALLOCATION];
    subst end.
  exists property; split; [exact READY |apply BODY].
Qed.
