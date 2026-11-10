(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An actual source null barrier survives arbitrary ignored
   callbacks, memory effects, interleaving and loss in its same continuation. *)
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayFailurePaths.

Theorem gateway_actual_null_context {World Event}(backend:gateway_backend World Event)ge source world events value after next:
  gateway_null_source source->
  gateway_steps backend ge(gateway_live source world)events(gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intros GOOD RUN;change(gateway_null_state(gateway_live source world))in GOOD.
  assert(FINAL:gateway_null_state(gateway_live(Returnstate value Kstop after)next)).
  { revert GOOD;induction RUN;intros GOOD;[exact GOOD|apply IHRUN;eapply gateway_null_step;eassumption]. }
  cbn in FINAL;tauto.
Qed.

Lemma gateway_null_context_replace source memory:
  gateway_null_source source->gateway_null_source(gateway_replace_memory source memory).
Proof. destruct source;cbn;auto. Qed.
Theorem gateway_failure_null_context {World Event}(backend:gateway_backend World Event)ge source:
  gateway_null_source source->gateway_failure_result backend ge source.
Proof.
  intros GOOD before world events value after next RUN.
  eapply gateway_actual_null_context;[apply gateway_null_context_replace;exact GOOD|exact RUN].
Qed.
