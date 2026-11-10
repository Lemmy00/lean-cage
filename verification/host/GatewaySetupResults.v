(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Setup consumers retain established result evidence. *)
From compcert Require Import AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewaySetupPaths GatewayFramedRuntime.

Theorem gateway_setup_post {World Event} (backend : gateway_backend World Event) ge result changed_result :
  (forall memory world, result memory world -> changed_result memory world) ->
  forall property source,
    gateway_setup_path backend ge result property source ->
    gateway_setup_path backend ge changed_result property source.
Proof.
  intro INCLUDED; fix IH 3; intros property source SCRIPT.
  destruct SCRIPT as [property memory CLOSED RESULT |
    property source FAILURE |
    property source target middle CLOSED INTERNAL EDGE SCRIPT |
    property external types result_type convention arguments continuation memory CLOSED OPERATION].
  - constructor; [exact CLOSED |intros before world GOOD; apply INCLUDED, RESULT; exact GOOD].
  - apply gateway_setup_failure; exact FAILURE.
  - eapply gateway_setup_next; [exact CLOSED |exact INTERNAL |exact EDGE |apply IH; exact SCRIPT].
  - eapply gateway_setup_external; [exact CLOSED |].
    intros before world returned after next observed GOOD STEP.
    destruct (OPERATION before world returned after next observed GOOD STEP) as [middle [READY REST]].
    exists middle; split; [exact READY |apply IH; exact REST].
Qed.
