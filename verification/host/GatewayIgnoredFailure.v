(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Ignored SDK results do not erase the original caller's failure. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayCalls GatewayInstructions GatewayFailurePaths.

Theorem gateway_failure_ignored_call {World Event}(backend:gateway_backend World Event)ge
    function expression arguments continuation environment temporaries memory:
  (forall returned,gateway_failure_result backend ge
    (Returnstate returned(Kcall None function environment temporaries continuation)memory))->
  gateway_failure_result backend ge(State function(Scall None expression arguments)continuation environment temporaries memory).
Proof.
  intros FAILURE before world events value after next RUN.
  destruct(gateway_source_call_occurrence backend ge function None expression arguments continuation environment temporaries
    before world events value after next RUN)
    as(prefix&suffix&called&called_world&definition&values&EVENTS&AMBIENT&PREFIX&CALL&REST).
  destruct(gateway_return_cut backend ge definition values(Kcall None function environment temporaries continuation)
    called called_world suffix(Returnstate value Kstop after)next I ltac:(cbn;lia)REST)
    as(body&following&returned&returned_memory&returned_world&SUFFIX&BODY&FOLLOWING).
  exact(FAILURE returned returned_memory returned_world following value after next FOLLOWING).
Qed.

Theorem gateway_failure_arbitrary_set {World Event}(backend:gateway_backend World Event)ge
    function identifier expression continuation environment temporaries memory:
  (forall assigned,gateway_failure_result backend ge
    (State function Sskip continuation environment(PTree.set identifier assigned temporaries)memory))->
  gateway_failure_result backend ge(State function(Sset identifier expression)continuation environment temporaries memory).
Proof.
  intros FAILURE before world events value after next RUN.
  destruct(gateway_set_result_cut backend ge function identifier expression continuation environment temporaries
    before world events value after next RUN)
    as(prefix&suffix&called&called_world&assigned&EVENTS&AMBIENT&PREFIX&EXPRESSION&REST).
  exact(FAILURE assigned called called_world suffix value after next REST).
Qed.
