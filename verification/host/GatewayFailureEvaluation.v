(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Guard evaluation constructs prefix-preserving source failure certificates. *)
From Stdlib Require Import List.
From compcert Require Import Maps AST Values Memory Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySourceDynamic GatewayFailureControl GatewayFailurePaths.

Lemma gateway_failure_control_statement {World Event}(backend:GatewayMachine.gateway_backend World Event)ge property
    function statement continuation environment parameters memory :
  gateway_pointer_return function ->gateway_must_null statement ->call_cont continuation=Kstop ->
  gateway_failure_control backend ge property(State function statement continuation environment parameters memory).
Proof.
  intros POINTER MUST STOP;apply gateway_failure_control_selected;left.
  split;[exact POINTER|]. split;[exact STOP|left;exact MUST].
Qed.

Ltac gateway_source_failure_control closed loads reduce pointer :=
  tryif solve[apply gateway_failure_control_statement;
    [exact pointer|cbn[gateway_must_null gateway_no_return];tauto|reflexivity]]then idtac else(
  lazymatch goal with
  | |-gateway_failure_control _ _ _ (Returnstate ?value ?saved ?memory)=>
    let call:=eval hnf in saved in
    lazymatch call with
    |Kcall ?destination ?function ?environment ?temporaries ?continuation=>
      eapply gateway_failure_control_same with(target:=State function Sskip continuation environment(set_opttemp destination value temporaries)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|
          gateway_source_failure_control closed loads reduce pointer]
    end
  | |-gateway_failure_control _ _ _ (State ?function ?body ?continuation ?environment ?temporaries ?memory)=>
    let statement:=eval hnf in body in
    lazymatch statement with
    |(if ?flag then ?yes else ?no)=>
      let selected:=eval vm_compute in flag in
      lazymatch selected with
      |true=>change body with yes;gateway_source_failure_control closed loads reduce pointer
      |false=>change body with no;gateway_source_failure_control closed loads reduce pointer
      |?unknown=>fail 1 "source guard remains symbolic" unknown
      end
    |Ssequence ?first ?rest=>
      eapply gateway_failure_control_same with(target:=State function first(Kseq rest continuation)environment temporaries memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|
          gateway_source_failure_control closed loads reduce pointer]
    |Sskip=>
      lazymatch continuation with
      |Kseq ?following ?rest=>
        eapply gateway_failure_control_same with(target:=State function following rest environment temporaries memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|
            gateway_source_failure_control closed loads reduce pointer]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_failure_control_same with(target:=State function Sskip continuation environment(PTree.set identifier result temporaries)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_source_dynamic_expression loads reduce|
          gateway_source_failure_control closed loads reduce pointer]
    |Sifthenelse ?expression ?yes ?no=>
      let flag:=open_constr:(_ : bool)in
      eapply gateway_failure_control_same with(target:=State function(if flag then yes else no)continuation environment temporaries memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;
          [gateway_source_dynamic_expression loads reduce|reduce ()]|
            gateway_source_failure_control closed loads reduce pointer]
    |?unknown=>fail 1 "unsupported failure source" unknown
    end
  | |- ?unknown=>fail 1 "unsupported failure goal" unknown
  end).
