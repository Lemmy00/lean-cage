(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Bind symbolic source temporaries before selecting the real call. *)
From compcert Require Import Maps AST Values Memory Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySourcePaths GatewaySourceSegmentAutomation GatewayFramedRuntime GatewaySourceCuts GatewayFailurePaths.

(* Same checked source-path constructors as SourceDynamic; the shared expression
   certificates additionally instantiate a symbolic saved temporary's value. *)
Ltac gateway_bound_source_call closed loads reduce :=
  lazymatch goal with
  | |- gateway_source_path _ _ _ _ _ _ (Returnstate ?value ?saved ?memory) _ =>
    let call := eval hnf in saved in lazymatch call with
    | Kcall ?destination ?function ?environment ?parameters ?continuation =>
      eapply gateway_source_same with (target := State function Sskip continuation environment (set_opttemp destination value parameters) memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |
         gateway_bound_source_call closed loads reduce]
    end
  | |- gateway_source_path _ _ _ _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory) _ =>
    let statement := eval hnf in body in lazymatch statement with
    | (if ?flag then ?yes else ?no) =>
      let selected := eval vm_compute in flag in lazymatch selected with
      | true => change body with yes; gateway_bound_source_call closed loads reduce
      | false => change body with no; gateway_bound_source_call closed loads reduce
      end
    | Ssequence ?first ?rest =>
      eapply gateway_source_same with (target := State function first (Kseq rest continuation) environment parameters memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |
         gateway_bound_source_call closed loads reduce]
    | Sskip => lazymatch continuation with
      | Kseq ?following ?rest =>
        eapply gateway_source_same with (target := State function following rest environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |
           gateway_bound_source_call closed loads reduce]
      end
    | Sset ?identifier ?expression =>
      let result := open_constr:(_ : Values.val) in
      eapply gateway_source_same with (target := State function Sskip continuation environment (PTree.set identifier result parameters) memory);
        [exact closed |cbn; tauto |intros; apply certified_set_edge; gateway_segment_expression loads reduce |
         gateway_bound_source_call closed loads reduce]
    | Sifthenelse ?expression ?yes ?no =>
      let flag := open_constr:(_ : bool) in
      eapply gateway_source_same with (target := State function (if flag then yes else no) continuation environment parameters memory);
        [exact closed |cbn; tauto |intros; eapply certified_if_edge;
         [gateway_segment_expression loads reduce |reduce ()] |
         gateway_bound_source_call closed loads reduce]
    | Scall _ _ _ => idtac
    end
  end.

(* Retain the same actual failure paths with symbolic temporary certificates. *)
Ltac gateway_bound_source_failure closed loads reduce pointer :=
  tryif solve[apply gateway_failure_when_selected;apply gateway_failure_selected;
    [exact pointer|first [solve[cbn[gateway_must_null gateway_no_return];tauto]|
      solve[vm_compute;auto]]|reflexivity]]then idtac else(
  lazymatch goal with
  | |-gateway_failure_when _ _ _ (Returnstate ?value ?saved ?memory)=>
    let call:=eval hnf in saved in
    lazymatch call with
    |Kcall ?destination ?function ?environment ?temporaries ?continuation=>
      eapply gateway_failure_when_same with(target:=State function Sskip continuation environment(set_opttemp destination value temporaries)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|
          gateway_bound_source_failure closed loads reduce pointer]
    end
  | |-gateway_failure_when _ _ _ (State ?function ?body ?continuation ?environment ?temporaries ?memory)=>
    let statement:=eval hnf in body in
    lazymatch statement with
    |(if ?flag then ?yes else ?no)=>
      let selected:=eval vm_compute in flag in
      lazymatch selected with
      |true=>change body with yes;gateway_bound_source_failure closed loads reduce pointer
      |false=>change body with no;gateway_bound_source_failure closed loads reduce pointer
      |?unknown=>fail 1 "source guard remains symbolic" unknown
      end
    |Ssequence ?first ?rest=>
      eapply gateway_failure_when_same with(target:=State function first(Kseq rest continuation)environment temporaries memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|
          gateway_bound_source_failure closed loads reduce pointer]
    |Sskip=>
      lazymatch continuation with
      |Kseq ?following ?rest=>
        eapply gateway_failure_when_same with(target:=State function following rest environment temporaries memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|
            gateway_bound_source_failure closed loads reduce pointer]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_failure_when_same with(target:=State function Sskip continuation environment(PTree.set identifier result temporaries)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_segment_expression loads reduce|
          gateway_bound_source_failure closed loads reduce pointer]
    |Sifthenelse ?expression ?yes ?no=>
      let flag:=open_constr:(_ : bool)in
      eapply gateway_failure_when_same with(target:=State function(if flag then yes else no)continuation environment temporaries memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;
          [gateway_segment_expression loads reduce|reduce ()]|
            gateway_bound_source_failure closed loads reduce pointer]
    |?unknown=>fail 1 "unsupported failure source" unknown
    end
  | |- ?unknown=>fail 1 "unsupported failure goal" unknown
  end).
