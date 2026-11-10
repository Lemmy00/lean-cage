(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Symbolic guards also produce checked actual-source certificates. *)
From Stdlib Require Import List.
From compcert Require Import Maps AST Values Memory Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySourcePaths GatewaySourceCuts GatewaySourceEvaluation GatewayFrames GatewayFramedRuntime
  GatewayFailurePaths.

Ltac gateway_source_dynamic_expression loads reduce :=
    lazymatch goal with
    | |- expression_value _ _ _ _ (Ebinop _ _ _ _) _=>
        eapply binary_expression_value;
          [gateway_source_dynamic_expression loads reduce|gateway_source_dynamic_expression loads reduce|reduce ()]
    | |- expression_value _ _ _ _ (Ecast _ _) _=>
        eapply cast_expression_value;[gateway_source_dynamic_expression loads reduce|reduce ()]
    | |- expression_value _ _ _ _ (Econst_int _ _) _=>apply old_expression_value;apply value_int
    | |- expression_value _ _ _ _ (Etempvar _ _) _=>
        apply old_expression_value;apply value_temp;unfold set_opttemp;
          repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|reflexivity|assumption]
    | |- _=>loads ()
    end.

Ltac gateway_source_dynamic_call closed loads reduce :=
  lazymatch goal with
  | |-gateway_source_path _ _ _ _ _ _ (Returnstate ?value ?saved ?memory) _=>
    let call:=eval hnf in saved in
    lazymatch call with
    |Kcall ?destination ?function ?environment ?temporaries ?continuation=>
      eapply gateway_source_same with(target:=State function Sskip continuation environment(set_opttemp destination value temporaries)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|gateway_source_dynamic_call closed loads reduce]
    end
  | |-gateway_source_path _ _ _ _ _ _ (State ?function ?body ?continuation ?environment ?temporaries ?memory) _=>
    let statement:=eval hnf in body in
    lazymatch statement with
    |(if ?flag then ?yes else ?no)=>
      let selected:=eval vm_compute in flag in
      lazymatch selected with
      |true=>change body with yes;gateway_source_dynamic_call closed loads reduce
      |false=>change body with no;gateway_source_dynamic_call closed loads reduce
      end
    |Ssequence ?first ?rest=>
      eapply gateway_source_same with(target:=State function first(Kseq rest continuation)environment temporaries memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|gateway_source_dynamic_call closed loads reduce]
    |Sskip=>
      lazymatch continuation with
      |Kseq ?following ?rest=>
        eapply gateway_source_same with(target:=State function following rest environment temporaries memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|gateway_source_dynamic_call closed loads reduce]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_source_same with(target:=State function Sskip continuation environment(PTree.set identifier result temporaries)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_source_dynamic_expression loads reduce|
          gateway_source_dynamic_call closed loads reduce]
    |Sifthenelse ?expression ?yes ?no=>
      let flag:=open_constr:(_ : bool)in
      eapply gateway_source_same with(target:=State function(if flag then yes else no)continuation environment temporaries memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;
          [gateway_source_dynamic_expression loads reduce|reduce ()]|gateway_source_dynamic_call closed loads reduce]
    |Scall _ _ _=>idtac
    end
  end.

Ltac gateway_source_dynamic_failure closed loads reduce pointer :=
  tryif solve[apply gateway_failure_when_selected;apply gateway_failure_selected;
    [exact pointer|cbn[gateway_must_null gateway_no_return];tauto|reflexivity]]then idtac else(
  lazymatch goal with
  | |-gateway_failure_when _ _ _ (Returnstate ?value ?saved ?memory)=>
    let call:=eval hnf in saved in
    lazymatch call with
    |Kcall ?destination ?function ?environment ?temporaries ?continuation=>
      eapply gateway_failure_when_same with(target:=State function Sskip continuation environment(set_opttemp destination value temporaries)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|
          gateway_source_dynamic_failure closed loads reduce pointer]
    end
  | |-gateway_failure_when _ _ _ (State ?function ?body ?continuation ?environment ?temporaries ?memory)=>
    let statement:=eval hnf in body in
    lazymatch statement with
    |(if ?flag then ?yes else ?no)=>
      let selected:=eval vm_compute in flag in
      lazymatch selected with
      |true=>change body with yes;gateway_source_dynamic_failure closed loads reduce pointer
      |false=>change body with no;gateway_source_dynamic_failure closed loads reduce pointer
      |?unknown=>fail 1 "source guard remains symbolic" unknown
      end
    |Ssequence ?first ?rest=>
      eapply gateway_failure_when_same with(target:=State function first(Kseq rest continuation)environment temporaries memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|
          gateway_source_dynamic_failure closed loads reduce pointer]
    |Sskip=>
      lazymatch continuation with
      |Kseq ?following ?rest=>
        eapply gateway_failure_when_same with(target:=State function following rest environment temporaries memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|
            gateway_source_dynamic_failure closed loads reduce pointer]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_failure_when_same with(target:=State function Sskip continuation environment(PTree.set identifier result temporaries)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_source_dynamic_expression loads reduce|
          gateway_source_dynamic_failure closed loads reduce pointer]
    |Sifthenelse ?expression ?yes ?no=>
      let flag:=open_constr:(_ : bool)in
      eapply gateway_failure_when_same with(target:=State function(if flag then yes else no)continuation environment temporaries memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;
          [gateway_source_dynamic_expression loads reduce|reduce ()]|
            gateway_source_dynamic_failure closed loads reduce pointer]
    |?unknown=>fail 1 "unsupported failure source" unknown
    end
  | |- ?unknown=>fail 1 "unsupported failure goal" unknown
  end).
