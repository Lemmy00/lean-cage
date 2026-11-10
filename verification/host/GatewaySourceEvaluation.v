(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source automation builds ordinary checked edge certificates. *)
From Stdlib Require Import List.
From compcert Require Import Maps AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySourcePaths GatewayFrames GatewayFramedRuntime.

(* The load tactic supplies proofs about exact current memory cells. This
   evaluator constructs expression certificates and never replaces Clight steps. *)
Ltac gateway_source_expression loads :=
  first[loads|
    lazymatch goal with
    | |- expression_value _ _ _ _ (Econst_int _ _) _=>apply old_expression_value;apply value_int
    | |- expression_value _ _ _ _ (Econst_long _ _) _=>
        fail "long literal requires its actual typed expression certificate"
    | |- expression_value _ _ _ _ (Etempvar _ _) _=>apply old_expression_value;apply value_temp;reflexivity
    | |- expression_value _ _ _ _ (Ebinop _ _ _ _) _=>
        eapply binary_expression_value;
          [gateway_source_expression loads|gateway_source_expression loads|reflexivity]
    | |- expression_value _ _ _ _ (Ecast _ _) _=>
        eapply cast_expression_value;[gateway_source_expression loads|reflexivity]
    | |- ?unknown=>fail 1 "unsupported source expression" unknown
    end].

Ltac gateway_source_to_call closed loads :=
  lazymatch goal with
  | |- gateway_source_path _ _ _ _ _ _ (State ?function ?body ?continuation ?environment ?temporaries ?memory) _=>
    let statement:=eval hnf in body in
    lazymatch statement with
    |(if ?flag then ?yes else ?no)=>
      let selected:=eval vm_compute in flag in
      lazymatch selected with
      |true=>change body with yes;gateway_source_to_call closed loads
      |false=>change body with no;gateway_source_to_call closed loads
      end
    |Ssequence ?first ?rest=>
      eapply gateway_source_same with(target:=State function first(Kseq rest continuation)environment temporaries memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|gateway_source_to_call closed loads]
    |Sskip=>
      lazymatch continuation with
      |Kseq ?following ?rest=>
        eapply gateway_source_same with(target:=State function following rest environment temporaries memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|gateway_source_to_call closed loads]
      |?unknown=>fail 1 "unsupported skip continuation" unknown
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_source_same with(target:=State function Sskip continuation environment(PTree.set identifier result temporaries)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_source_expression loads|gateway_source_to_call closed loads]
    |Sifthenelse ?expression ?yes ?no=>
      let flag:=open_constr:(_ : bool)in
      eapply gateway_source_same with(target:=State function(if flag then yes else no)continuation environment temporaries memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;
          [gateway_source_expression loads|reflexivity]|gateway_source_to_call closed loads]
    |Scall _ _ _=>idtac
    |?unknown=>fail 1 "unsupported source form" unknown
    end
  end.
