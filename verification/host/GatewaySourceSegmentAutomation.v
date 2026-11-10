(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Pure source segments stop at their specified actual boundary. *)
From compcert Require Import Maps AST Values Memory Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySourceSegments GatewaySourceDynamic GatewayFramedRuntime.

(* Initial symbolic temporaries need eassumption to instantiate their value.
   Each candidate still produces the ordinary checked expression certificate. *)
Ltac gateway_segment_expression loads reduce :=
  lazymatch goal with
  | |- expression_value _ _ _ _ (Ebinop _ _ _ _) _ =>
    eapply binary_expression_value;
      [gateway_segment_expression loads reduce |gateway_segment_expression loads reduce |reduce ()]
  | |- expression_value _ _ _ _ (Ecast _ _) _ =>
    eapply cast_expression_value; [gateway_segment_expression loads reduce |reduce ()]
  | |- expression_value _ _ _ _ (Econst_int _ _) _ => apply old_expression_value; apply value_int
  | |- expression_value _ _ _ _ (Etempvar _ _) _ =>
    apply old_expression_value; apply value_temp; unfold set_opttemp;
      repeat rewrite PTree.gso by discriminate;
      first [apply PTree.gss |reflexivity |eassumption]
  | |- _ => loads ()
  end.

Ltac gateway_segment_dynamic closed loads reduce :=
  tryif solve [apply gateway_segment_here] then idtac else
  lazymatch goal with
  | |- gateway_source_segment _ _ _ (Returnstate ?value ?saved ?memory) _ _ =>
    let call_view := eval hnf in saved in
    lazymatch call_view with
    | Kcall ?destination ?function ?environment ?temporaries ?continuation =>
      eapply gateway_segment_same with
        (next := State function Sskip continuation environment (set_opttemp destination value temporaries) memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |
         gateway_segment_dynamic closed loads reduce]
    end
  | |- gateway_source_segment _ _ _
      (State ?function ?body ?continuation ?environment ?temporaries ?memory) _ _ =>
    let shape := eval hnf in body in
    lazymatch shape with
    | (if ?flag then ?yes else ?no) =>
      let selected := eval vm_compute in flag in
      lazymatch selected with
      | true => change body with yes; gateway_segment_dynamic closed loads reduce
      | false => change body with no; gateway_segment_dynamic closed loads reduce
      end
    | Ssequence ?first ?rest =>
      eapply gateway_segment_same with
        (next := State function first (Kseq rest continuation) environment temporaries memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |
         gateway_segment_dynamic closed loads reduce]
    | Sskip =>
      let continuation_view := eval hnf in continuation in
      lazymatch continuation_view with
      | Kseq ?following ?rest =>
        eapply gateway_segment_same with
          (next := State function following rest environment temporaries memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |
           gateway_segment_dynamic closed loads reduce]
      end
    | Sset ?identifier ?expression =>
      let result_value := open_constr:(_ : Values.val) in
      eapply gateway_segment_same with
        (next := State function Sskip continuation environment (PTree.set identifier result_value temporaries) memory);
        [exact closed |cbn; tauto |intros; apply certified_set_edge;
         gateway_segment_expression loads reduce |
         gateway_segment_dynamic closed loads reduce]
    | Sifthenelse ?expression ?yes ?no =>
      let branch_value := open_constr:(_ : bool) in
      eapply gateway_segment_same with
        (next := State function (if branch_value then yes else no) continuation environment temporaries memory);
        [exact closed |cbn; tauto |intros; eapply certified_if_edge;
         [gateway_segment_expression loads reduce |reduce ()] |
         gateway_segment_dynamic closed loads reduce]
    end
  end.
