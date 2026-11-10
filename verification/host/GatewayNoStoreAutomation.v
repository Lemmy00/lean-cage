(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Build certificates from actual read-only source edges. *)
From compcert Require Import Maps AST Values Memory Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewayNoStoreControl GatewaySourceSegmentAutomation GatewayFramedRuntime.

(* This tactic constructs ordinary checked Clight edges. The supplied finalizer
   must discharge every SDK occurrence and selected branch; it assumes neither
   completion nor a future callback return. *)
Ltac gateway_nostore_dynamic closed loads reduce finish :=
  first [solve [finish ()] |
  lazymatch goal with
  | |- gateway_nostore_control _ _ _ (Returnstate ?value ?saved ?memory) =>
    let call_view := eval hnf in saved in
    lazymatch call_view with
    | Kcall ?destination ?function ?environment ?temporaries ?continuation =>
      eapply gateway_nostore_source_same with
        (target := State function Sskip continuation environment (set_opttemp destination value temporaries) memory);
        [exact closed |cbn; tauto |exact I |intros; apply unchanged_store_edge, edge_returnstate |
         gateway_nostore_dynamic closed loads reduce finish]
    end
  | |- gateway_nostore_control _ _ _
      (State ?function ?body ?continuation ?environment ?temporaries ?memory) =>
    let shape := eval hnf in body in
    lazymatch shape with
    | (if ?flag then ?yes else ?no) =>
      let selected := eval vm_compute in flag in
      lazymatch selected with
      | true => change body with yes; gateway_nostore_dynamic closed loads reduce finish
      | false => change body with no; gateway_nostore_dynamic closed loads reduce finish
      end
    | Ssequence ?first ?rest =>
      eapply gateway_nostore_source_same with
        (target := State function first (Kseq rest continuation) environment temporaries memory);
        [exact closed |cbn; tauto |exact I |intros; apply unchanged_store_edge, edge_seq |
         gateway_nostore_dynamic closed loads reduce finish]
    | Sskip =>
      let continuation_view := eval hnf in continuation in
      lazymatch continuation_view with
      | Kseq ?following ?rest =>
        eapply gateway_nostore_source_same with
          (target := State function following rest environment temporaries memory);
          [exact closed |cbn; tauto |exact I |intros; apply unchanged_store_edge, edge_skip_seq |
           gateway_nostore_dynamic closed loads reduce finish]
      end
    | Sset ?identifier ?expression =>
      let result_value := open_constr:(_ : Values.val) in
      eapply gateway_nostore_source_same with
        (target := State function Sskip continuation environment (PTree.set identifier result_value temporaries) memory);
        [exact closed |cbn; tauto |exact I |intros; apply certified_set_edge;
         gateway_segment_expression loads reduce |
         gateway_nostore_dynamic closed loads reduce finish]
    | Sifthenelse ?expression ?yes ?no =>
      let branch_value := open_constr:(_ : bool) in
      eapply gateway_nostore_source_same with
        (target := State function (if branch_value then yes else no) continuation environment temporaries memory);
        [exact closed |cbn; tauto |exact I |intros; eapply certified_if_edge;
         [gateway_segment_expression loads reduce |reduce ()] |
         gateway_nostore_dynamic closed loads reduce finish]
    | Scall _ _ _ => idtac
    end
  end].
