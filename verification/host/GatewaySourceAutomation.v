(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Structural source certificates retain the same proof obligation. *)
From compcert Require Import Maps AST Values Memory Clight.
Require Import ClightSteps StoreSteps.
From HostGateway Require Import GatewaySourcePaths GatewayFramedRuntime.

(* This only constructs checked structural edges; it does not solve API calls,
   memory accesses, conditions, ownership or terminal application claims. *)
Ltac gateway_source_structure closed :=
  lazymatch goal with
  | |- gateway_source_path ?backend ?ge ?definition ?arguments ?sink ?property
      (State ?function ?body ?continuation ?environment ?temporaries ?memory) ?result =>
    let shape := eval hnf in body in
    lazymatch shape with
    | Ssequence ?first ?rest =>
      eapply gateway_source_same with
        (target := State function first (Kseq rest continuation) environment temporaries memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |]
    | Sskip =>
      let next := eval hnf in continuation in
      lazymatch next with
      | Kseq ?following ?rest =>
        eapply gateway_source_same with
          (target := State function following rest environment temporaries memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |]
      end
    end
  | |- gateway_source_path ?backend ?ge ?definition ?arguments ?sink ?property
      (Returnstate ?value (Kcall ?destination ?function ?environment ?temporaries ?continuation) ?memory) ?result =>
    eapply gateway_source_same with
      (target := State function Sskip continuation environment (set_opttemp destination value temporaries) memory);
      [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |]
  end.
