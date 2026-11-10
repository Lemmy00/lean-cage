(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Control automation constructs actual certified Clight edges. *)
From compcert Require Import Clight.
Require Import ClightSteps StoreSteps.
From HostGateway Require Import GatewaySourcePaths GatewaySourceSegments GatewayMachine.

Ltac gateway_path_seq closed :=
  lazymatch goal with
  | |-gateway_source_path _ _ _ _ _ _ (State ?f(Ssequence ?first ?rest)?k ?e ?le ?m)_ =>
    eapply gateway_source_same with(target:=State f first(Kseq rest k)e le m);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|]
  end.

Ltac gateway_path_skip closed :=
  lazymatch goal with
  | |-gateway_source_path _ _ _ _ _ _ (State ?f Sskip(Kseq ?rest ?k)?e ?le ?m)_ =>
    eapply gateway_source_same with(target:=State f rest k e le m);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|]
  end.

Ltac gateway_segment_seq closed :=
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (State ?f(Ssequence ?first ?rest)?k ?e ?le ?m)_ _ =>
    eapply gateway_segment_same with(next:=State f first(Kseq rest k)e le m);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|]
  end.

Ltac gateway_segment_skip closed :=
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (State ?f Sskip(Kseq ?rest ?k)?e ?le ?m)_ _ =>
    eapply gateway_segment_same with(next:=State f rest k e le m);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|]
  end.
