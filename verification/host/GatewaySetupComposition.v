(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source cuts compose with their actual setup continuation. *)
From compcert Require Import AST Values Memory Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewaySourcePaths GatewaySetupPaths GatewayFramedRuntime GatewaySourceSegments.

Theorem gateway_setup_after_source {World Event} (backend : gateway_backend World Event) ge
    definition arguments continuation boundary property source result :
  gateway_source_path backend ge definition arguments continuation property source boundary ->
  gateway_ambient_closed backend property -> gateway_ambient_closed backend boundary ->
  (forall memory, gateway_setup_path backend ge result boundary
    (Callstate definition arguments continuation memory)) ->
  gateway_setup_path backend ge result property source.
Proof.
  intro SCRIPT.
  induction SCRIPT as [first memory last INCLUDED |
    first source target middle last AMBIENT INTERNAL EDGE SCRIPT IH];
    intros CLOSED BOUNDARY NEXT.
  - eapply gateway_setup_pre; [apply NEXT |exact CLOSED |exact INCLUDED].
  - destruct SCRIPT as [tail_property memory tail_result INCLUDED |
      tail_property tail_source tail_target tail_middle tail_result TAIL_CLOSED TAIL_INTERNAL
      TAIL_EDGE TAIL_SCRIPT].
    + eapply gateway_setup_next with
        (next := Callstate definition arguments continuation memory) (middle := tail_result).
      * exact CLOSED.
      * exact INTERNAL.
      * intros before world GOOD.
        destruct (EDGE before world GOOD) as [after [REAL MIDDLE]].
        exists after; split; [exact REAL |eapply INCLUDED; exact MIDDLE].
      * apply NEXT.
    + eapply gateway_setup_next; [exact CLOSED |exact INTERNAL |exact EDGE |].
      apply IH; [exact TAIL_CLOSED |exact BOUNDARY |exact NEXT].
Qed.

Ltac gateway_setup_structure closed :=
  lazymatch goal with
  | |- gateway_setup_path ?backend ?ge ?result ?property
      (State ?function ?body ?continuation ?environment ?temporaries ?memory) =>
    let shape := eval hnf in body in
    lazymatch shape with
    | Ssequence ?first ?rest =>
      eapply gateway_setup_same with
        (next := State function first (Kseq rest continuation) environment temporaries memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |]
    | Sskip =>
      let continuation_view := eval hnf in continuation in
      lazymatch continuation_view with
      | Kseq ?following ?rest =>
        eapply gateway_setup_same with
          (next := State function following rest environment temporaries memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |]
      end
    end
  | |- gateway_setup_path ?backend ?ge ?result ?property (Returnstate ?value ?saved ?memory) =>
    let call_view := eval hnf in saved in
    lazymatch call_view with
    | Kcall ?destination ?function ?environment ?temporaries ?continuation =>
      eapply gateway_setup_same with
        (next := State function Sskip continuation environment (set_opttemp destination value temporaries) memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |]
    end
  end.

Theorem gateway_setup_after_segment {World Event} (backend : gateway_backend World Event) ge
    property source boundary middle result :
  gateway_source_segment backend ge property source boundary middle ->
  gateway_setup_path backend ge result middle boundary ->
  gateway_setup_path backend ge result property source.
Proof.
  intros SCRIPT; induction SCRIPT; intro REST; [exact REST |].
  eapply gateway_setup_next; [exact H |exact H0 |exact H1 |apply IHSCRIPT; exact REST].
Qed.
