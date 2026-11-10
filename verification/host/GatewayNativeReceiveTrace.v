(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Actual C receive events select their own rows in one global history. *)
From Stdlib Require Import ZArith List Lia Sorting.Sorted.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayStreamInterface
  GatewayNativeImport GatewayNativeWords GatewayNativeRows GatewayNativeCallOperands GatewayNativeStreamObservation
  GatewaySpawnHistory.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Definition gateway_direct_receive {Event} (io : Event -> option gateway_native_io)
    (event : gateway_event Event) : option (int * Z * Z * list Byte.int) :=
  match event with
  | gateway_primitive actual | gateway_committed_lost actual =>
    match io actual with
    | Some (gateway_native_receive descriptor requested returned bytes) =>
      Some (descriptor, requested, returned, bytes)
    | _ => None
    end
  | _ => None
  end.

(* io classifies only this SDK operation's direct byte effect. A callback's
   other operations retain their own global rows; this is not their exclusion. *)
Record gateway_direct_receive_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io) : Prop := {
  gateway_direct_receive_external : forall definition arguments before world result after next event
      descriptor requested returned bytes,
    gateway_runtime_operation backend definition arguments before world result after next event ->
    io event = Some (gateway_native_receive descriptor requested returned bytes) ->
    exists output extent flags,
      definition = gateway_receive_definition /\
      arguments = [Vint descriptor; output; Vlong extent; Vint flags];
  gateway_direct_receive_builtin : forall ef types arguments before world result after next event,
    gateway_builtin backend ef types arguments before world result after next event ->
    forall descriptor requested returned bytes,
      io event <> Some (gateway_native_receive descriptor requested returned bytes)
}.

Record gateway_receive_row_sample := {
  gateway_receive_row_position : nat;
  gateway_receive_row_code : ND.LeanCage_Host_NativeCode_CallRow;
  gateway_receive_row_descriptor : int;
  gateway_receive_row_requested : Z;
  gateway_receive_row_returned : Z;
  gateway_receive_row_bytes : list Byte.int;
  gateway_receive_row_extent : int64;
  gateway_receive_row_flags : int;
  gateway_receive_row_operation :
    gateway_native_row_operation gateway_receive_row_code =
      gateway_native_receive_code gateway_receive_row_descriptor gateway_receive_row_extent gateway_receive_row_flags;
  gateway_receive_row_product : gateway_native_stream_product gateway_receive_row_code
    ND.LeanCage_Host_NativeCode_Product_received gateway_receive_row_bytes
}.

Definition gateway_receive_rows_bytes descriptor (samples : list gateway_receive_row_sample) :=
  flat_map (fun sample => if Int.eq (gateway_receive_row_descriptor sample) descriptor
    then gateway_receive_row_bytes sample else []) samples.

Inductive gateway_receive_row_step {World Event} (backend : gateway_backend World Event) ge io rows :
    gateway_state World -> gateway_event Event -> gateway_state World -> list gateway_receive_row_sample -> Prop :=
| gateway_receive_row_direct : forall source event after observed descriptor requested returned bytes
      selected row extent flags output definition arguments memory world continuation
      (operation : gateway_native_row_operation row = gateway_native_receive_code descriptor extent flags)
      (product : gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_received bytes),
    source = gateway_live (Callstate definition arguments continuation memory) world ->
    (event = gateway_primitive observed \/ event = gateway_committed_lost observed) ->
    definition = gateway_receive_definition ->
    arguments = [Vint descriptor; output; Vlong extent; Vint flags] ->
    gateway_step backend ge source event after ->
    rows world observed = Some (selected, row) ->
    io observed = Some (gateway_native_receive descriptor requested returned bytes) ->
    gateway_receive_row_step backend ge io rows source event after
      [{| gateway_receive_row_position := selected; gateway_receive_row_code := row;
          gateway_receive_row_descriptor := descriptor; gateway_receive_row_requested := requested;
          gateway_receive_row_returned := returned; gateway_receive_row_bytes := bytes;
          gateway_receive_row_extent := extent; gateway_receive_row_flags := flags;
          gateway_receive_row_operation := operation; gateway_receive_row_product := product |}]
| gateway_receive_row_quiet : forall source event after,
    gateway_step backend ge source event after -> gateway_direct_receive io event = None ->
    gateway_receive_row_step backend ge io rows source event after [].

Theorem gateway_direct_receive_none_bytes {Event} io descriptor (event : gateway_event Event) :
  gateway_direct_receive io event = None -> gateway_received_event io descriptor event = [].
Proof.
  destruct event; cbn [gateway_direct_receive gateway_received_event]; try reflexivity;
    destruct (io observed) as [sample |]; try reflexivity;
    destruct sample; try reflexivity; discriminate.
Qed.

Theorem gateway_receive_row_step_bytes {World Event} (backend : gateway_backend World Event)
    ge io rows source event after samples descriptor :
  gateway_receive_row_step backend ge io rows source event after samples ->
  gateway_receive_rows_bytes descriptor samples = gateway_received_event io descriptor event.
Proof.
  intro ACTUAL; inversion ACTUAL; subst; unfold gateway_receive_rows_bytes;
    cbn [flat_map gateway_receive_row_descriptor gateway_receive_row_bytes].
  - destruct H0 as [SAME |SAME]; subst event; cbn [gateway_received_event];
      match goal with IO : io _ = Some (gateway_native_receive _ _ _ _) |- _ => rewrite IO end;
      rewrite ?app_nil_r; reflexivity.
  - symmetry; apply gateway_direct_receive_none_bytes; assumption.
Qed.

Inductive gateway_receive_row_trace {World Event} (backend : gateway_backend World Event) ge io rows :
    gateway_state World -> list (gateway_event Event) -> gateway_state World ->
      list gateway_receive_row_sample -> Prop :=
| gateway_receive_trace_nil : forall source,
    gateway_receive_row_trace backend ge io rows source [] source []
| gateway_receive_trace_cons : forall source event middle events after first last,
    gateway_receive_row_step backend ge io rows source event middle first ->
    gateway_receive_row_trace backend ge io rows middle events after last ->
    gateway_receive_row_trace backend ge io rows source (event :: events) after (first ++ last).

Theorem gateway_receive_row_trace_erase {World Event} (backend : gateway_backend World Event)
    ge io rows source events after samples :
  gateway_receive_row_trace backend ge io rows source events after samples ->
  gateway_steps backend ge source events after.
Proof.
  intro TRACE; induction TRACE; [constructor |].
  inversion H; subst; econstructor; eassumption.
Qed.

Theorem gateway_receive_row_trace_bytes {World Event} (backend : gateway_backend World Event)
    ge io rows source events after samples descriptor :
  gateway_receive_row_trace backend ge io rows source events after samples ->
  gateway_receive_rows_bytes descriptor samples = gateway_received_bytes io descriptor events.
Proof.
  intro ACTUAL; induction ACTUAL; [reflexivity |].
  unfold gateway_receive_rows_bytes; rewrite flat_map_app; fold (gateway_receive_rows_bytes descriptor first).
  fold (gateway_receive_rows_bytes descriptor last).
  rewrite (gateway_receive_row_step_bytes _ _ _ _ _ _ _ _ descriptor H), IHACTUAL; reflexivity.
Qed.

Theorem gateway_external_receive_row_step {World Event} (backend : gateway_backend World Event)
    ge io process position builders genuine actions attributes rows
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_native_stream_runtime backend io rows)
    (direct : gateway_direct_receive_runtime backend io)
    definition arguments continuation memory world result changed next observed event after :
  gateway_runtime_operation backend definition arguments memory world result changed next observed ->
  (event = gateway_primitive observed \/ event = gateway_committed_lost observed) ->
  gateway_step backend ge (gateway_live (Callstate definition arguments continuation memory) world) event after ->
  exists samples, gateway_receive_row_step backend ge io rows
    (gateway_live (Callstate definition arguments continuation memory) world) event after samples.
Proof.
  intros OPERATION EVENT STEP.
  destruct (io observed) as [sample |] eqn:IO.
  - destruct sample as [descriptor requested returned bytes |descriptor requested returned bytes].
    + destruct (gateway_direct_receive_external _ _ direct _ _ _ _ _ _ _ _ _ _ _ _ OPERATION IO)
        as (output & extent & flags & DEFINITION & ARGUMENTS).
      subst definition arguments.
      assert (INPUTS : gateway_native_operation_inputs builders genuine actions attributes memory world
        gateway_receive_definition [Vint descriptor; output; Vlong extent; Vint flags]
        (gateway_native_receive_code descriptor extent flags)).
      { apply gateway_native_direct_inputs; apply gateway_native_receive_operands. }
      destruct (gateway_native_operation_row _ _ _ _ _ _ _ _ recording _ _ _ _ _ _ _ _ _
        INPUTS OPERATION) as (selected & row & ROW & PROCESS & CODE & ORDER).
      assert (PRODUCT : gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_received bytes).
      { eapply gateway_native_receive_product; eassumption. }
      exists [{| gateway_receive_row_position := selected; gateway_receive_row_code := row;
        gateway_receive_row_descriptor := descriptor; gateway_receive_row_requested := requested;
        gateway_receive_row_returned := returned; gateway_receive_row_bytes := bytes;
        gateway_receive_row_extent := extent; gateway_receive_row_flags := flags;
        gateway_receive_row_operation := CODE; gateway_receive_row_product := PRODUCT |}].
      eapply gateway_receive_row_direct; try reflexivity; eassumption.
    + exists []; apply gateway_receive_row_quiet; [exact STEP |].
      destruct EVENT as [SAME |SAME]; subst event; cbn [gateway_direct_receive]; rewrite IO; reflexivity.
  - exists []; apply gateway_receive_row_quiet; [exact STEP |].
    destruct EVENT as [SAME |SAME]; subst event; cbn [gateway_direct_receive]; rewrite IO; reflexivity.
Qed.

Theorem gateway_actual_receive_row_trace {World Event} (backend : gateway_backend World Event)
    ge io process position builders genuine actions attributes rows
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_native_stream_runtime backend io rows)
    (direct : gateway_direct_receive_runtime backend io)
    source events after :
  gateway_steps backend ge source events after ->
  exists samples, gateway_receive_row_trace backend ge io rows source events after samples /\
    forall descriptor, gateway_receive_rows_bytes descriptor samples = gateway_received_bytes io descriptor events.
Proof.
  intro RUN.
  assert (TRACE : exists samples, gateway_receive_row_trace backend ge io rows source events after samples).
  { induction RUN.
    - exists []; constructor.
    - destruct IHRUN as [tail REST].
      assert (HEAD : exists samples, gateway_receive_row_step backend ge io rows first observed middle samples).
      { inversion H; subst.
        - exists []; constructor; [exact H |reflexivity].
        - eapply gateway_external_receive_row_step; [exact recording |exact observation |exact direct | |left; reflexivity |exact H].
          exact H0.
        - exists []; apply gateway_receive_row_quiet; [exact H |].
          cbn [gateway_direct_receive].
          destruct (io observed0) as [sample |] eqn:IO; [destruct sample |reflexivity]; [|reflexivity].
          exfalso; eapply gateway_direct_receive_builtin; [exact direct |exact H1 |exact IO].
        - exists []; constructor; [exact H |reflexivity].
        - exists []; constructor; [exact H |reflexivity].
        - exists []; constructor; [exact H |reflexivity].
        - eapply gateway_external_receive_row_step; [exact recording |exact observation |exact direct | |right; reflexivity |exact H].
          exact H0.
        - exists []; apply gateway_receive_row_quiet; [exact H |].
          cbn [gateway_direct_receive].
          destruct (io observed0) as [sample |] eqn:IO; [destruct sample |reflexivity]; [|reflexivity].
          exfalso; eapply gateway_direct_receive_builtin; [exact direct |exact H1 |exact IO]. }
      destruct HEAD as [head CURRENT].
      exists (head ++ tail); econstructor; eassumption. }
  destruct TRACE as [samples ACTUAL]; exists samples; split; [exact ACTUAL |].
  intro descriptor; eapply gateway_receive_row_trace_bytes; exact ACTUAL.
Qed.

Theorem gateway_receive_row_step_position {World Event} (backend : gateway_backend World Event)
    ge io process position builders genuine actions attributes rows
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    source event after samples :
  gateway_receive_row_step backend ge io rows source event after samples ->
  Forall (fun sample =>
    gateway_native_row_process (gateway_receive_row_code sample) =
      Nat_of_nat (process (gateway_state_world source)) /\
    (position (gateway_state_world source) <= gateway_receive_row_position sample <
      position (gateway_state_world after))%nat) samples.
Proof.
  intro ACTUAL; inversion ACTUAL; subst; [|constructor].
  constructor; [|constructor].
  cbn [gateway_receive_row_code gateway_receive_row_position gateway_state_world].
  assert (PHYSICAL : exists result changed next,
    gateway_runtime_operation backend gateway_receive_definition
      [Vint descriptor; output; Vlong extent; Vint flags] memory world result changed next observed /\
    gateway_state_world after = next).
  { destruct H0 as [SAME |SAME]; subst event; inversion H3; subst;
      try contradiction; (eexists; eexists; eexists; split;
      [unfold gateway_runtime_operation, gateway_receive_definition; eassumption |reflexivity]). }
  destruct PHYSICAL as (result & changed & next & OPERATION & AFTER).
  assert (INPUTS : gateway_native_operation_inputs builders genuine actions attributes memory world
    gateway_receive_definition [Vint descriptor; output; Vlong extent; Vint flags]
    (gateway_native_receive_code descriptor extent flags)).
  { apply gateway_native_direct_inputs; apply gateway_native_receive_operands. }
  destruct (gateway_native_operation_row _ _ _ _ _ _ _ _ recording _ _ _ _ _ _ _ _ _
    INPUTS OPERATION) as (actual & code & ROW & PROCESS & CODE & ORDER).
  assert (SAME : actual = selected /\ code = row) by (split; congruence).
  destruct SAME; subst actual code; rewrite AFTER; split; assumption.
Qed.

Theorem gateway_receive_row_trace_positions {World Event} (backend : gateway_backend World Event)
    ge io process position builders genuine actions attributes rows
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    source events after samples :
  gateway_receive_row_trace backend ge io rows source events after samples ->
  Forall (fun sample =>
    gateway_native_row_process (gateway_receive_row_code sample) =
      Nat_of_nat (process (gateway_state_world source)) /\
    (position (gateway_state_world source) <= gateway_receive_row_position sample <
      position (gateway_state_world after))%nat) samples /\
  StronglySorted (fun first last => (gateway_receive_row_position first < gateway_receive_row_position last)%nat) samples.
Proof.
  intro TRACE; induction TRACE.
  - split; constructor.
  - destruct IHTRACE as [TAIL SORTED].
    assert (STEP : gateway_step backend ge source event middle).
    { inversion H; subst; assumption. }
    destruct (gateway_native_step_actor _ _ _ _ _ _ _ _ recording _ _ _ _ STEP) as [PROCESS RANGE].
    pose proof (gateway_receive_row_trace_erase _ _ _ _ _ _ _ _ TRACE) as RUN.
    destruct (gateway_native_run_actor _ _ _ _ _ _ _ _ recording _ _ _ _ RUN) as [LATER LAST].
    pose proof (gateway_receive_row_step_position _ _ _ _ _ _ _ _ _ _ recording _ _ _ _ H) as HEAD.
    split.
    + apply Forall_app; split.
      * eapply Forall_impl; [|exact HEAD]. intros sample [TOKEN BOUND]; split; [exact TOKEN |lia].
      * eapply Forall_impl; [|exact TAIL]. intros sample [TOKEN BOUND]; split; [rewrite PROCESS in TOKEN; exact TOKEN |lia].
    + inversion H; subst; cbn in *; [|exact SORTED].
      constructor; [exact SORTED |].
      inversion HEAD; subst.
      eapply Forall_impl; [|exact TAIL]. intros sample [TOKEN BOUND].
      cbn [gateway_receive_row_position] in *; lia.
Qed.
