(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual readiness either returns or retries after excluding its error branch. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyPhases
  GatewayControlPaths GatewayPollStorePath GatewayInertCuts GatewayInertEffects GatewayBranches GatewayRuntimeCuts
  GatewayIntegerFailures GatewayOperations GatewayFrames GatewayStreamInterface GatewayPrimitiveCalls GatewayTransferMath
  GatewayGuardObservation.
Import ListNotations.

Definition ready_error_guard := match ready_after_signals with Ssequence guard _ => guard | _ => Sskip end.
Definition ready_result_test := match ready_after_signals with Ssequence _ test => test | _ => Sskip end.
Definition ready_error_boolean := match ready_error_guard with Ssequence boolean _ => boolean | _ => Sskip end.
Definition ready_error_test := match ready_error_guard with Ssequence _ test => test | _ => Sskip end.
Definition ready_error_condition := match ready_error_test with Sifthenelse condition _ _ => condition
  | _ => Econst_int Int.zero tint end.
Definition ready_error_failure := match ready_error_test with Sifthenelse _ failure _ => failure | _ => Sskip end.
Definition ready_result_condition := match ready_result_test with Sifthenelse condition _ _ => condition
  | _ => Econst_int Int.zero tint end.
Definition ready_success_return := Sreturn (Some (Econst_int Int.zero tint)).
Definition ready_error_boolean_cont := Kseq ready_error_test (Kseq ready_result_test ready_iteration_cont).

Lemma actual_ready_error_prefix ge item temporaries memory :
  gateway_retained_prefix ge
    (State f_host_ready ready_error_boolean ready_error_boolean_cont (ready_environment item) temporaries memory)
    (State f_host_ready ready_after_signals ready_iteration_cont (ready_environment item) temporaries memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_ready ready_error_guard
    (Kseq ready_result_test ready_iteration_cont) (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  eapply gateway_prefix_next with (next := State f_host_ready ready_error_boolean ready_error_boolean_cont
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_seq |].
  exact (gateway_prefix_reached ge _ memory).
Qed.

Lemma actual_ready_retry_prefix ge item temporaries memory :
  gateway_retained_prefix ge
    (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item) temporaries memory)
    (State f_host_ready Sskip ready_iteration_cont (ready_environment item) temporaries memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_ready Sskip
    (Kloop2 ready_iteration_body Sskip Kstop) (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_loop1 |].
  eapply gateway_prefix_next with (next := State f_host_ready (fn_body f_host_ready) Kstop
    (ready_environment item) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_loop2 |].
  exact (gateway_prefix_reached ge _ memory).
Qed.

Theorem actual_ready_tail_choice {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor ready (discipline : gateway_runtime_discipline backend ready)
    item temporaries stream before world events after next :
  temporaries ! _stream = Some stream -> ready before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready ready_after_signals ready_iteration_cont
      (ready_environment item) temporaries before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists prefix suffix final_temporaries memory current (returning : bool),
    events = prefix ++ suffix /\ gateway_received_bytes io descriptor prefix = [] /\
    final_temporaries ! _stream = Some stream /\ ready memory current /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready ready_after_signals ready_iteration_cont
        (ready_environment item) temporaries before) world) prefix
      (gateway_live (State f_host_ready (if returning then ready_success_return else Sskip) ready_iteration_cont
        (ready_environment item) final_temporaries memory) current) /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready (if returning then ready_success_return else Sskip) ready_iteration_cont
        (ready_environment item) final_temporaries memory) current)
      suffix (gateway_live (Returnstate (Vint Int.zero) Kstop after) next).
Proof.
  intros STREAM READY RUN.
  destruct (gateway_quiet_prefix_cut backend ge io descriptor ready discipline _ _ before world events (Vint Int.zero) after next
    (actual_ready_error_prefix ge item temporaries before) READY RUN)
    as (p0 & rest0 & m0 & w0 & E0S & B0 & P0 & C0 & R0).
  assert (PROFILE : gateway_inert_source _stream stream ready_error_boolean_cont f_host_ready (ready_environment item)
    (State f_host_ready ready_error_boolean ready_error_boolean_cont (ready_environment item) temporaries m0)).
  { cbn [gateway_inert_source]; split; [reflexivity |]. split; [reflexivity |]. split; [exact STREAM |].
    split; [cbn; intuition discriminate | constructor]. }
  destruct (gateway_inert_effect_cut backend ge io descriptor ready discipline _stream stream ready_error_test
    (Kseq ready_result_test ready_iteration_cont) f_host_ready (ready_environment item)
    (State f_host_ready ready_error_boolean ready_error_boolean_cont (ready_environment item) temporaries m0)
    w0 rest0 (Vint Int.zero) after next ltac:(cbn; tauto) PROFILE C0 R0)
    as (p1 & rest1 & temps & m1 & w1 & E1S & B1 & PARAMETER & C1 & P1 & R1).
  destruct (gateway_actual_branch backend ge ready discipline f_host_ready ready_error_condition ready_error_failure Sskip
    (Kseq ready_result_test ready_iteration_cont) (ready_environment item) temps m1 w1 rest1 (Vint Int.zero) after next C1 R1)
    as (p2 & rest2 & m2 & w2 & value & branch & E2S & A2 & C2 & VALUE2 & BOOL2 & P2 & R2).
  destruct branch.
  - pose proof (gateway_actual_selected_integer_failure backend ge f_host_ready ready_error_failure
      (Kseq ready_result_test ready_iteration_cont) (ready_environment item) temps m2 w2 rest2 (Vint Int.zero) after next
      ltac:(reflexivity) ltac:(cbn; tauto) ltac:(reflexivity) R2) as BAD; discriminate BAD.
  - destruct (gateway_uniform_edge_side_cut backend ge ready discipline
      (State f_host_ready Sskip (Kseq ready_result_test ready_iteration_cont) (ready_environment item) temps m2)
      (State f_host_ready ready_result_test ready_iteration_cont (ready_environment item) temps m2)
      m2 w2 rest2 (Vint Int.zero) after next ltac:(cbn; tauto)
      ltac:(intro another; apply unchanged_store_edge, edge_skip_seq) C2 R2)
      as (p3 & rest3 & m3 & w3 & E3S & A3 & P3 & C3 & R3).
    destruct (gateway_actual_branch backend ge ready discipline f_host_ready ready_result_condition ready_success_return Sskip
      ready_iteration_cont (ready_environment item) temps m3 w3 rest3 (Vint Int.zero) after next C3 R3)
      as (p4 & suffix & memory & current & result_value & returning & E4S & A4 & C4 & VALUE4 & BOOL4 & P4 & R4).
    exists (p0 ++ p1 ++ p2 ++ gateway_source E0 :: p3 ++ gateway_source E0 :: p4 ++ [gateway_source E0]),
      suffix, temps, memory, current, returning.
    split.
    + rewrite E0S, E1S, E2S, E3S, E4S; repeat rewrite <- app_assoc; cbn [app].
      repeat rewrite <- app_assoc; cbn [app].
      repeat rewrite <- app_assoc; cbn [app]; reflexivity.
    + split.
      * repeat rewrite gateway_received_bytes_append; rewrite B0, B1.
        assert (B2 : gateway_received_bytes io descriptor p2 = []) by
          (apply gateway_quiet_received_empty; eapply Forall_impl; [|exact A2]; intros event SAME; right; exact SAME).
        assert (B3 : gateway_received_bytes io descriptor p3 = []) by
          (apply gateway_quiet_received_empty; eapply Forall_impl; [|exact A3]; intros event SAME; right; exact SAME).
        assert (B4 : gateway_received_bytes io descriptor p4 = []) by
          (apply gateway_quiet_received_empty; eapply Forall_impl; [|exact A4]; intros event SAME; right; exact SAME).
        rewrite B2; cbn [app]; rewrite gateway_received_source_cons, gateway_received_bytes_append, B3.
        cbn [app]; rewrite gateway_received_source_cons, gateway_received_bytes_append, B4; reflexivity.
      * split; [exact PARAMETER |]. split; [exact C4 |]. split; [|exact R4].
        eapply gateway_steps_append; [exact P0 |].
        eapply gateway_steps_append; [exact P1 |].
        eapply gateway_steps_append; [exact P2 |].
        econstructor.
        -- apply gateway_internal; [cbn; tauto | apply step_ifthenelse with (v1 := value) (b := false); assumption].
        -- eapply gateway_steps_append; [exact P3 |].
           econstructor; [apply gateway_internal; [cbn; tauto | apply edge_skip_seq] |].
           eapply gateway_steps_append; [exact P4 |].
           econstructor; [|constructor].
           apply gateway_internal; [cbn; tauto | apply step_ifthenelse with (v1 := result_value) (b := returning); assumption].
Qed.

Definition ready_tail_target item temporaries memory (returning : bool) :=
  if returning then State f_host_ready ready_success_return ready_iteration_cont (ready_environment item) temporaries memory
  else State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item) temporaries memory.

Theorem actual_ready_tail_destination {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor ready (discipline : gateway_runtime_discipline backend ready)
    item temporaries stream before world events after next :
  temporaries ! _stream = Some stream -> ready before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready ready_after_signals ready_iteration_cont
      (ready_environment item) temporaries before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists prefix suffix final_temporaries memory current (returning : bool),
    events = prefix ++ suffix /\ gateway_received_bytes io descriptor prefix = [] /\
    final_temporaries ! _stream = Some stream /\ ready memory current /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready ready_after_signals ready_iteration_cont
        (ready_environment item) temporaries before) world) prefix
      (gateway_live (ready_tail_target item final_temporaries memory returning) current) /\
    gateway_steps backend ge (gateway_live (ready_tail_target item final_temporaries memory returning) current)
      suffix (gateway_live (Returnstate (Vint Int.zero) Kstop after) next).
Proof.
  intros STREAM READY RUN.
  destruct (actual_ready_tail_choice backend ge io descriptor ready discipline item temporaries stream before world events after next
    STREAM READY RUN) as (prefix & suffix & temps & memory & current & returning & EVENTS & EMPTY & PARAMETER & INPUT & PREFIX & REST).
  destruct returning.
  - exists prefix, suffix, temps, memory, current, true; split; [exact EVENTS |]. split; [exact EMPTY |].
    split; [exact PARAMETER |]. split; [exact INPUT |]. split; assumption.
  - destruct (gateway_quiet_prefix_cut backend ge io descriptor ready discipline _ _ memory current suffix (Vint Int.zero) after next
      (actual_ready_retry_prefix ge item temps memory) INPUT REST)
      as (retry & following & changed & next_world & SUFFIX & RETRY_EMPTY & RETRY & FINAL & FOLLOWING).
    exists (prefix ++ retry), following, temps, changed, next_world, false.
    split; [rewrite EVENTS, SUFFIX, app_assoc; reflexivity |]. split.
    + rewrite gateway_received_bytes_append, EMPTY, RETRY_EMPTY; reflexivity.
    + split; [exact PARAMETER |]. split; [exact FINAL |]. split; [|exact FOLLOWING].
      eapply gateway_steps_append; [exact PREFIX |exact RETRY].
Qed.
