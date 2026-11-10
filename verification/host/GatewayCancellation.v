(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Cancellation bytes and local ownership come from the real source. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess ReceiverAllocation CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFunctionEntry GatewayGuardScope
  GatewayThreadRuntime GatewayStreamInterface GatewayRuntimeABI GatewayPrefix GatewayGuardedCuts
  GatewayStreamAccess GatewayStreamLayout.
Import ListNotations.
Open Scope Z_scope.

Definition control_environment command := PTree.set _command (command, tuchar) empty_env.
Definition control_temporaries stream := PTree.set _stream stream (create_undef_temps (fn_temps f_host_control)).

Lemma actual_control_body_structure :
  fn_body f_host_control = Ssequence control_entry_guard control_after_guard.
Proof. reflexivity. Qed.

Lemma control_function_entry ge before command after stream :
  Mem.alloc before 0 1 = (after, command) ->
  function_entry2 ge f_host_control [stream] before (control_environment command)
    (control_temporaries stream) after.
Proof.
  intro ALLOC; constructor.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate |]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate |]); apply list_norepet_nil.
  - unfold list_disjoint, var_names; cbn; intros a b LEFT RIGHT.
    destruct LEFT as [LEFT | LEFT]; [subst a | contradiction].
    repeat destruct RIGHT as [RIGHT | RIGHT]; try contradiction; subst b; discriminate.
  - unfold control_environment; cbn [fn_vars]; econstructor; [exact ALLOC | constructor].
  - reflexivity.
Qed.

Theorem actual_control_entry_allocates ge before stream continuation :
  exists command after,
    store_edge ge (Callstate (Internal f_host_control) [stream] continuation before)
      (State f_host_control (fn_body f_host_control) continuation (control_environment command)
        (control_temporaries stream) after) /\
    Mem.alloc before 0 1 = (after, command) /\ ~ Mem.valid_block before command /\
    Mem.range_perm after command 0 1 Cur Freeable /\ Mem.unchanged_on (fun _ _ => True) before after.
Proof.
  destruct (Mem.alloc before 0 1) as [after command] eqn:ALLOC.
  exists command, after; split.
  - apply function_entry_source_edge, control_function_entry; exact ALLOC.
  - split; [reflexivity |]. split; [eapply Mem.fresh_block_alloc; exact ALLOC |]. split.
    + intros position RANGE; eapply Mem.perm_alloc_2; eassumption.
    + eapply Mem.alloc_unchanged_on; exact ALLOC.
Qed.

Lemma actual_control_entry_canonical ge before stream environment temporaries allocated :
  function_entry2 ge f_host_control [stream] before environment temporaries allocated ->
  exists command,
    environment = control_environment command /\ temporaries = control_temporaries stream /\
    Mem.alloc before 0 1 = (allocated, command) /\ ~ Mem.valid_block before command /\
    Mem.range_perm allocated command 0 1 Cur Freeable /\ Mem.unchanged_on (fun _ _ => True) before allocated.
Proof.
  intro ENTRY.
  destruct (actual_control_entry_allocates ge before stream Kstop)
    as [command [after [[INTERNAL [REAL UNIQUE]] [ALLOC [FRESH [PERMISSION FRAME]]]]]].
  assert (ACTUAL : step2 ge (Callstate (Internal f_host_control) [stream] Kstop before) E0
    (State f_host_control (fn_body f_host_control) Kstop environment temporaries allocated)).
  { apply step_internal_function; exact ENTRY. }
  destruct (UNIQUE _ _ ACTUAL) as [_ SAME]; inversion SAME; subst.
  exists command; exact (conj eq_refl (conj eq_refl (conj ALLOC (conj FRESH (conj PERMISSION FRAME))))).
Qed.

Definition control_command_assignment := match control_after_guard with
  | Ssequence assignment _ => assignment | _ => Sskip end.
Definition control_after_command := match control_after_guard with
  | Ssequence _ after => after | _ => Sskip end.

Lemma actual_control_command_assignment ge command temporaries before after continuation :
  Mem.store Mint8unsigned before command 0 (Vint (Int.repr 67)) = Some after ->
  store_edge ge
    (State f_host_control control_command_assignment continuation (control_environment command) temporaries before)
    (State f_host_control Sskip continuation (control_environment command) temporaries after).
Proof.
  intro STORE; eapply assignment_source_edge with (b := command) (ofs := Ptrofs.zero)
    (v := Vint (Int.repr 67)) (w := Vint (Int.repr 67)).
  - apply local_location_value; apply PTree.gss.
  - apply old_expression_value; constructor.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint8unsigned); [reflexivity |].
    unfold Mem.storev; cbn; exact STORE.
Qed.

Lemma actual_control_command_bytes before after command :
  Mem.store Mint8unsigned before command 0 (Vint (Int.repr 67)) = Some after ->
  Mem.loadbytes after command 0 1 = Some [Byte (Byte.repr 67)].
Proof. intro STORE; exact (Mem.loadbytes_store_same _ _ _ _ _ _ STORE). Qed.

Definition control_send_binding := match control_after_command with
  | Ssequence first _ => first | _ => Sskip end.
Definition control_after_send := match control_after_command with
  | Ssequence _ after => after | _ => Sskip end.
Definition control_send_prefix := match control_send_binding with
  | Ssequence first _ => first | _ => Sskip end.
Definition control_count_binding := match control_send_binding with
  | Ssequence _ after => after | _ => Sskip end.
Definition control_descriptor_load := match control_send_prefix with
  | Ssequence first _ => first | _ => Sskip end.
Definition control_send_call := match control_send_prefix with
  | Ssequence _ call => call | _ => Sskip end.
Definition control_descriptor_values temporaries descriptor := PTree.set _t'14 (Vint descriptor) temporaries.
Definition control_send_cont command temporaries descriptor :=
  Kcall (Some _t'5) f_host_control (control_environment command)
    (control_descriptor_values temporaries descriptor) (Kseq control_count_binding (Kseq control_after_send Kstop)).

Lemma actual_control_send_structure :
  control_after_guard = Ssequence control_command_assignment control_after_command /\
  control_after_command = Ssequence control_send_binding control_after_send /\
  control_send_binding = Ssequence control_send_prefix control_count_binding /\
  control_send_prefix = Ssequence control_descriptor_load control_send_call.
Proof. repeat split; reflexivity. Qed.

Lemma actual_control_send_call (ge : Clight.genv) command temporaries descriptor memory symbol :
  Genv.find_symbol ge _send = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_send_definition ->
  store_edge ge
    (State f_host_control control_send_call (Kseq control_count_binding (Kseq control_after_send Kstop))
      (control_environment command) (control_descriptor_values temporaries descriptor) memory)
    (Callstate gateway_send_definition
      [Vint descriptor; Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
      (control_send_cont command temporaries descriptor) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - eapply cons_argument_values with (v := Vint descriptor).
    + apply old_expression_value, value_temp; apply PTree.gss.
    + reflexivity.
    + eapply cons_argument_values with (v := Vptr command Ptrofs.zero).
      * apply local_address_expression; apply PTree.gss.
      * reflexivity.
      * eapply cons_argument_values with (v := Vint Int.one).
        -- apply old_expression_value; constructor.
        -- reflexivity.
        -- eapply cons_argument_values with (v := Vint (Int.repr 16384)).
           ++ apply old_expression_value; constructor.
           ++ reflexivity.
           ++ apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_control_descriptor_send_path (ge : Clight.genv) command temporaries stream_block stream_offset
    initial memory symbol :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  stream_member_layout ge _control 4 ->
  Genv.find_symbol ge _send = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_send_definition ->
  gateway_guarded_retained_path ge
    (fun memory => gateway_stream_memory memory stream_block stream_offset initial)
    gateway_send_definition
    [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
    (control_send_cont command temporaries (stream_control initial))
    (State f_host_control control_descriptor_load
      (Kseq control_send_call (Kseq control_count_binding (Kseq control_after_send Kstop)))
      (control_environment command) temporaries memory).
Proof.
  intros STREAM LAYOUT SYMBOL FUNCTION.
  eapply gateway_guarded_next with (next := State f_host_control Sskip
    (Kseq control_send_call (Kseq control_count_binding (Kseq control_after_send Kstop)))
    (control_environment command) (control_descriptor_values temporaries (stream_control initial)) memory).
  - cbn; tauto.
  - intros another CELLS; apply certified_set_edge.
    eapply actual_stream_member_read with (delta := 4) (chunk := Mint32).
    + exact STREAM.
    + exact LAYOUT.
    + reflexivity.
    + exact (proj1 (proj2 CELLS)).
  - eapply gateway_guarded_next with (next := State f_host_control control_send_call
      (Kseq control_count_binding (Kseq control_after_send Kstop))
      (control_environment command) (control_descriptor_values temporaries (stream_control initial)) memory).
    + cbn; tauto.
    + intros another CELLS; apply unchanged_store_edge, edge_skip_seq.
    + eapply gateway_guarded_next with (next := Callstate gateway_send_definition
        [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
        (control_send_cont command temporaries (stream_control initial)) memory).
      * cbn; tauto.
      * intros another CELLS; eapply actual_control_send_call; eassumption.
      * constructor.
Qed.
