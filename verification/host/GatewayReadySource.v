(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual readiness helper owns its poll item and source phases. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps CallAccess LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFunctionEntry.
Import ListNotations.

Definition ready_item_type := Tstruct _pollfd noattr.
Definition ready_environment item := PTree.set _item (item, ready_item_type) empty_env.
Definition ready_temporaries stream direction := PTree.set _events (Vint direction)
  (PTree.set _stream stream (create_undef_temps (fn_temps f_host_ready))).

Theorem actual_ready_item_size : sizeof (genv_cenv (Clight.globalenv prog)) ready_item_type = 8.
Proof. vm_compute; reflexivity. Qed.

Lemma ready_function_entry (ge : Clight.genv) before item after stream direction :
  Mem.alloc before 0 (sizeof (genv_cenv ge) ready_item_type) = (after, item) ->
  function_entry2 ge f_host_ready [stream; Vint direction] before (ready_environment item)
    (ready_temporaries stream direction) after.
Proof.
  intro ALLOC; constructor.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate |]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate |]); apply list_norepet_nil.
  - unfold list_disjoint, var_names; cbn; intros a b LEFT RIGHT.
    destruct LEFT as [LEFT | [LEFT | LEFT]]; try contradiction; subst a;
      repeat destruct RIGHT as [RIGHT | RIGHT]; try contradiction; subst b; discriminate.
  - unfold ready_environment; cbn [fn_vars]; econstructor; [exact ALLOC | constructor].
  - reflexivity.
Qed.

Theorem actual_ready_entry_allocates (ge : Clight.genv) before stream direction continuation :
  exists item after,
    store_edge ge (Callstate (Internal f_host_ready) [stream; Vint direction] continuation before)
      (State f_host_ready (fn_body f_host_ready) continuation (ready_environment item)
        (ready_temporaries stream direction) after) /\
    Mem.alloc before 0 (sizeof (genv_cenv ge) ready_item_type) = (after, item) /\
    ~ Mem.valid_block before item /\
    Mem.range_perm after item 0 (sizeof (genv_cenv ge) ready_item_type) Cur Freeable /\
    Mem.unchanged_on (fun _ _ => True) before after.
Proof.
  destruct (Mem.alloc before 0 (sizeof (genv_cenv ge) ready_item_type)) as [after item] eqn:ALLOC.
  exists item, after; split.
  - apply function_entry_source_edge, ready_function_entry; exact ALLOC.
  - split; [reflexivity |]. split; [eapply Mem.fresh_block_alloc; exact ALLOC |]. split.
    + intros position RANGE; eapply Mem.perm_alloc_2; eassumption.
    + eapply Mem.alloc_unchanged_on; exact ALLOC.
Qed.

Lemma actual_ready_entry_canonical (ge : Clight.genv) before stream direction environment temporaries allocated :
  function_entry2 ge f_host_ready [stream; Vint direction] before environment temporaries allocated ->
  exists item,
    environment = ready_environment item /\ temporaries = ready_temporaries stream direction /\
    Mem.alloc before 0 (sizeof (genv_cenv ge) ready_item_type) = (allocated, item) /\
    ~ Mem.valid_block before item /\
    Mem.range_perm allocated item 0 (sizeof (genv_cenv ge) ready_item_type) Cur Freeable /\
    Mem.unchanged_on (fun _ _ => True) before allocated.
Proof.
  intro ENTRY.
  destruct (actual_ready_entry_allocates ge before stream direction Kstop)
    as (item & after & EDGE & ALLOC & FRESH & PERMISSIONS & FRAME).
  destruct EDGE as [IN [REAL UNIQUE]].
  assert (ACTUAL : step2 ge (Callstate (Internal f_host_ready) [stream; Vint direction] Kstop before)
    E0 (State f_host_ready (fn_body f_host_ready) Kstop environment temporaries allocated)) by
    (apply step_internal_function; exact ENTRY).
  destruct (UNIQUE _ _ ACTUAL) as [TRACE SAME]; inversion SAME; subst.
  exists item; split; [reflexivity |]. split; [reflexivity |]. split; [exact ALLOC |].
  split; [exact FRESH |]. split; [exact PERMISSIONS | exact FRAME].
Qed.

Definition ready_iteration_body := match fn_body f_host_ready with Sloop body _ => body | _ => Sskip end.
Definition ready_iteration := match ready_iteration_body with Ssequence _ body => body | _ => Sskip end.
Definition ready_iteration_cont := Kloop1 ready_iteration_body Sskip Kstop.
Definition ready_control_sequence := match ready_iteration with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_control := match ready_iteration with Ssequence _ after => after | _ => Sskip end.
Definition ready_control_call := match ready_control_sequence with Ssequence call _ => call | _ => Sskip end.
Definition ready_control_test := match ready_control_sequence with Ssequence _ test => test | _ => Sskip end.
Definition ready_clock_sequence := match ready_after_control with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_clock := match ready_after_control with Ssequence _ after => after | _ => Sskip end.
Definition ready_clock_call := match ready_clock_sequence with Ssequence call _ => call | _ => Sskip end.
Definition ready_clock_bind := match ready_clock_sequence with Ssequence _ bind => bind | _ => Sskip end.
Definition ready_clock_guard := match ready_after_clock with Ssequence guard _ => guard | _ => Sskip end.
Definition ready_after_clock_guard := match ready_after_clock with Ssequence _ after => after | _ => Sskip end.
Definition ready_clock_boolean := match ready_clock_guard with Ssequence boolean _ => boolean | _ => Sskip end.
Definition ready_clock_test := match ready_clock_guard with Ssequence _ test => test | _ => Sskip end.

Lemma actual_ready_body_structure :
  fn_body f_host_ready = Sloop ready_iteration_body Sskip /\
  ready_iteration_body = Ssequence Sskip ready_iteration /\
  ready_iteration = Ssequence ready_control_sequence ready_after_control /\
  ready_control_sequence = Ssequence ready_control_call ready_control_test /\
  ready_after_control = Ssequence ready_clock_sequence ready_after_clock /\
  ready_clock_sequence = Ssequence ready_clock_call ready_clock_bind /\
  ready_after_clock = Ssequence ready_clock_guard ready_after_clock_guard /\
  ready_clock_guard = Ssequence ready_clock_boolean ready_clock_test.
Proof. repeat split; reflexivity. Qed.
