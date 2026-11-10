(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual clock helper supplies its own fresh output object. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess ReceiverAllocation CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFunctionEntry GatewayCallPath
  GatewayPrefix GatewayPython GatewayRuntimeABI.
Import ListNotations.
Open Scope Z_scope.

Definition clock_sample_type := Tstruct _timespec noattr.
Definition clock_environment sample := PTree.set _sample (sample, clock_sample_type) empty_env.
Definition clock_temporaries := create_undef_temps (fn_temps f_host_now).

Theorem actual_clock_sample_size :
  sizeof (genv_cenv (Clight.globalenv prog)) clock_sample_type = 16.
Proof. vm_compute; reflexivity. Qed.

Definition clock_gettime_definition := gateway_clock_gettime_definition.

Definition clock_first_call :=
  match fn_body f_host_now with
  | Ssequence (Ssequence (Ssequence call _) _) _ => call
  | _ => Sskip
  end.
Definition clock_call_test :=
  match fn_body f_host_now with
  | Ssequence (Ssequence (Ssequence _ test) _) _ => test
  | _ => Sskip
  end.
Definition clock_sample_guard :=
  match fn_body f_host_now with
  | Ssequence (Ssequence _ guard) _ => guard
  | _ => Sskip
  end.
Definition clock_after_guard :=
  match fn_body f_host_now with Ssequence _ rest => rest | _ => Sskip end.

Definition clock_api_cont sample continuation :=
  Kcall (Some _t'1) f_host_now (clock_environment sample) clock_temporaries
    (Kseq clock_call_test (Kseq clock_sample_guard (Kseq clock_after_guard continuation))).

Lemma clock_actual_body_structure : fn_body f_host_now =
  Ssequence (Ssequence (Ssequence clock_first_call clock_call_test) clock_sample_guard) clock_after_guard.
Proof. reflexivity. Qed.

Lemma clock_function_entry (ge : Clight.genv) before sample after :
  Mem.alloc before 0 (sizeof (genv_cenv ge) clock_sample_type) = (after, sample) ->
  function_entry2 ge f_host_now [] before (clock_environment sample) clock_temporaries after.
Proof.
  intro ALLOC;constructor.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate |]); apply list_norepet_nil.
  - apply list_norepet_nil.
  - unfold list_disjoint, var_names; cbn; intuition.
  - unfold clock_environment; cbn [fn_vars]; econstructor; [exact ALLOC | constructor].
  - reflexivity.
Qed.

Lemma clock_actual_entry_allocates (ge : Clight.genv) before continuation :
  exists sample after,
    store_edge ge (Callstate (Internal f_host_now) [] continuation before)
      (State f_host_now (fn_body f_host_now) continuation (clock_environment sample) clock_temporaries after) /\
    Mem.alloc before 0 (sizeof (genv_cenv ge) clock_sample_type) = (after, sample) /\
    ~ Mem.valid_block before sample /\
    Mem.range_perm after sample 0 (sizeof (genv_cenv ge) clock_sample_type) Cur Freeable /\
    Mem.unchanged_on (fun _ _ => True) before after.
Proof.
  destruct (Mem.alloc before 0 (sizeof (genv_cenv ge) clock_sample_type)) as [after sample] eqn:ALLOC.
  exists sample, after; split.
  - apply function_entry_source_edge, clock_function_entry; exact ALLOC.
  - split; [reflexivity |].
    assert (CHAIN : local_allocations before [(sample, sizeof (genv_cenv ge) clock_sample_type)] after).
    { econstructor; [exact ALLOC | constructor]. }
    pose proof (local_allocations_objects _ _ _ CHAIN) as OBJECTS.
    inversion OBJECTS as [|? ? SAMPLE REST]; subst.
    split; [exact (proj1 SAMPLE) |].
    split; [exact (proj2 SAMPLE) | eapply local_allocations_unchanged; exact CHAIN].
Qed.

Lemma clock_actual_entry_canonical (ge : Clight.genv) before environment temporaries allocated :
  function_entry2 ge f_host_now [] before environment temporaries allocated ->
  exists sample,
    environment = clock_environment sample /\ temporaries = clock_temporaries /\
    Mem.alloc before 0 (sizeof (genv_cenv ge) clock_sample_type) = (allocated, sample) /\
    ~ Mem.valid_block before sample /\
    Mem.range_perm allocated sample 0 (sizeof (genv_cenv ge) clock_sample_type) Cur Freeable /\
    Mem.unchanged_on (fun _ _ => True) before allocated.
Proof.
  intro ENTRY.
  destruct (clock_actual_entry_allocates (ge : Clight.genv) before Kstop)
    as [sample [after [[INTERNAL [REAL UNIQUE]] [ALLOC [FRESH [PERMISSION FRAME]]]]]].
  assert (ACTUAL : step2 ge (Callstate (Internal f_host_now) [] Kstop before) E0
    (State f_host_now (fn_body f_host_now) Kstop environment temporaries allocated)).
  { apply step_internal_function; exact ENTRY. }
  destruct (UNIQUE _ _ ACTUAL) as [_ SAME]; inversion SAME; subst.
  exists sample; exact (conj eq_refl (conj eq_refl (conj ALLOC (conj FRESH (conj PERMISSION FRAME))))).
Qed.

Lemma clock_actual_first_call (ge : Clight.genv) sample memory continuation symbol :
  Genv.find_symbol ge _clock_gettime = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some clock_gettime_definition ->
  store_edge ge
    (State f_host_now clock_first_call
      (Kseq clock_call_test (Kseq clock_sample_guard (Kseq clock_after_guard continuation)))
      (clock_environment sample) clock_temporaries memory)
    (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
      (clock_api_cont sample continuation) memory).
Proof.
  intros SYMBOL FUNCTION.
  eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - eapply cons_argument_values with (v := Vint Int.one).
    + apply old_expression_value; constructor.
    + reflexivity.
    + eapply cons_argument_values with (v := Vptr sample Ptrofs.zero).
      * apply local_address_expression; apply PTree.gss.
      * reflexivity.
      * apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Lemma clock_body_first_call_retained (ge : Clight.genv) sample memory continuation symbol :
  Genv.find_symbol ge _clock_gettime = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some clock_gettime_definition ->
  gateway_retained_call_path ge clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
    (clock_api_cont sample continuation)
    (State f_host_now (fn_body f_host_now) continuation (clock_environment sample) clock_temporaries memory).
Proof.
  intros SYMBOL FUNCTION; rewrite clock_actual_body_structure.
  eapply gateway_retained_next with (next := State f_host_now
    (Ssequence (Ssequence clock_first_call clock_call_test) clock_sample_guard)
    (Kseq clock_after_guard continuation) (clock_environment sample) clock_temporaries memory).
  - cbn; tauto.
  - intro another; apply unchanged_store_edge, edge_seq.
  - eapply gateway_retained_next with (next := State f_host_now
      (Ssequence clock_first_call clock_call_test)
      (Kseq clock_sample_guard (Kseq clock_after_guard continuation))
      (clock_environment sample) clock_temporaries memory).
    + cbn; tauto.
    + intro another; apply unchanged_store_edge, edge_seq.
    + eapply gateway_retained_next with (next := State f_host_now clock_first_call
        (Kseq clock_call_test (Kseq clock_sample_guard (Kseq clock_after_guard continuation)))
        (clock_environment sample) clock_temporaries memory).
      * cbn; tauto.
      * intro another; apply unchanged_store_edge, edge_seq.
      * eapply gateway_retained_next with (next := Callstate clock_gettime_definition
          [Vint Int.one; Vptr sample Ptrofs.zero] (clock_api_cont sample continuation) memory).
        -- cbn; tauto.
        -- intro another; eapply clock_actual_first_call; eassumption.
        -- constructor.
Qed.

Lemma clock_body_first_call_path (ge : Clight.genv) sample memory continuation symbol :
  Genv.find_symbol ge _clock_gettime = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some clock_gettime_definition ->
  gateway_control_call_path ge clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
    (clock_api_cont sample continuation)
    (State f_host_now (fn_body f_host_now) continuation (clock_environment sample) clock_temporaries memory).
Proof.
  intros SYMBOL FUNCTION; apply gateway_retained_control.
  eapply clock_body_first_call_retained; eassumption.
Qed.

(* §FS-host-boundary.caller: Every actual helper return crosses this exact clock/output call. *)
Theorem actual_clock_call_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    before world events returned after next symbol :
  Genv.find_symbol ge _clock_gettime = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some clock_gettime_definition ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix sample memory called_world allocation_before allocated,
    events = prefix ++ suffix /\
    Mem.alloc allocation_before 0 (sizeof (genv_cenv ge) clock_sample_type) = (allocated, sample) /\
    ~ Mem.valid_block allocation_before sample /\
    gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) prefix
      (gateway_live (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop) memory) called_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop) memory) called_world) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros SYMBOL FUNCTION RUN.
  destruct (actual_gateway_function_entry backend ge f_host_now [] Kstop before world events returned
    Kstop after next RUN)
    as [entry_prefix [body_events [allocation_before [allocation_world [environment [temporaries
      [allocated [EVENTS [PREFIX [ENTRY BODY]]]]]]]]]].
  destruct (clock_actual_entry_canonical (ge : Clight.genv) allocation_before environment temporaries allocated ENTRY)
    as [sample [ENV [TEMPS [ALLOC [FRESH [PERMISSION FRAME]]]]]]; subst environment temporaries.
  destruct (gateway_control_call_cut backend ge clock_gettime_definition
    [Vint Int.one; Vptr sample Ptrofs.zero] (clock_api_cont sample Kstop)
    (State f_host_now (fn_body f_host_now) Kstop (clock_environment sample) clock_temporaries allocated)
    allocation_world body_events returned after next
    (clock_body_first_call_path (ge : Clight.genv) sample allocated Kstop symbol SYMBOL FUNCTION) BODY)
    as [body_prefix [suffix [memory [called_world [BODY_EVENTS [CALL REST]]]]]].
  exists (entry_prefix ++ gateway_source E0 :: body_prefix), suffix, sample, memory, called_world,
    allocation_before, allocated.
  split; [rewrite EVENTS, BODY_EVENTS; rewrite <- app_assoc; reflexivity |].
  split; [exact ALLOC |]. split; [exact FRESH |]. split; [| exact REST].
  eapply gateway_steps_append; [exact PREFIX |].
  econstructor; [apply gateway_internal; [exact I | apply step_internal_function; exact ENTRY] | exact CALL].
Qed.


Theorem actual_clock_local_is_runtime_private (ge : Clight.genv) python before sample after :
  python_world_valid python before ->
  Mem.alloc before 0 (sizeof (genv_cenv ge) clock_sample_type) = (after, sample) ->
  ~ python_runtime_owned python sample.
Proof.
  intros [_ [_ [VALID _]]] ALLOC RUNTIME.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ ALLOC) as FRESH.
  apply FRESH; apply VALID; exact RUNTIME.
Qed.
