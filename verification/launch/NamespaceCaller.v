(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Connect the real namespace caller to local child creation and admission. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths.
Import ListNotations.
Open Scope Z_scope.
Set Printing Depth 30.

Definition namespace_tail index := child_tail index (fn_body f_namespace_init).
Definition namespace_phase index :=
  match namespace_tail index with Ssequence first _ => first | last => last end.
Definition namespace_creation_set := Sset _error (Etempvar _t'10 tint).
Definition namespace_creation_cont e le k :=
  Kcall (Some _t'10) f_namespace_init e le
    (Kseq namespace_creation_set (Kseq (namespace_tail 10) k)).

Ltac namespace_function := apply old_expression_value; eapply value_function;
  [eassumption|reflexivity|reflexivity].
Ltac namespace_call id := eapply certified_call_edge with (vf:=Vptr (namespace_symbol id) Ptrofs.zero);
  [reflexivity|namespace_function| |reflexivity|reflexivity].

Lemma namespace_local_int_value e le m id object value :
  e!id = Some (object,tint) -> Mem.load Mint32 m object 0 = Some (Vint value) ->
  expression_value namespace_ge e le m (Evar id tint) (Vint value).
Proof.
  intros LOCAL LOAD; eapply location_read_value; [apply local_location_value; exact LOCAL|].
  eapply deref_loc_value; [reflexivity|exact LOAD].
Qed.

Lemma namespace_global_int_value e le m id value :
  e!id = None -> Genv.find_symbol namespace_ge id = Some (namespace_symbol id) ->
  Mem.load Mint32 m (namespace_symbol id) 0 = Some (Vint value) ->
  expression_value namespace_ge e le m (Evar id tint) (Vint value).
Proof.
  intros GLOBAL SYMBOL LOAD; eapply location_read_value;
    [apply global_location_value; eassumption|].
  eapply deref_loc_value; [reflexivity|exact LOAD].
Qed.

Lemma namespace_local_address e le m id ty object : e!id = Some (object,ty) ->
  expression_value namespace_ge e le m (Eaddrof (Evar id ty) (tptr ty)) (Vptr object Ptrofs.zero).
Proof.
  intro LOCAL; split; [apply eval_Eaddrof; apply eval_Evar_local; exact LOCAL|].
  intros other VALUE; inversion VALUE; subst.
  - match goal with LOCATION : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ =>
      inversion LOCATION; subst; try congruence end; f_equal; congruence.
  - match goal with LOCATION : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion LOCATION end.
Qed.

Theorem namespace_create_call_source e le m k input output errors pipe child :
  e!_create_entry_child = None -> e!_pipefd = Some (pipe,tarray tint 2) ->
  e!_child = Some (child,tint) -> le!_error = Some (Vint Int.zero) ->
  le!_input = Some (Vint input) -> le!_output = Some (Vint output) ->
  le!_errors = Some (Vint errors) ->
  store_path namespace_ge (fun _ => True)
    (State f_namespace_init (namespace_tail 9) k e le m) 4
    (Callstate (Internal f_create_entry_child)
      [Vint input;Vint output;Vint errors;Vptr pipe Ptrofs.zero;Vptr child Ptrofs.zero]
      (namespace_creation_cont e le k) m).
Proof.
  intros GLOBAL PIPE CHILD ERROR INPUT OUTPUT ERRORS.
  unfold namespace_creation_cont,namespace_creation_set,namespace_tail,child_tail; cbn [fn_body].
  child_route.
  eapply store_next; [exact I|apply certified_if_edge with (v:=Vint Int.one) (b:=true)|].
  - apply old_expression_value; eapply value_unary; [apply value_temp; exact ERROR|reflexivity].
  - reflexivity.
  - child_route; eapply store_next; [exact I|namespace_call _create_entry_child|apply store_done; exact I].
    child_argument; child_argument; child_argument.
    eapply cons_argument_values with (v:=Vptr pipe Ptrofs.zero); [|reflexivity|].
    + eapply binary_expression_value.
      * eapply location_read_value; [apply local_location_value; exact PIPE|].
        apply deref_loc_reference; reflexivity.
      * apply old_expression_value,value_int.
      * reflexivity.
    + eapply cons_argument_values with (v:=Vptr child Ptrofs.zero);
        [apply namespace_local_address; exact CHILD|reflexivity|apply no_argument_values].
Qed.

Definition namespace_created_env le :=
  PTree.set _error (Vint Int.zero) (PTree.set _t'10 (Vint Int.zero) le).

Theorem namespace_create_return_source e le m k :
  store_path namespace_ge (fun _ => True)
    (Returnstate (Vint Int.zero) (namespace_creation_cont e le k) m) 7
    (State f_namespace_init (namespace_tail 11) k e (namespace_created_env le) m).
Proof.
  unfold namespace_creation_cont,namespace_creation_set,namespace_created_env.
  child_route; child_route; child_set.
  - apply old_expression_value,value_temp; apply PTree.gss.
  - child_route; unfold namespace_tail,child_tail; cbn [fn_body]; child_route.
    eapply store_next; [exact I|apply certified_if_edge with (v:=Vint Int.zero) (b:=false)|].
    + apply old_expression_value,value_temp; apply PTree.gss.
    + reflexivity.
    + child_route; apply store_done; exact I.
Qed.

Definition namespace_admit_guard :=
  match namespace_phase 24 with Ssequence _ guard => guard | _ => Sskip end.
Definition namespace_admit_env (le:temp_env) (_child _cgroup:int) := le.
Definition namespace_admit_cont e le (child cgroup:int) k :=
  Kcall (Some _t'12) f_namespace_init e le
    (Kseq namespace_admit_guard (Kseq (namespace_tail 25) k)).

Theorem namespace_admit_call_source e le m k child cgroup status :
  e!_admit_child = None -> e!_status = Some (status,tint) ->
  le!_launch_child = Some (Vint child) -> le!_launch_cgroup = Some (Vint cgroup) ->
  store_path namespace_ge (fun _ => True)
    (State f_namespace_init (namespace_tail 24) k e le m) 3
    (Callstate (Internal f_admit_child) [Vint child;Vint cgroup;Vptr status Ptrofs.zero]
      (namespace_admit_cont e le child cgroup k) m).
Proof.
  intros ADMIT STATUS CHILD CGROUP.
  unfold namespace_admit_cont,namespace_admit_guard,namespace_phase,namespace_tail,child_tail;cbn[fn_body].
  child_route;child_route;eapply store_next;[exact I|namespace_call _admit_child|apply store_done;exact I].
  child_argument;child_argument.
  eapply cons_argument_values with(v:=Vptr status Ptrofs.zero);
    [apply namespace_local_address;exact STATUS|reflexivity|apply no_argument_values].
Qed.

Definition namespace_close_cont e le index k :=
  Kcall None f_namespace_init e le (Kseq (namespace_tail (S index)) k).

Theorem namespace_close_call_source e le m k index id descriptor :
  namespace_tail index =
    Ssequence (Scall None (Evar _close (Tfunction [tint] tint cc_default))
      [Etempvar id tint]) (namespace_tail (S index)) ->
  e!_close = None -> le!id = Some (Vint descriptor) ->
  store_path namespace_ge (fun _ => True)
    (State f_namespace_init (namespace_tail index) k e le m) 2
    (Callstate close_definition [Vint descriptor] (namespace_close_cont e le index k) m).
Proof.
  intros SOURCE GLOBAL VALUE; rewrite SOURCE; unfold namespace_close_cont; child_route.
  eapply store_next; [exact I|namespace_call _close|apply store_done; exact I].
  child_argument; apply no_argument_values.
Qed.

Theorem namespace_close_return_source e le m k index returned :
  store_path namespace_ge (fun _ => True)
    (Returnstate returned (namespace_close_cont e le index k) m) 2
    (State f_namespace_init (namespace_tail (S index)) k e le m).
Proof. unfold namespace_close_cont; child_route; child_route; apply store_done; exact I. Qed.

Theorem namespace_close_phase_source index id :
  nth_error [_input;_output;_errors;_parentfd] index = Some id ->
  namespace_tail (11+index)%nat =
    Ssequence (Scall None (Evar _close (Tfunction [tint] tint cc_default))
      [Etempvar id tint]) (namespace_tail (S(11+index)%nat)).
Proof.
  destruct index as [|[|[|[|rest]]]]; cbn; intros SOURCE;
    try solve [inversion SOURCE; reflexivity].
  destruct rest; discriminate.
Qed.

Definition namespace_close_event descriptor reply :=
  namespace_process (process_entry (entry_library (close_returned descriptor reply))).

Theorem namespace_close_phase_run cell e le before after k index id descriptor reply :
  nth_error [_input;_output;_errors;_parentfd] index = Some id ->
  e!_close = None -> le!id = Some (Vint descriptor) -> close_effect cell before reply after ->
  namespace_steps namespace_ge cell
    (live (State f_namespace_init (namespace_tail (11+index)%nat) k e le before))
    (repeat namespace_source_event 2 ++ [namespace_close_event descriptor reply] ++
      repeat namespace_source_event 2)
    (live (State f_namespace_init (namespace_tail (S(11+index)%nat)) k e le after)).
Proof.
  intros SOURCE GLOBAL VALUE CLOSE.
  eapply namespace_steps_append; [eapply namespace_store_path_actual;
    eapply namespace_close_call_source; [apply namespace_close_phase_source; exact SOURCE|exact GLOBAL|exact VALUE]|].
  eapply namespace_steps_cons.
  - apply namespace_process_step,process_entry_step,entry_library_step,close_step; exact CLOSE.
  - eapply namespace_store_path_actual,namespace_close_return_source.
Qed.

Definition namespace_parent_checked_env le child := PTree.set _t'91 (Vint child) le.

Theorem namespace_parent_child_source e le m k object child :
  e!_child = Some (object,tint) -> Mem.load Mint32 m object 0 = Some (Vint child) ->
  0 <= Int.signed child ->
  store_path namespace_ge (fun _ => True)
    (State f_namespace_init (namespace_tail 15) k e le m) 6
    (State f_namespace_init (namespace_tail 16) k e (namespace_parent_checked_env le child) m).
Proof.
  intros CHILD VALUE NONNEGATIVE; unfold namespace_tail,child_tail; cbn [fn_body].
  child_route; child_route; child_set.
  - eapply namespace_local_int_value; [exact CHILD|exact VALUE].
  - child_route.
    eapply store_next; [exact I|apply certified_if_edge with (v:=Vint Int.zero) (b:=false)|].
    + eapply binary_expression_value; [apply old_expression_value,value_temp; apply PTree.gss|
        apply old_expression_value,value_int|].
      change (Some (Val.of_bool (Int.lt child Int.zero)) = Some (Vint Int.zero)).
      unfold Int.lt; rewrite Int.signed_zero; destruct (zlt (Int.signed child) 0); [lia|reflexivity].
    + reflexivity.
    + child_route; apply store_done; exact I.
Qed.

Definition namespace_admission_ready_env le :=
  PTree.set _bad (Vint Int.zero)
    (PTree.set _leader_done (Vint Int.zero) (PTree.set _entered (Vint Int.zero) le)).

Theorem namespace_admission_initialize_source e le before after k status :
  e!_status = Some (status,tint) -> Mem.store Mint32 before status 0 (Vint Int.zero) = Some after ->
  store_path namespace_ge (fun _ => True)
    (State f_namespace_init (namespace_tail 16) k e le before) 12
    (State f_namespace_init (namespace_tail 20) k e (namespace_admission_ready_env le) after).
Proof.
  intros STATUS STORE; unfold namespace_admission_ready_env,namespace_tail,child_tail; cbn [fn_body].
  child_route; eapply store_next; [exact I| |].
  - eapply assignment_source_edge with (v:=Vint Int.zero) (w:=Vint Int.zero).
    + apply local_location_value; exact STATUS.
    + apply old_expression_value,value_int.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|exact STORE].
  - child_route; child_route; child_set.
    + apply old_expression_value,value_int.
    + child_route; child_route; child_set.
      * apply old_expression_value,value_int.
      * child_route; child_route; child_set.
        -- apply old_expression_value,value_int.
        -- child_route; apply store_done; exact I.
Qed.

Theorem namespace_close_preserves_load cell before after reply chunk object offset value :
  close_effect cell before reply after -> object <> tls_block cell ->
  Mem.load chunk before object offset = Some value -> Mem.load chunk after object offset = Some value.
Proof.
  intros CLOSE DIFFERENT LOAD; eapply Mem.load_unchanged_on;
    [eapply close_preserves_outside_tls; exact CLOSE| |exact LOAD].
  intros position RANGE; left; exact DIFFERENT.
Qed.

Theorem namespace_close_preserves_access cell before after reply chunk object offset permission :
  close_effect cell before reply after -> Mem.valid_access before chunk object offset permission ->
  Mem.valid_access after chunk object offset permission.
Proof.
  intros CLOSE [PERMISSIONS ALIGN]; split; [|exact ALIGN].
  intros position RANGE.
  apply (proj2 (close_preserves_permissions _ _ _ _ CLOSE object position Cur permission)).
  apply PERMISSIONS; exact RANGE.
Qed.

Definition namespace_parent_ready_env le child :=
  namespace_admission_ready_env (namespace_parent_checked_env (namespace_created_env le) child).

(* §FS-entry.release: Immutable caller temporaries retain exactly the selected source values. *)
Definition namespace_launch_env le child peer cgroup checking :=
  PTree.set _launch_check(Vint checking)(PTree.set _launch_cgroup(Vint cgroup)
    (PTree.set _launch_peer(Vint peer)(PTree.set _launch_child(Vint child)le))).
Definition namespace_launch_values le child peer cgroup checking :=
  le!_launch_child=Some(Vint child) /\le!_launch_peer=Some(Vint peer) /\
    le!_launch_cgroup=Some(Vint cgroup) /\le!_launch_check=Some(Vint checking).

Lemma namespace_launch_values_set le child peer cgroup checking :
  namespace_launch_values(namespace_launch_env le child peer cgroup checking)child peer cgroup checking.
Proof. unfold namespace_launch_values,namespace_launch_env;repeat split;WriteAll.lookup. Qed.

Theorem namespace_launch_capture_source e le memory k childobject pipe child peer cgroup checking :
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  Mem.load Mint32 memory childobject 0=Some(Vint child) ->
  Mem.load Mint32 memory pipe 0=Some(Vint peer) ->
  Mem.load Mint32 memory(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 memory(namespace_symbol _preflight)0=Some(Vint checking) ->
  store_path namespace_ge(fun current=>current=memory)
    (State f_namespace_init(namespace_tail 20)k e le memory)12
    (State f_namespace_init(namespace_tail 24)k e(namespace_launch_env le child peer cgroup checking)memory).
Proof.
  intros CHILD PIPE CGROUP PREFLIGHT PID PEER CGFD CHECK.
  unfold namespace_launch_env,namespace_tail,child_tail;cbn[fn_body].
  child_route;child_set.
  - eapply namespace_local_int_value;[exact CHILD|exact PID].
  - child_route;child_route;child_set.
    + eapply location_read_value with(b:=pipe)(ofs:=Ptrofs.zero).
      * apply pointer_location_value;eapply binary_expression_value.
        -- eapply location_read_value;[apply local_location_value;exact PIPE|apply deref_loc_reference;reflexivity].
        -- apply old_expression_value,value_int.
        -- reflexivity.
      * eapply deref_loc_value;[reflexivity|exact PEER].
    + child_route;child_route;child_set.
      * eapply namespace_global_int_value;[exact CGROUP|reflexivity|exact CGFD].
      * child_route;child_route;child_set.
        -- eapply namespace_global_int_value;[exact PREFLIGHT|reflexivity|exact CHECK].
        -- child_route;apply store_done;reflexivity.
Qed.

Theorem namespace_parent_admission_source cell e le m0 m1 m2 m3 m4 k
    input output errors parentfd childobject child cgroup status pipe peer checking reply0 reply1 reply2 reply3 :
  e!_close = None -> e!_admit_child = None -> e!_admission_cgroup = None ->e!_preflight=None ->
  e!_child = Some (childobject,tint) -> e!_status = Some (status,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->
  le!_input = Some (Vint input) -> le!_output = Some (Vint output) ->
  le!_errors = Some (Vint errors) -> le!_parentfd = Some (Vint parentfd) ->
  Mem.load Mint32 m0 childobject 0 = Some (Vint child) -> 0 <= Int.signed child ->
  Mem.load Mint32 m0 (namespace_symbol _admission_cgroup) 0 = Some (Vint cgroup) ->
  Mem.load Mint32 m0 pipe 0=Some(Vint peer) ->
  Mem.load Mint32 m0(namespace_symbol _preflight)0=Some(Vint checking) ->
  childobject <> tls_block cell -> namespace_symbol _admission_cgroup <> tls_block cell ->
  pipe<>tls_block cell ->namespace_symbol _preflight<>tls_block cell ->
  childobject <> status -> namespace_symbol _admission_cgroup <> status ->
  pipe<>status ->namespace_symbol _preflight<>status ->
  Mem.valid_access m0 Mint32 status 0 Writable ->
  close_effect cell m0 reply0 m1 -> close_effect cell m1 reply1 m2 ->
  close_effect cell m2 reply2 m3 -> close_effect cell m3 reply3 m4 ->
  exists after events,
    namespace_steps namespace_ge cell
      (live (Returnstate (Vint Int.zero) (namespace_creation_cont e le k) m0)) events
      (live (Callstate (Internal f_admit_child) [Vint child;Vint cgroup;Vptr status Ptrofs.zero]
        (namespace_admit_cont e (namespace_launch_env(namespace_parent_ready_env le child)child peer cgroup checking) child cgroup k) after)) /\
    Mem.load Mint32 after childobject 0 = Some (Vint child) /\
    Mem.load Mint32 after (namespace_symbol _admission_cgroup) 0 = Some (Vint cgroup) /\
    Mem.load Mint32 after status 0 = Some (Vint Int.zero).
Proof.
  intros CLOSE ADMIT CGROUP PREFLIGHT CHILD STATUS PIPE INPUT OUTPUT ERRORS PARENT PID NONNEGATIVE CGFD
    PEER_VALUE CHECK_VALUE CHILD_TLS CG_TLS PIPE_TLS CHECK_TLS CHILD_STATUS CG_STATUS
    PIPE_STATUS CHECK_STATUS ACCESS C0 C1 C2 C3.
  assert (PID4 : Mem.load Mint32 m4 childobject 0 = Some (Vint child)).
  { eapply namespace_close_preserves_load; [exact C3|exact CHILD_TLS|].
    eapply namespace_close_preserves_load; [exact C2|exact CHILD_TLS|].
    eapply namespace_close_preserves_load; [exact C1|exact CHILD_TLS|].
    eapply namespace_close_preserves_load; [exact C0|exact CHILD_TLS|exact PID]. }
  assert (CG4 : Mem.load Mint32 m4 (namespace_symbol _admission_cgroup) 0 = Some (Vint cgroup)).
  { eapply namespace_close_preserves_load; [exact C3|exact CG_TLS|].
    eapply namespace_close_preserves_load; [exact C2|exact CG_TLS|].
    eapply namespace_close_preserves_load; [exact C1|exact CG_TLS|].
    eapply namespace_close_preserves_load; [exact C0|exact CG_TLS|exact CGFD]. }
  assert(PEER4:Mem.load Mint32 m4 pipe 0=Some(Vint peer)).
  { eapply namespace_close_preserves_load;[exact C3|exact PIPE_TLS|].
    eapply namespace_close_preserves_load;[exact C2|exact PIPE_TLS|].
    eapply namespace_close_preserves_load;[exact C1|exact PIPE_TLS|].
    eapply namespace_close_preserves_load;[exact C0|exact PIPE_TLS|exact PEER_VALUE]. }
  assert(CHECK4:Mem.load Mint32 m4(namespace_symbol _preflight)0=Some(Vint checking)).
  { eapply namespace_close_preserves_load;[exact C3|exact CHECK_TLS|].
    eapply namespace_close_preserves_load;[exact C2|exact CHECK_TLS|].
    eapply namespace_close_preserves_load;[exact C1|exact CHECK_TLS|].
    eapply namespace_close_preserves_load;[exact C0|exact CHECK_TLS|exact CHECK_VALUE]. }
  assert (ACCESS4 : Mem.valid_access m4 Mint32 status 0 Writable).
  { eapply namespace_close_preserves_access; [exact C3|].
    eapply namespace_close_preserves_access; [exact C2|].
    eapply namespace_close_preserves_access; [exact C1|].
    eapply namespace_close_preserves_access; [exact C0|exact ACCESS]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint Int.zero) ACCESS4) as [after STORE].
  assert (PID5 : Mem.load Mint32 after childobject 0 = Some (Vint child)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ STORE) by (left; exact CHILD_STATUS); exact PID4. }
  assert (CG5 : Mem.load Mint32 after (namespace_symbol _admission_cgroup) 0 = Some (Vint cgroup)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ STORE) by (left; exact CG_STATUS); exact CG4. }
  assert(PEER5:Mem.load Mint32 after pipe 0=Some(Vint peer)).
  { rewrite(Mem.load_store_other _ _ _ _ _ _ STORE)by(left;exact PIPE_STATUS);exact PEER4. }
  assert(CHECK5:Mem.load Mint32 after(namespace_symbol _preflight)0=Some(Vint checking)).
  { rewrite(Mem.load_store_other _ _ _ _ _ _ STORE)by(left;exact CHECK_STATUS);exact CHECK4. }
  exists after; eexists; split.
  - eapply namespace_steps_append; [eapply namespace_store_path_actual,namespace_create_return_source|].
    eapply namespace_steps_append.
    + apply namespace_close_phase_run with (index:=0%nat) (id:=_input) (reply:=reply0);
        [reflexivity|exact CLOSE|unfold namespace_created_env; WriteAll.lookup|exact C0].
    + eapply namespace_steps_append.
      * apply namespace_close_phase_run with (index:=1%nat) (id:=_output) (reply:=reply1);
          [reflexivity|exact CLOSE|unfold namespace_created_env; WriteAll.lookup|exact C1].
      * eapply namespace_steps_append.
        -- apply namespace_close_phase_run with (index:=2%nat) (id:=_errors) (reply:=reply2);
             [reflexivity|exact CLOSE|unfold namespace_created_env; WriteAll.lookup|exact C2].
        -- eapply namespace_steps_append.
           ++ apply namespace_close_phase_run with (index:=3%nat) (id:=_parentfd) (reply:=reply3);
                [reflexivity|exact CLOSE|unfold namespace_created_env; WriteAll.lookup|exact C3].
           ++ eapply namespace_steps_append.
              ** eapply namespace_store_path_actual; eapply namespace_parent_child_source;
                   [exact CHILD|exact PID4|exact NONNEGATIVE].
              ** eapply namespace_steps_append.
                 --- eapply namespace_store_path_actual; eapply namespace_admission_initialize_source;
                       [exact STATUS|exact STORE].
                 --- eapply namespace_steps_append.
                     +++ eapply namespace_store_path_actual,namespace_launch_capture_source;
                           [exact CHILD|exact PIPE|exact CGROUP|exact PREFLIGHT|exact PID5|exact PEER5|exact CG5|exact CHECK5].
                     +++ eapply namespace_store_path_actual,namespace_admit_call_source;
                           [exact ADMIT|exact STATUS|unfold namespace_launch_env;WriteAll.lookup|unfold namespace_launch_env;WriteAll.lookup].
  - split; [exact PID5|]. split; [exact CG5|].
    rewrite (Mem.load_store_same _ _ _ _ _ _ STORE); reflexivity.
Qed.
