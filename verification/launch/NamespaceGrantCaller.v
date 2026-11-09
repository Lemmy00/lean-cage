(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The fork parent's actual execution produces its checked private grant. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessReleaseSafety ProcessCaller ProcessGlobalCalls.
From EntryReporting Require Import ResultLayout.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller NamespaceSocket
  NamespaceParentEntry NamespaceParentSafety NamespaceGrantAuthorization NamespaceGrantCut NamespaceRelease
  NamespaceReleaseProjection NamespaceTLS NamespaceForkParent.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_fork_parent_private_grant cell e le before input output errors parent childobject pipe status
    child peer cgroup temporary admission report sequence events called arguments continuation final event after io:
  caller_env_global e ->
  le!_input=Some(Vint input) ->le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  le!_parentfd=Some(Vint parent) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->e!_status=Some(status,tint) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  e!__res__6=Some(temporary,result_type) ->e!_admission=Some(admission,result_type) ->
  Mem.load Mint32 before childobject 0=Some(Vint child) ->0<=Int.signed child ->
  Mem.load Mint32 before pipe 0=Some(Vint peer) ->
  Mem.load Mint32 before(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 before(namespace_symbol _preflight)0=Some(Vint Int.zero) ->
  childobject<>tls_block cell ->pipe<>tls_block cell ->
  namespace_symbol _admission_cgroup<>tls_block cell ->namespace_symbol _preflight<>tls_block cell ->
  status<>childobject ->status<>pipe ->status<>namespace_symbol _admission_cgroup ->status<>namespace_symbol _preflight ->
  Mem.valid_block before(tls_block cell) ->cgroup<>peer ->report<>peer ->
  namespace_steps namespace_ge cell
    (live(Returnstate(Vint Int.zero)(namespace_creation_cont e le Kstop)before))events
    (live(Callstate called arguments continuation final)) ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))event after ->
  namespace_socket_io event=Some io ->operation(source_socket_request io)=writing ->
  descriptor(source_socket_request io)=peer ->
  exists setup_prefix ready grant_prefix release_prefix resume_ordinal,
    Forall(fun event=>namespace_parent_prelude_event event=true)setup_prefix /\
    Forall(namespace_parent_closes_from[input;output;errors;parent])setup_prefix /\
    events=setup_prefix++grant_prefix++release_prefix /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(namespace_creation_cont e le Kstop)before))setup_prefix
      (live(State f_namespace_init(namespace_tail 20)Kstop e(namespace_parent_setup_env le child)ready)) /\
    namespace_authorized_parent cell ready child peer cgroup status temporary admission report sequence grant_prefix /\
    nth_error events resume_ordinal=Some(namespace_process(release_resume_event child)) /\
    (length setup_prefix+length grant_prefix<=resume_ordinal)%nat /\
    (resume_ordinal<length events)%nat /\requested(source_socket_request io)=1 /\
    source_socket_bytes io=[Byte.repr 165].
Proof.
  intros GLOBAL INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION
    PID POSITIVE PEER CGFD CHECK CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS
    STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK TLS CG_OTHER REPORT_OTHER RUN WRITE SOCKET WRITING DESCRIPTOR.
  assert(CLOSE:e!_close=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(OUTSIDE:called<>close_definition).
  { intro SAME;subst called.
    destruct(namespace_socket_step_call _ _ _ _ _ _ WRITE SOCKET)as[k[memory IMPOSSIBLE]].
    rewrite WRITING in IMPOSSIBLE;discriminate IMPOSSIBLE. }
  destruct(actual_parent_creation_reaches_setup cell e le before Kstop input output errors parent childobject pipe status
    child peer cgroup Int.zero report sequence events called arguments continuation final
    CLOSE INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS PID POSITIVE PEER CGFD CHECK
    CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK TLS OUTSIDE RUN)
    as[setup_prefix[ready[rest[QUIET[CLOSED[EVENTS[SETUP[CONTINUE[PID'[PEER'[CGFD'[CHECK'[STATUS'[TLS'[BAD'[REPORT' SEQUENCE']]]]]]]]]]]]]]]].
  assert(PRIVATE:private_namespace_write peer event)by(exists io;auto).
  destruct(actual_private_parent_write_authorized cell e(namespace_parent_setup_env le child)ready childobject pipe child peer
    cgroup status temporary admission report sequence rest called arguments continuation final event after
    GLOBAL CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION PID' PEER' CGFD' CHECK' BAD' REPORT' SEQUENCE' TLS'
    CG_OTHER REPORT_OTHER CONTINUE WRITE PRIVATE)
    as[grant_prefix[release_prefix[release_temps[released[local[next[ORDER[AUTHORIZED[PREFIX[RELEASE STEP]]]]]]]]]].
  assert(RELEASE_TLS:Mem.valid_block released(tls_block cell)).
  { eapply(namespace_steps_tls_valid namespace_ge cell _ _ _ PREFIX TLS'). }
  assert(HELPER:namespace_steps namespace_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop released))(release_prefix++[event])next).
  { eapply namespace_steps_append;[exact RELEASE|econstructor;[exact STEP|constructor]]. }
  destruct(actual_namespace_release_socket_checked_from_live_tls cell released child peer
    (release_prefix++[event])next release_prefix event[]io RELEASE_TLS HELPER eq_refl SOCKET)
    as[RESUMED[WRITING'[DESCRIPTOR'[COUNT BYTES]]]].
  apply In_nth_error in RESUMED as[resume_offset RESUME].
  assert(OFFSET:(resume_offset<length release_prefix)%nat).
  { apply nth_error_Some;rewrite RESUME;discriminate. }
  exists setup_prefix,ready,grant_prefix,release_prefix,(length setup_prefix+length grant_prefix+resume_offset)%nat.
  assert(FULL:events=setup_prefix++grant_prefix++release_prefix)by(rewrite EVENTS,ORDER;reflexivity).
  split;[exact QUIET|]. split;[exact CLOSED|]. split;[exact FULL|]. split;[exact SETUP|]. split;[exact AUTHORIZED|]. split.
  - rewrite FULL,nth_error_app2 by lia.
    replace(length setup_prefix+length grant_prefix+resume_offset-length setup_prefix)%nat
      with(length grant_prefix+resume_offset)%nat by lia.
    rewrite nth_error_app2 by lia.
    replace(length grant_prefix+resume_offset-length grant_prefix)%nat with resume_offset by lia;exact RESUME.
  - split;[lia|]. split;[rewrite FULL,!app_length;lia|auto].
Qed.

Theorem actual_positive_fork_private_grant cell pair child_temps failure e le before input output errors parent childobject pipe status
    child peer cgroup temporary admission report sequence events called arguments continuation final event after io:
  caller_env_global e ->child_temps!_child=Some(Vptr childobject Ptrofs.zero) ->
  child_temps!_failure=Some(Vint failure) ->child<>Int.zero ->
  le!_input=Some(Vint input) ->le!_output=Some(Vint output) ->le!_errors=Some(Vint errors) ->
  le!_parentfd=Some(Vint parent) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->e!_status=Some(status,tint) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  e!__res__6=Some(temporary,result_type) ->e!_admission=Some(admission,result_type) ->
  0<=Int.signed child ->
  Mem.load Mint32 before pipe 0=Some(Vint peer) ->
  Mem.load Mint32 before(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 before(namespace_symbol _preflight)0=Some(Vint Int.zero) ->
  childobject<>tls_block cell ->pipe<>tls_block cell ->
  namespace_symbol _admission_cgroup<>tls_block cell ->namespace_symbol _preflight<>tls_block cell ->
  status<>childobject ->status<>pipe ->status<>namespace_symbol _admission_cgroup ->status<>namespace_symbol _preflight ->
  childobject<>pair ->pipe<>childobject ->pipe<>pair ->
  namespace_symbol _admission_cgroup<>childobject ->namespace_symbol _admission_cgroup<>pair ->
  namespace_symbol _preflight<>childobject ->namespace_symbol _preflight<>pair ->
  Mem.valid_block before(tls_block cell) ->cgroup<>peer ->report<>peer ->
  namespace_steps namespace_ge cell
    (live(Returnstate(Vint child)(child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))before))events
    (live(Callstate called arguments continuation final)) ->
  namespace_step namespace_ge cell(live(Callstate called arguments continuation final))event after ->
  namespace_socket_io event=Some io ->operation(source_socket_request io)=writing ->
  descriptor(source_socket_request io)=peer ->
  exists finish_prefix setup_prefix ready grant_prefix release_prefix resume_ordinal,
    Forall(fun event=>namespace_parent_prelude_event event=true)(finish_prefix++setup_prefix) /\
    Forall(namespace_parent_closes_from[failure;input;output;errors;parent])(finish_prefix++setup_prefix) /\
    events=finish_prefix++setup_prefix++grant_prefix++release_prefix /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint child)(child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))before))
      (finish_prefix++setup_prefix)
      (live(State f_namespace_init(namespace_tail 20)Kstop e(namespace_parent_setup_env le child)ready)) /\
    namespace_authorized_parent cell ready child peer cgroup status temporary admission report sequence grant_prefix /\
    nth_error events resume_ordinal=Some(namespace_process(release_resume_event child)) /\
    (length finish_prefix+length setup_prefix+length grant_prefix<=resume_ordinal)%nat /\
    (resume_ordinal<length events)%nat /\requested(source_socket_request io)=1 /\
    source_socket_bytes io=[Byte.repr 165].
Proof.
  intros GLOBAL CHILD_POINTER FAILURE NONZERO INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS CGROUP PREFLIGHT
    TEMPORARY ADMISSION POSITIVE PEER CGFD CHECK CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS
    STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK CHILD_PAIR PIPE_CHILD PIPE_PAIR CGROUP_CHILD CGROUP_PAIR
    CHECK_CHILD CHECK_PAIR TLS CG_OTHER REPORT_OTHER RUN WRITE SOCKET WRITING DESCRIPTOR.
  assert(OUTSIDE:called<>close_definition).
  { intro SAME;subst called.
    destruct(namespace_socket_step_call _ _ _ _ _ _ WRITE SOCKET)as[k[memory IMPOSSIBLE]].
    rewrite WRITING in IMPOSSIBLE;discriminate IMPOSSIBLE. }
  destruct(actual_positive_fork_parent_return cell pair child_temps before(namespace_creation_cont e le Kstop)child failure
    childobject events called arguments continuation final CHILD_POINTER FAILURE NONZERO CHILD_TLS CHILD_PAIR OUTSIDE RUN)
    as[finish_prefix[created[rest[FINISH_QUIET[FINISH_CLOSED[EVENTS[FINISH[CONTINUE[PID FRAME]]]]]]]]].
  assert(PEER':Mem.load Mint32 created pipe 0=Some(Vint peer))by(eapply FRAME;eassumption).
  assert(CGFD':Mem.load Mint32 created(namespace_symbol _admission_cgroup)0=Some(Vint cgroup))by(eapply FRAME;eassumption).
  assert(CHECK':Mem.load Mint32 created(namespace_symbol _preflight)0=Some(Vint Int.zero))by(eapply FRAME;eassumption).
  assert(TLS':Mem.valid_block created(tls_block cell)).
  { exact(namespace_steps_tls_valid namespace_ge cell _ _ _ FINISH TLS). }
  destruct(actual_fork_parent_private_grant cell e le created input output errors parent childobject pipe status child peer cgroup
    temporary admission report sequence rest called arguments continuation final event after io GLOBAL
    INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS CGROUP PREFLIGHT TEMPORARY ADMISSION PID POSITIVE
    PEER' CGFD' CHECK' CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK TLS'
    CG_OTHER REPORT_OTHER CONTINUE WRITE SOCKET WRITING DESCRIPTOR)
    as[setup_prefix[ready[grant_prefix[release_prefix[resume_ordinal[SETUP_QUIET[SETUP_CLOSED[REST[SETUP[AUTHORIZED[RESUMED[AFTER[ORDER[COUNT BYTES]]]]]]]]]]]]]].
  exists finish_prefix,setup_prefix,ready,grant_prefix,release_prefix,(length finish_prefix+resume_ordinal)%nat.
  split;[apply Forall_app;auto|].
  split.
  { apply Forall_app;split.
    - eapply namespace_parent_closes_weaken;[|exact FINISH_CLOSED];cbn;tauto.
    - eapply namespace_parent_closes_weaken;[|exact SETUP_CLOSED];cbn;tauto. }
  split;[rewrite EVENTS,REST;reflexivity|].
  split;[eapply namespace_steps_append;[exact FINISH|exact SETUP]|].
  split;[exact AUTHORIZED|]. split.
  - rewrite EVENTS,nth_error_app2 by lia.
    rewrite(Nat.add_comm(length finish_prefix)resume_ordinal),Nat.add_sub;exact RESUMED.
  - split;[lia|]. split;[rewrite EVENTS,app_length;lia|auto].
Qed.
