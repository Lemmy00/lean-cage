(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Resolve an exact source occurrence, including committed writes with lost acknowledgement. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessJournal ProcessMachine ProcessCaller ProcessGlobalCalls ProcessReleaseSafety.
From EntryReporting Require Import ResultLayout.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller NamespaceSocket
  NamespaceParentEntry NamespaceParentSafety NamespaceGrantAuthorization NamespaceGrantCut NamespaceGrantCaller NamespaceRelease.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_positive_fork_write_occurrence cell pair child_temps failure e le before input output errors parent childobject pipe status
    child peer cgroup temporary admission report sequence events target ordinal event io:
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
    (live(Returnstate(Vint child)(child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))before))events target ->
  nth_error events ordinal=Some event ->
  namespace_socket_io event=Some io ->operation(source_socket_request io)=writing ->
  descriptor(source_socket_request io)=peer ->
  exists finish_prefix setup_prefix ready grant_prefix release_prefix resume_ordinal,
    Forall(fun event=>namespace_parent_prelude_event event=true)(finish_prefix++setup_prefix) /\
    Forall(namespace_parent_closes_from[failure;input;output;errors;parent])(finish_prefix++setup_prefix) /\
    firstn ordinal events=finish_prefix++setup_prefix++grant_prefix++release_prefix /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint child)(child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))before))
      (finish_prefix++setup_prefix)
      (live(State f_namespace_init(namespace_tail 20)Kstop e(namespace_parent_setup_env le child)ready)) /\
    namespace_authorized_parent cell ready child peer cgroup status temporary admission report sequence grant_prefix /\
    nth_error events resume_ordinal=Some(namespace_process(release_resume_event child)) /\
    (length finish_prefix+length setup_prefix+length grant_prefix<=resume_ordinal)%nat /\
    (resume_ordinal<ordinal)%nat /\requested(source_socket_request io)=1 /\
    source_socket_bytes io=[Byte.repr 165].
Proof.
  intros GLOBAL CHILD_POINTER FAILURE NONZERO INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS CGROUP PREFLIGHT
    TEMPORARY ADMISSION POSITIVE PEER CGFD CHECK CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS
    STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK CHILD_PAIR PIPE_CHILD PIPE_PAIR CGROUP_CHILD CGROUP_PAIR
    CHECK_CHILD CHECK_PAIR TLS CG_OTHER REPORT_OTHER RUN SELECTED SOCKET WRITING DESCRIPTOR.
  destruct(nth_error_split _ _ SELECTED)as[prefix[suffix[EVENTS ORDINAL]]].
  destruct(namespace_steps_at_event _ _ _ _ _ _ _ _ RUN EVENTS)
    as[middle[next[PREFIX[STEP SUFFIX]]]].
  destruct(namespace_socket_step_call _ _ _ _ _ _ STEP SOCKET)as[k[memory CURRENT]].
  rewrite WRITING in CURRENT;subst middle.
  destruct(actual_positive_fork_private_grant cell pair child_temps failure e le before input output errors parent childobject
    pipe status child peer cgroup temporary admission report sequence prefix _ _ _ _ event next io GLOBAL
    CHILD_POINTER FAILURE NONZERO INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS CGROUP PREFLIGHT
    TEMPORARY ADMISSION POSITIVE PEER CGFD CHECK CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS
    STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK CHILD_PAIR PIPE_CHILD PIPE_PAIR CGROUP_CHILD CGROUP_PAIR
    CHECK_CHILD CHECK_PAIR TLS CG_OTHER REPORT_OTHER PREFIX STEP SOCKET WRITING DESCRIPTOR)
    as[finish_prefix[setup_prefix[ready[grant_prefix[release_prefix[resume_ordinal
      [QUIET[CLOSED[ORDER[SETUP[AUTHORIZED[RESUME[AFTER[BEFORE[COUNT BYTES]]]]]]]]]]]]]]].
  exists finish_prefix,setup_prefix,ready,grant_prefix,release_prefix,resume_ordinal.
  split;[exact QUIET|]. split;[exact CLOSED|]. split.
  - rewrite EVENTS. rewrite <-ORDINAL. rewrite firstn_app,firstn_all,Nat.sub_diag. cbn;rewrite app_nil_r;exact ORDER.
  - split;[exact SETUP|]. split;[exact AUTHORIZED|]. split.
    + rewrite EVENTS,nth_error_app1 by exact BEFORE;exact RESUME.
    + split;[exact AFTER|]. rewrite <-ORDINAL;auto.
Qed.


Lemma recorded_parent_subtract_successor whole prefix rest:
  (S prefix<=whole)%nat ->(whole-prefix=S rest)%nat ->(whole-S prefix=rest)%nat.
Proof. intros;lia. Qed.
Lemma recorded_parent_add_after_fork prefix offset:
  (S prefix+offset-prefix=S offset)%nat.
Proof. lia. Qed.
Lemma recorded_parent_relative_before prefix offset selected:
  (S prefix<=selected)%nat ->(offset<selected-S prefix)%nat ->
  (S prefix<=S prefix+offset<selected)%nat.
Proof. intros;lia. Qed.

Theorem actual_recorded_positive_fork_write cell pair child_temps failure e le before input output errors parent childobject pipe status
    child peer cgroup temporary admission report sequence run common body ordinal event io:
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
  source_cell run=cell ->
  source_events run=common++namespace_forked child::body ->
  namespace_steps namespace_ge cell
    (live(Returnstate(Vint child)(child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))before))body(source_after run) ->
  (S(length common)<=ordinal)%nat ->nth_error(source_events run)ordinal=Some event ->
  namespace_socket_io event=Some io ->operation(source_socket_request io)=writing ->
  descriptor(source_socket_request io)=peer ->
  exists finish_prefix setup_prefix ready grant_prefix release_prefix resume_ordinal,
    Forall(fun event=>namespace_parent_prelude_event event=true)(finish_prefix++setup_prefix) /\
    Forall(namespace_parent_closes_from[failure;input;output;errors;parent])(finish_prefix++setup_prefix) /\
    firstn(ordinal-S(length common))body=finish_prefix++setup_prefix++grant_prefix++release_prefix /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint child)(child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))before))
      (finish_prefix++setup_prefix)
      (live(State f_namespace_init(namespace_tail 20)Kstop e(namespace_parent_setup_env le child)ready)) /\
    namespace_authorized_parent cell ready child peer cgroup status temporary admission report sequence grant_prefix /\
    nth_error(source_events run)resume_ordinal=Some(namespace_process(release_resume_event child)) /\
    (S(length common)+length finish_prefix+length setup_prefix+length grant_prefix<=resume_ordinal)%nat /\
    (S(length common)<=resume_ordinal<ordinal)%nat /\requested(source_socket_request io)=1 /\
    source_socket_bytes io=[Byte.repr 165].
Proof.
  intros GLOBAL CHILD_POINTER FAILURE NONZERO INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS CGROUP PREFLIGHT
    TEMPORARY ADMISSION POSITIVE PEER CGFD CHECK CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS
    STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK CHILD_PAIR PIPE_CHILD PIPE_PAIR CGROUP_CHILD CGROUP_PAIR
    CHECK_CHILD CHECK_PAIR TLS CG_OTHER REPORT_OTHER CELL WHOLE RUN LOWER SELECTED SOCKET WRITING DESCRIPTOR.
  assert(BODY_SELECTED:nth_error body(ordinal-S(length common))=Some event).
  { rewrite WHOLE,nth_error_app2 in SELECTED by lia.
    destruct(ordinal-length common)%nat as[|remaining]eqn:REMAINING;[lia|].
    change(nth_error body remaining=Some event)in SELECTED.
    rewrite(recorded_parent_subtract_successor _ _ _ LOWER REMAINING);exact SELECTED. }
  destruct(actual_positive_fork_write_occurrence cell pair child_temps failure e le before input output errors parent childobject
    pipe status child peer cgroup temporary admission report sequence body(source_after run)(ordinal-S(length common))event io
    GLOBAL CHILD_POINTER FAILURE NONZERO INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS CGROUP PREFLIGHT
    TEMPORARY ADMISSION POSITIVE PEER CGFD CHECK CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS
    STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK CHILD_PAIR PIPE_CHILD PIPE_PAIR CGROUP_CHILD CGROUP_PAIR
    CHECK_CHILD CHECK_PAIR TLS CG_OTHER REPORT_OTHER RUN BODY_SELECTED SOCKET WRITING DESCRIPTOR)
    as[finish_prefix[setup_prefix[ready[grant_prefix[release_prefix[resume
      [QUIET[CLOSED[ORDER[SETUP[AUTHORIZED[RESUMED[AFTER[BEFORE[COUNT BYTES]]]]]]]]]]]]]]].
  exists finish_prefix,setup_prefix,ready,grant_prefix,release_prefix,(S(length common)+resume)%nat.
  split;[exact QUIET|]. split;[exact CLOSED|]. split;[exact ORDER|]. split;[exact SETUP|]. split;[exact AUTHORIZED|]. split.
  - rewrite WHOLE,nth_error_app2 by lia.
    rewrite recorded_parent_add_after_fork;exact RESUMED.
  - split;[lia|]. split;[apply recorded_parent_relative_before;assumption|auto].
Qed.
