(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual admission and publication guards control the sole release call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths NamespaceCaller.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Lemma namespace_admission_symbol :
  Genv.find_symbol namespace_ge _admission_cgroup=Some(namespace_symbol _admission_cgroup).
Proof. reflexivity. Qed.
Local Opaque namespace_symbol.

Definition namespace_after_admit_env le child cgroup returned :=
  PTree.set _t'12(Vint returned)(namespace_admit_env le child cgroup).
Definition namespace_checked_admit_env le child cgroup returned :=
  if Int.eq returned Int.zero then namespace_after_admit_env le child cgroup returned
  else PTree.set _bad(Vint Int.one)(namespace_after_admit_env le child cgroup returned).

Theorem namespace_admit_return_source e le m k child cgroup returned :
  exists count,store_path namespace_ge(fun _=>True)
    (Returnstate(Vint returned)(namespace_admit_cont e le child cgroup k)m)count
    (State f_namespace_init(namespace_tail 25)k e
      (namespace_checked_admit_env le child cgroup returned)m).
Proof.
  unfold namespace_admit_cont,namespace_checked_admit_env,namespace_after_admit_env.
  destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;eexists;child_route;child_route.
    eapply store_next;[exact I|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + child_route;apply store_done;exact I.
  - rewrite Int.eq_false by exact NONZERO;eexists;child_route;child_route.
    eapply store_next;[exact I|apply certified_if_edge with(v:=Vint returned)(b:=true)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + cbn;rewrite Int.eq_false by exact NONZERO;reflexivity.
    + child_set;[apply old_expression_value,value_int|].
      child_route;apply store_done;exact I.
Qed.

Theorem failed_admit_latches_bad le child cgroup returned :
  returned<>Int.zero ->(namespace_checked_admit_env le child cgroup returned)!_bad=Some(Vint Int.one).
Proof. intro NONZERO;unfold namespace_checked_admit_env;rewrite Int.eq_false by exact NONZERO;apply PTree.gss. Qed.

Definition namespace_cgroup_close_env(le:temp_env)(_cgroup:int):=le.
Definition namespace_cgroup_close_guard:=match namespace_phase 25 with Ssequence _ guard=>guard|_=>Sskip end.
Definition namespace_cgroup_close_cont e le(cgroup:int)k:=
  Kcall(Some _t'13)f_namespace_init e le
    (Kseq namespace_cgroup_close_guard(Kseq(namespace_tail 26)k)).
Definition namespace_after_cgroup_close_env le cgroup returned:=
  PTree.set _t'13(Vint returned)(namespace_cgroup_close_env le cgroup).
Definition namespace_checked_cgroup_close_env le cgroup returned:=
  if Int.eq returned Int.zero then namespace_after_cgroup_close_env le cgroup returned
  else PTree.set _bad(Vint Int.one)(namespace_after_cgroup_close_env le cgroup returned).

Theorem namespace_cgroup_close_call_source e le m k cgroup :
  e!_close=None ->le!_launch_cgroup=Some(Vint cgroup) ->
  exists count,store_path namespace_ge(fun _=>True)
    (State f_namespace_init(namespace_tail 25)k e le m)count
    (Callstate close_definition[Vint cgroup](namespace_cgroup_close_cont e le cgroup k)m).
Proof.
  intros CLOSE VALUE;unfold namespace_cgroup_close_cont,namespace_cgroup_close_guard,
    namespace_phase,namespace_tail,child_tail;cbn[fn_body].
  eexists;child_route;child_route;
    eapply store_next;[exact I|namespace_call _close|apply store_done;exact I].
  child_argument;apply no_argument_values.
Qed.

Theorem namespace_cgroup_close_return_source e le m k cgroup returned :
  exists count,store_path namespace_ge(fun _=>True)
    (Returnstate(Vint returned)(namespace_cgroup_close_cont e le cgroup k)m)count
    (State f_namespace_init(namespace_tail 26)k e(namespace_checked_cgroup_close_env le cgroup returned)m).
Proof.
  unfold namespace_cgroup_close_cont,namespace_checked_cgroup_close_env,namespace_after_cgroup_close_env.
  destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;eexists;child_route;child_route.
    eapply store_next;[exact I|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + child_route;apply store_done;exact I.
  - rewrite Int.eq_false by exact NONZERO;eexists;child_route;child_route.
    eapply store_next;[exact I|apply certified_if_edge with(v:=Vint returned)(b:=true)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + cbn;rewrite Int.eq_false by exact NONZERO;reflexivity.
    + child_set;[apply old_expression_value,value_int|].
      child_route;apply store_done;exact I.
Qed.

Theorem cgroup_close_retains_bad le cgroup returned : le!_bad=Some(Vint Int.one) ->
  (namespace_checked_cgroup_close_env le cgroup returned)!_bad=Some(Vint Int.one).
Proof.
  intro BAD;unfold namespace_checked_cgroup_close_env;destruct(Int.eq returned Int.zero);
    unfold namespace_after_cgroup_close_env,namespace_cgroup_close_env;WriteAll.lookup.
Qed.

Theorem namespace_cgroup_forget_source e le before after k :
  e!_admission_cgroup=None ->
  Mem.store Mint32 before(namespace_symbol _admission_cgroup)0(Vint Int.mone)=Some after ->
  exists count,store_path namespace_ge(fun current=>current=before\/current=after)
    (State f_namespace_init(namespace_tail 26)k e le before)count
    (State f_namespace_init(namespace_tail 27)k e le after).
Proof.
  intros GLOBAL STORE;unfold namespace_tail,child_tail;cbn[fn_body];eexists;child_route.
  eapply store_next;[left;reflexivity| |].
  - eapply assignment_source_edge.
    + apply global_location_value;[exact GLOBAL|exact namespace_admission_symbol].
    + apply old_expression_value;WriteAll.expression.
    + reflexivity.
    + eapply assign_loc_value;[reflexivity|exact STORE].
  - child_route;apply store_done;right;reflexivity.
Qed.

Theorem namespace_failed_admission_skips_report e le m k : le!_bad=Some(Vint Int.one) ->
  exists count final,final!_bad=Some(Vint Int.one) /\
    store_path namespace_ge(fun current=>current=m)
      (State f_namespace_init(namespace_tail 29)k e le m)count
      (State f_namespace_init(namespace_tail 30)k e final m).
Proof.
  intro BAD;unfold namespace_tail,child_tail;cbn[fn_body].
  eexists;exists(PTree.set _t'17(Vint Int.zero)(PTree.set _t'16(Vint Int.zero)le));split;[WriteAll.lookup|].
  child_route;child_route;child_route.
  eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - child_set;[apply old_expression_value,value_int|]. child_route.
    eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + child_set;[apply old_expression_value,value_int|]. child_route.
      eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * child_route;apply store_done;reflexivity.
Qed.

Theorem namespace_failed_admission_skips_release e le m k : le!_bad=Some(Vint Int.one) ->
  exists count final,final!_bad=Some(Vint Int.one) /\
    store_path namespace_ge(fun current=>current=m)
      (State f_namespace_init(namespace_tail 30)k e le m)count
      (State f_namespace_init(namespace_tail 31)k e final m).
Proof.
  intro BAD;unfold namespace_tail,child_tail;cbn[fn_body].
  eexists;exists(PTree.set _t'20(Vint Int.zero)le);split;[WriteAll.lookup|].
  child_route;child_route.
  eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - child_set;[apply old_expression_value,value_int|]. child_route.
    eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + child_route;apply store_done;reflexivity.
Qed.

Definition namespace_release_cast:=Sset _t'20(Ecast(Etempvar _t'21 tint)tbool).
Definition namespace_release_guard:=match namespace_phase 30 with Ssequence _ guard=>guard|_=>Sskip end.
Definition namespace_release_call_env(le:temp_env)(_child _peer:int):=le.
Definition namespace_release_cont e le(child peer:int)k:=
  Kcall(Some _t'21)f_namespace_init e le
    (Kseq namespace_release_cast(Kseq namespace_release_guard(Kseq(namespace_tail 31)k))).

Lemma namespace_peer_slot_value e le m pipe peer:
  e!_pipefd=Some(pipe,tarray tint 2) ->Mem.load Mint32 m pipe 0=Some(Vint peer) ->
  expression_value namespace_ge e le m
    (Ederef(Ebinop Oadd(Evar _pipefd(tarray tint 2))(Econst_int Int.zero tint)(tptr tint))tint)(Vint peer).
Proof.
  intros PIPE LOAD;eapply location_read_value with(b:=pipe)(ofs:=Ptrofs.zero).
  - apply pointer_location_value;eapply binary_expression_value.
    + eapply location_read_value;[apply local_location_value;exact PIPE|apply deref_loc_reference;reflexivity].
    + apply old_expression_value,value_int.
    + reflexivity.
  - eapply deref_loc_value;[reflexivity|exact LOAD].
Qed.

Theorem namespace_authorized_release_call_source e le m k child peer:
  le!_bad=Some(Vint Int.zero) ->e!_release_child=None ->
  le!_launch_child=Some(Vint child) ->le!_launch_peer=Some(Vint peer) ->
  exists count,store_path namespace_ge(fun current=>current=m)
    (State f_namespace_init(namespace_tail 30)k e le m)count
    (Callstate(Internal f_release_child)[Vint child;Vint peer](namespace_release_cont e le child peer k)m).
Proof.
  intros BAD RELEASE CHILD PEER.
  unfold namespace_release_cont,namespace_release_guard,namespace_release_cast,
    namespace_phase,namespace_tail,child_tail;cbn[fn_body].
  eexists;child_route;child_route.
  eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - child_route;eapply store_next;[reflexivity|namespace_call _release_child|apply store_done;reflexivity].
    child_argument;child_argument;apply no_argument_values.
Qed.
