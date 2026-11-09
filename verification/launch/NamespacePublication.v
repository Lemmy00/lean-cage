(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The actual public admission report must return success before release. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll LibraryMachine.
From EntryNative Require Import EntrySource.
From EntryNamespace Require Import NamespaceStructure NamespacePaths NamespaceCaller NamespaceRelease.
From EntryReporting Require Import ResultLayout.
Import ListNotations.
Open Scope Z_scope.
Lemma namespace_preflight_symbol:Genv.find_symbol namespace_ge _preflight=Some(namespace_symbol _preflight).
Proof. reflexivity. Qed.
Local Opaque namespace_ge namespace_symbol.

Definition namespace_publication_cast:=Sset _t'17(Ecast(Etempvar _t'19 tint)tbool).
Definition namespace_publication_guard:=match namespace_phase 29 with Ssequence _ guard=>guard|_=>Sskip end.
Definition namespace_publication_call_env le sequence:=
  PTree.set _sequence(Vlong(Int64.add sequence Int64.one))
    (PTree.set _t'18(Vlong sequence)(PTree.set _t'16(Vint Int.one)le)).
Definition namespace_publication_cont e le sequence k:=
  Kcall(Some _t'19)f_namespace_init e(namespace_publication_call_env le sequence)
    (Kseq namespace_publication_cast(Kseq namespace_publication_guard(Kseq(namespace_tail 30)k))).
Definition namespace_publication_return_env le sequence returned:=
  PTree.set _t'17(Vint(if Int.eq returned Int.zero then Int.zero else Int.one))
    (PTree.set _t'19(Vint returned)(namespace_publication_call_env le sequence)).
Definition namespace_checked_publication_env le sequence returned:=
  if Int.eq returned Int.zero then namespace_publication_return_env le sequence returned
  else PTree.set _bad(Vint Int.one)(namespace_publication_return_env le sequence returned).

Theorem namespace_normal_publication_call_source e le m k admission report sequence:
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  e!_send_frame=None ->e!_admission=Some(admission,result_type) ->
  le!_launch_check=Some(Vint Int.zero) ->
  exists count,store_path namespace_ge(fun current=>current=m)
    (State f_namespace_init(namespace_tail 29)k e le m)count
    (Callstate(Internal f_send_frame)[Vint report;Vlong sequence;Vptr admission Ptrofs.zero]
      (namespace_publication_cont e le sequence k)m).
Proof.
  intros BAD REPORT SEQUENCE SEND ADMISSION CHECK.
  unfold namespace_publication_cont,namespace_publication_call_env,namespace_publication_guard,
    namespace_publication_cast,namespace_phase,namespace_tail,child_tail;cbn[fn_body].
  eexists;child_route;child_route;child_route.
  eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - child_set.
    + apply old_expression_value;WriteAll.expression.
    + child_route.
      eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * child_route;child_route;child_route;child_set.
        -- apply old_expression_value,value_temp;WriteAll.lookup.
        -- child_route;child_set.
           ++ apply old_expression_value;WriteAll.expression.
           ++ child_route;eapply store_next;[reflexivity|namespace_call _send_frame|apply store_done;reflexivity].
              child_argument;child_argument.
              eapply cons_argument_values.
              ** eapply location_read_value;[apply local_location_value;exact ADMISSION|apply deref_loc_copy;reflexivity].
              ** reflexivity.
              ** apply no_argument_values.
Qed.

Theorem namespace_publication_return_source e le m k sequence returned:
  exists count,store_path namespace_ge(fun current=>current=m)
    (Returnstate(Vint returned)(namespace_publication_cont e le sequence k)m)count
    (State f_namespace_init(namespace_tail 30)k e(namespace_checked_publication_env le sequence returned)m).
Proof.
  unfold namespace_publication_cont,namespace_publication_cast,namespace_checked_publication_env,
    namespace_publication_return_env.
  destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;eexists;child_route;child_route;child_set.
    + apply old_expression_value;WriteAll.expression.
    + child_route;eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * child_route;apply store_done;reflexivity.
  - rewrite Int.eq_false by exact NONZERO;eexists;child_route;child_route;child_set.
    + apply old_expression_value;eapply value_cast;[apply value_temp;apply PTree.gss|].
      cbn;rewrite Int.eq_false by exact NONZERO;reflexivity.
    + child_route;eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * child_set;[apply old_expression_value,value_int|]. child_route;apply store_done;reflexivity.
Qed.

Theorem successful_publication_guard_requires_return_zero le sequence returned:
  (namespace_checked_publication_env le sequence returned)!_bad=Some(Vint Int.zero) ->
  returned=Int.zero /\le!_bad=Some(Vint Int.zero).
Proof.
  unfold namespace_checked_publication_env;destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;unfold namespace_publication_return_env,namespace_publication_call_env;
      intros BAD;split;[reflexivity|];repeat rewrite PTree.gso in BAD by discriminate;exact BAD.
  - rewrite Int.eq_false by exact NONZERO;rewrite PTree.gss;discriminate.
Qed.

Theorem failed_publication_latches_bad le sequence returned:
  returned<>Int.zero ->(namespace_checked_publication_env le sequence returned)!_bad=Some(Vint Int.one).
Proof. intro NONZERO;unfold namespace_checked_publication_env;rewrite Int.eq_false by exact NONZERO;apply PTree.gss. Qed.
