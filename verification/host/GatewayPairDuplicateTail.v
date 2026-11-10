(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: A failed duplicate follows the actual cleanup branch; only its success reaches replacement. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPairStatements GatewayIntegerFailures
  GatewayFramedRuntime GatewaySetupPaths.
Import ListNotations.
Open Scope Z_scope.

Definition pair_duplicate_cont temporaries:=Kcall(Some _t'2)f_host_private_pair empty_env temporaries
  (Kseq pair_moved_set(Kseq pair_after_duplicate pair_loop_cont)).
Definition pair_duplicate_temps temporaries moved:=PTree.set _moved(Vint(Int.repr moved))
  (PTree.set _t'2(Vint(Int.repr moved))temporaries).

Lemma actual_pair_moved_guard(ge:Clight.genv)temporaries memory moved:
  temporaries!_moved=Some(Vint(Int.repr moved))->Int.min_signed<=moved<=Int.max_signed->
  expression_value ge empty_env temporaries memory
    (Ebinop Olt(Etempvar _moved tint)(Econst_int Int.zero tint)tint)
    (Vint(if zlt moved 0 then Int.one else Int.zero)).
Proof.
  intros MOVED BOUND;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact MOVED.
  - constructor.
  - change(Some(Val.of_bool(Int.lt(Int.repr moved)Int.zero))=
      Some(Vint(if zlt moved 0 then Int.one else Int.zero))).
    unfold Int.lt;rewrite Int.signed_repr by exact BOUND.
    change(Int.signed Int.zero)with 0;destruct(zlt moved 0);reflexivity.
Qed.

Theorem actual_pair_duplicate_tail_script {World Event}(backend:gateway_backend World Event)ge
    (property:mem->World->Prop)result temporaries memory moved:
  gateway_ambient_closed backend property->Int.min_signed<=moved<=Int.max_signed->
  (0<=moved->forall memory,gateway_setup_path backend ge result property
    (State f_host_private_pair pair_replacement pair_loop_cont empty_env(pair_duplicate_temps temporaries moved)memory))->
  gateway_setup_path backend ge result property
    (Returnstate(Vint(Int.repr moved))(pair_duplicate_cont temporaries)memory).
Proof.
  intros CLOSED BOUND REST.
  eapply gateway_setup_same with(next:=State f_host_private_pair Sskip
    (Kseq pair_moved_set(Kseq pair_after_duplicate pair_loop_cont))empty_env
    (PTree.set _t'2(Vint(Int.repr moved))temporaries)memory);[exact CLOSED|cbn;tauto| |].
  { intros available current GOOD;apply unchanged_store_edge,edge_returnstate. }
  eapply gateway_setup_same with(next:=State f_host_private_pair pair_moved_set
    (Kseq pair_after_duplicate pair_loop_cont)empty_env(PTree.set _t'2(Vint(Int.repr moved))temporaries)memory);
    [exact CLOSED|cbn;tauto| |].
  { intros available current GOOD;apply unchanged_store_edge,edge_skip_seq. }
  eapply gateway_setup_same with(next:=State f_host_private_pair Sskip(Kseq pair_after_duplicate pair_loop_cont)
    empty_env(pair_duplicate_temps temporaries moved)memory);[exact CLOSED|cbn;tauto| |].
  { intros available current GOOD;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss. }
  eapply gateway_setup_same with(next:=State f_host_private_pair pair_after_duplicate pair_loop_cont
    empty_env(pair_duplicate_temps temporaries moved)memory);[exact CLOSED|cbn;tauto| |].
  { intros available current GOOD;apply unchanged_store_edge,edge_skip_seq. }
  eapply gateway_setup_same with(next:=State f_host_private_pair pair_moved_guard(Kseq pair_replacement pair_loop_cont)
    empty_env(pair_duplicate_temps temporaries moved)memory);[exact CLOSED|cbn;tauto| |].
  { intros available current GOOD;apply unchanged_store_edge,edge_seq. }
  destruct(zlt moved 0)as[NEGATIVE|NONNEGATIVE].
  - eapply gateway_setup_same with(next:=State f_host_private_pair pair_failure(Kseq pair_replacement pair_loop_cont)
      empty_env(pair_duplicate_temps temporaries moved)memory);[exact CLOSED|cbn;tauto| |].
    { intros available current GOOD;apply certified_if_edge with(v:=Vint Int.one)(b:=true).
      - pose proof(actual_pair_moved_guard ge(pair_duplicate_temps temporaries moved)available moved
          ltac:(apply PTree.gss)BOUND)as VALUE;destruct(zlt moved 0);[exact VALUE|lia].
      - reflexivity. }
    apply gateway_setup_failure;left;split;[reflexivity|]. split;[reflexivity|]. left.
    cbn;tauto.
  - eapply gateway_setup_same with(next:=State f_host_private_pair Sskip(Kseq pair_replacement pair_loop_cont)
      empty_env(pair_duplicate_temps temporaries moved)memory);[exact CLOSED|cbn;tauto| |].
    { intros available current GOOD;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
      - pose proof(actual_pair_moved_guard ge(pair_duplicate_temps temporaries moved)available moved
          ltac:(apply PTree.gss)BOUND)as VALUE;destruct(zlt moved 0);[lia|exact VALUE].
      - reflexivity. }
    eapply gateway_setup_same with(next:=State f_host_private_pair pair_replacement pair_loop_cont
      empty_env(pair_duplicate_temps temporaries moved)memory);[exact CLOSED|cbn;tauto| |].
    { intros available current GOOD;apply unchanged_store_edge,edge_skip_seq. }
    apply REST;lia.
Qed.
