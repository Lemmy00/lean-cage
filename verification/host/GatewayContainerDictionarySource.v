(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Dictionary frontiers select the actual key/duplicate/child/insertion statements. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayValueEntry GatewayContainerLoopSource GatewayContainerArraySource.
Import ListNotations.

Definition gateway_dictionary_branch := match gateway_container_tag_guard with
  Sifthenelse _ _ branch => branch | _ => Sskip end.
Definition gateway_dictionary_key_group := match gateway_dictionary_branch with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_after_key := match gateway_dictionary_branch with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_key_call := match gateway_dictionary_key_group with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_bind_key := match gateway_dictionary_key_group with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_contains_group := match gateway_dictionary_after_key with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_after_contains := match gateway_dictionary_after_key with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_contains_select := match gateway_dictionary_contains_group with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_bind_duplicate := match gateway_dictionary_contains_group with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_contains_yes := match gateway_dictionary_contains_select with Sifthenelse _ branch _ => branch | _ => Sskip end.
Definition gateway_dictionary_contains_call := match gateway_dictionary_contains_yes with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_contains_cast := match gateway_dictionary_contains_yes with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_key_check := match gateway_dictionary_after_contains with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_after_check := match gateway_dictionary_after_contains with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_child_group := match gateway_dictionary_after_check with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_after_child := match gateway_dictionary_after_check with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_child_call := match gateway_dictionary_child_group with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_bind_child := match gateway_dictionary_child_group with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_child_guard := match gateway_dictionary_after_child with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_after_child_guard := match gateway_dictionary_after_child with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_insert_group := match gateway_dictionary_after_child_guard with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_after_insert := match gateway_dictionary_after_child_guard with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_insert_call := match gateway_dictionary_insert_group with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_bind_result := match gateway_dictionary_insert_group with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_release_key := match gateway_dictionary_after_insert with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_after_release_key := match gateway_dictionary_after_insert with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_release_child := match gateway_dictionary_after_release_key with Ssequence first _ => first | _ => Sskip end.
Definition gateway_dictionary_insert_guard := match gateway_dictionary_after_release_key with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_dictionary_iteration_cont :=
  Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont.
Definition gateway_dictionary_key_cont slots parameters :=
  Kcall (Some _t'34) f_host_value (gateway_value_environment slots) parameters
    (Kseq gateway_dictionary_bind_key (Kseq gateway_dictionary_after_key gateway_dictionary_iteration_cont)).
Definition gateway_dictionary_contains_cont slots parameters :=
  Kcall (Some _t'36) f_host_value (gateway_value_environment slots) parameters
    (Kseq gateway_dictionary_contains_cast (Kseq gateway_dictionary_bind_duplicate
      (Kseq gateway_dictionary_after_contains gateway_dictionary_iteration_cont))).
Definition gateway_dictionary_second_cont slots parameters :=
  Kcall (Some _t'39) f_host_value (gateway_value_environment slots) parameters
    (Kseq gateway_dictionary_bind_child (Kseq gateway_dictionary_after_child gateway_dictionary_iteration_cont)).
Definition gateway_dictionary_insert_cont slots parameters :=
  Kcall (Some _t'40) f_host_value (gateway_value_environment slots) parameters
    (Kseq gateway_dictionary_bind_result (Kseq gateway_dictionary_after_insert gateway_dictionary_iteration_cont)).
Definition gateway_dictionary_release_key_cont slots parameters :=
  Kcall None f_host_value (gateway_value_environment slots) parameters
    (Kseq gateway_dictionary_after_release_key gateway_dictionary_iteration_cont).
Definition gateway_dictionary_release_child_cont slots parameters :=
  Kcall None f_host_value (gateway_value_environment slots) parameters
    (Kseq gateway_dictionary_insert_guard gateway_dictionary_iteration_cont).

Theorem actual_dictionary_source_shape :
  gateway_dictionary_bind_key = Sset _string_key (Etempvar _t'34 tint) /\
  gateway_dictionary_contains_cast = Sset _t'35 (Ecast (Etempvar _t'36 tint) tint) /\
  gateway_dictionary_bind_duplicate = Sset _duplicate (Etempvar _t'35 tint) /\
  gateway_dictionary_bind_child = Sset _value__1 (Etempvar _t'39 (tptr (Tstruct __object noattr))) /\
  gateway_dictionary_bind_result = Sset _result__1 (Etempvar _t'40 tint).
Proof. repeat split; reflexivity. Qed.
