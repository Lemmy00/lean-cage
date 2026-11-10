(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Integer construction paths are projections of the maintained
   number helper, including all intermediate reference releases and loop continuations. *)
From Stdlib Require Import List.
From compcert Require Import AST Integers Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayJsonNumberSource GatewayNumberConstruction GatewayNumber.
Import ListNotations.

Definition number_integer_guard_group:=json_number_first gateway_number_after_base.
Definition number_integer_short_guard:=json_number_first number_integer_guard_group.
Definition number_integer_failure_guard:=json_number_rest number_integer_guard_group.
Definition number_integer_after_guard:=json_number_rest gateway_number_after_base.
Definition number_integer_index_set:=json_number_first number_integer_after_guard.
Definition number_integer_after_index:=json_number_rest number_integer_after_guard.
Definition number_integer_width_set:=json_number_first number_integer_after_index.
Definition number_integer_after_width:=json_number_rest number_integer_after_index.
Definition number_integer_width_guard:=json_number_first number_integer_after_width.
Definition number_integer_after_width_guard:=json_number_rest number_integer_after_width.
Definition number_integer_loop:=json_number_first number_integer_after_width_guard.
Definition number_integer_after_loop:=json_number_rest number_integer_after_width_guard.
Definition number_integer_loop_body:=match number_integer_loop with Sloop body _=>body|_=>Sskip end.
Definition number_integer_work:=json_number_rest number_integer_loop_body.
Definition number_integer_chunk_zero:=json_number_first number_integer_work.
Definition number_integer_after_chunk_zero:=json_number_rest number_integer_work.
Definition number_integer_chunk_group:=json_number_first number_integer_after_chunk_zero.
Definition number_integer_after_chunk:=json_number_rest number_integer_after_chunk_zero.
Definition number_integer_part_group:=json_number_first number_integer_after_chunk.
Definition number_integer_part_assign:=json_number_rest number_integer_part_group.
Definition number_integer_after_part:=json_number_rest number_integer_after_chunk.
Definition number_integer_part_guard:=json_number_first number_integer_after_part.
Definition number_integer_after_part_guard:=json_number_rest number_integer_after_part.
Definition number_integer_multiply_group:=json_number_first number_integer_after_part_guard.
Definition number_integer_multiply_assign:=json_number_rest number_integer_multiply_group.
Definition number_integer_after_multiply:=json_number_rest number_integer_after_part_guard.
Definition number_integer_release_value:=json_number_first number_integer_after_multiply.
Definition number_integer_after_release_value:=json_number_rest number_integer_after_multiply.
Definition number_integer_scaled_guard:=json_number_first number_integer_after_release_value.
Definition number_integer_after_scaled_guard:=json_number_rest number_integer_after_release_value.
Definition number_integer_add_group:=json_number_first number_integer_after_scaled_guard.
Definition number_integer_add_assign:=json_number_rest number_integer_add_group.
Definition number_integer_after_add:=json_number_rest number_integer_after_scaled_guard.
Definition number_integer_release_scaled:=json_number_first number_integer_after_add.
Definition number_integer_after_release_scaled:=json_number_rest number_integer_after_add.
Definition number_integer_release_part:=json_number_first number_integer_after_release_scaled.
Definition number_integer_after_release_part:=json_number_rest number_integer_after_release_scaled.
Definition number_integer_value_guard:=json_number_first number_integer_after_release_part.
Definition number_integer_advance:=json_number_rest number_integer_after_release_part.
Definition number_integer_loop_cont:=Kseq number_integer_after_loop Kstop.
Definition number_integer_work_cont:=Kloop1 number_integer_loop_body Sskip number_integer_loop_cont.
Definition number_integer_chunk_cont:=Kseq number_integer_after_chunk number_integer_work_cont.
Definition number_integer_part_cont parameters:=Kcall(Some _t'18)f_host_json_number empty_env parameters
  (Kseq number_integer_part_assign(Kseq number_integer_after_part number_integer_work_cont)).
Definition number_integer_multiply_cont parameters:=Kcall(Some _t'19)f_host_json_number empty_env parameters
  (Kseq number_integer_multiply_assign(Kseq number_integer_after_multiply number_integer_work_cont)).
Definition number_integer_release_value_cont parameters:=Kcall None f_host_json_number empty_env parameters
  (Kseq number_integer_after_release_value number_integer_work_cont).
Definition number_integer_add_cont parameters:=Kcall(Some _t'20)f_host_json_number empty_env parameters
  (Kseq number_integer_add_assign(Kseq number_integer_after_add number_integer_work_cont)).
Definition number_integer_release_scaled_cont parameters:=Kcall None f_host_json_number empty_env parameters
  (Kseq number_integer_after_release_scaled number_integer_work_cont).
Definition number_integer_release_part_cont parameters:=Kcall None f_host_json_number empty_env parameters
  (Kseq number_integer_after_release_part number_integer_work_cont).

Theorem actual_number_integer_chunk_group:
  number_integer_chunk_group=Ssequence
    (Sset _offset(Ecast(Econst_int Int.zero Ctypesdefs.tint)Ctypesdefs.tulong))gateway_number_chunk_loop.
Proof. reflexivity. Qed.

Theorem actual_number_integer_release_operands:
  number_integer_release_value=Scall None
    (Evar _Py_DecRef(Tfunction[Ctypesdefs.tptr(Tstruct __object noattr)]Ctypesdefs.tvoid cc_default))
    [Etempvar _value__1(Ctypesdefs.tptr(Tstruct __object noattr))] /\
  number_integer_release_scaled=Scall None
    (Evar _Py_DecRef(Tfunction[Ctypesdefs.tptr(Tstruct __object noattr)]Ctypesdefs.tvoid cc_default))
    [Etempvar _scaled(Ctypesdefs.tptr(Tstruct __object noattr))] /\
  number_integer_release_part=Scall None
    (Evar _Py_DecRef(Tfunction[Ctypesdefs.tptr(Tstruct __object noattr)]Ctypesdefs.tvoid cc_default))
    [Etempvar _part(Ctypesdefs.tptr(Tstruct __object noattr))].
Proof. repeat split;reflexivity. Qed.
