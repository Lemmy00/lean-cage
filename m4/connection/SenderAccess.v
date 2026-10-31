(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Actual sender field and local-array expression evaluation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Errors Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine
  ScalarMemory ResultLayout FrameRecord SenderSource.
Import ListNotations.
Open Scope Z_scope.
Ltac sender_location := first
  [eapply local_location_value;unfold sender_env;WriteAll.lookup
  |eapply pointer_location_value;sender_expression
  |eapply struct_location_value;[sender_expression|reflexivity|reflexivity|reflexivity]]
with sender_expression := first
  [apply old_expression_value;WriteAll.expression
  |eapply location_read_value;[sender_location|first
    [apply deref_loc_copy;reflexivity|apply deref_loc_reference;reflexivity]]
  |eapply binary_expression_value;[sender_expression|sender_expression|reflexivity]
  |eapply cast_expression_value;[sender_expression|reflexivity]].

Lemma sender_field_expression : forall m result_local bytes_local le r digest field ty chunk delta value,
  frame_result_owned m result_local 0 r digest ->
  field_offset result_ge field result_members=OK(delta,Full) -> access_mode ty=By_value chunk ->
  In {|scalar_chunk:=chunk;scalar_offset:=delta;scalar_value:=value|} (frame_result_cells r digest) ->
  expression_value result_ge (sender_env result_local bytes_local) le m
    (Efield (Evar _result__1 result_type) field ty) (Val.load_result chunk value).
Proof.
  intros m result_local bytes_local le r digest field ty chunk delta value OWN FIELD MODE CELL.
  pose proof (frame_result_cells_valid r digest) as VALID;rewrite Forall_forall in VALID.
  destruct (VALID _ CELL) as [LOW [HIGH ALIGN]];cbn in LOW,HIGH.
  eapply location_read_value.
  - eapply struct_location_value;[sender_expression|reflexivity|reflexivity|exact FIELD].
  - eapply deref_loc_value;[exact MODE|].
    rewrite Ptrofs.add_zero_l. unfold Mem.loadv.
    rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned;change Ptrofs.modulus with 18446744073709551616;pose proof (size_chunk_pos chunk);lia).
    rewrite zle_true by (change Ptrofs.modulus with 18446744073709551616;lia).
    destruct OWN as [_ [_ [_ [_ [_ [CONTENTS _]]]]]].
    exact (CONTENTS _ CELL).
Qed.

Theorem sender_encoding_symbols : exists b32 b64 bc,
  Genv.find_symbol result_ge _put32=Some b32 /\
  Genv.find_funct result_ge (Vptr b32 Ptrofs.zero)=Some (Internal f_put32) /\
  Genv.find_symbol result_ge _put64=Some b64 /\
  Genv.find_funct result_ge (Vptr b64 Ptrofs.zero)=Some (Internal f_put64) /\
  Genv.find_symbol result_ge _memcpy=Some bc /\
  Genv.find_funct result_ge (Vptr bc Ptrofs.zero)=Some memcpy_definition.
Proof. eexists;eexists;eexists. split;[vm_compute;reflexivity|]. split;[vm_compute;reflexivity|]. split;[vm_compute;reflexivity|]. split;[vm_compute;reflexivity|]. split;vm_compute;reflexivity. Qed.

Ltac sender_field r OWN :=
  lazymatch goal with |- expression_value _ _ _ _ (Efield _ ?field _) _ =>
    let cell := lazymatch field with
      | _kind=>constr:(cell32 0 (fr_kind r)) | _stage=>constr:(cell32 4 (fr_stage r))
      | _detail=>constr:(cell32 8 (fr_detail r)) | _entry=>constr:(cell32 12 (fr_entry r))
      | _clean=>constr:(cell32 16 (fr_clean r)) | _triggers=>constr:(cell32 20 (fr_triggers r))
      | _uid=>constr:(cell32 24 (fr_uid r)) | _run=>constr:(cell64 32 (fr_run r))
      | _cpu=>constr:(cell64 40 (fr_cpu r)) | _peak=>constr:(cell64 48 (fr_peak r))
      | _out=>constr:(cell64 56 (fr_out r)) | _err=>constr:(cell64 64 (fr_err r))
      | _elapsed=>constr:(cell64 72 (fr_elapsed r)) | _oom=>constr:(cell64 80 (fr_oom r))
      | _pids=>constr:(cell64 88 (fr_pids r)) | _export_state=>constr:(cell32 96 (fr_export_state r))
      | _omitted=>constr:(cell32 100 (fr_omitted r)) | _export_error=>constr:(cell32 104 (fr_export_error r)) end in
    eapply (sender_field_expression _ _ _ _ _ _ _ _ (scalar_chunk cell) (scalar_offset cell) (scalar_value cell));
      [exact OWN|reflexivity|reflexivity|cbn [frame_result_cells app In];tauto]
  end.

Ltac sender_arguments := first [apply no_argument_values|
  eapply cons_argument_values;[sender_expression|reflexivity|sender_arguments]].
