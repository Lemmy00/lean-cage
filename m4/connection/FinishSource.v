(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.finish: Actual finish entry, by-value copy, field reads, call and local return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Errors Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess ScalarMemory ResultLayout
  FreshMemory FrameRecord FrameCopy SenderSource.
Import ListNotations.
Open Scope Z_scope.
Definition finish_env local := PTree.set _result__1 (local,result_type) empty_env.
Definition finish_temps input ofs := PTree.set _result__1 (Vptr input (Ptrofs.repr ofs))
  (create_undef_temps (fn_temps f_finish)).
Definition finish_initial input ofs k m := Callstate (Internal f_finish) [Vptr input (Ptrofs.repr ofs)] k m.
Definition finish_copy := match fn_body f_finish with Ssequence s _=>s|_=>Sskip end.
Definition finish_after_copy := statement_drop 1 (fn_body f_finish).
Definition finish_after_send := statement_drop 1 finish_after_copy.
Definition finish_sender_cont local le k := Kcall None f_finish (finish_env local) le (Kseq finish_after_send k).
Definition finish_exit_word r :=
  if Int.eq (fr_kind r) (Int.repr 7) then Int.zero else
  if Int.eq (fr_kind r) Int.zero then fr_detail r else
  if Int.eq (fr_kind r) (Int.repr 2) then Int.add (Int.repr 128) (fr_detail r) else
  if Int.eq (fr_kind r) Int.one then Int.repr 125 else
  if Int.eq (fr_kind r) (Int.repr 3) then Int.repr 124 else Int.repr 126.
Ltac finish_location := first
  [eapply local_location_value;unfold finish_env;WriteAll.lookup
  |eapply pointer_location_value;finish_expression
  |eapply struct_location_value;[finish_expression|reflexivity|reflexivity|reflexivity]]
with finish_expression := first
  [apply old_expression_value;WriteAll.expression
  |eapply location_read_value;[finish_location|first
    [apply deref_loc_copy;reflexivity|apply deref_loc_reference;reflexivity]]
  |eapply binary_expression_value;[finish_expression|finish_expression|reflexivity]
  |eapply cast_expression_value;[finish_expression|reflexivity]].
Theorem finish_entry_source : forall base allocated local input ofs k,
  Mem.alloc base 0 144=(allocated,local) ->
  store_edge result_ge (finish_initial input ofs k base)
    (State f_finish (fn_body f_finish) k (finish_env local) (finish_temps input ofs) allocated).
Proof.
  intros;apply function_entry_source_edge;constructor.
  - repeat (apply list_norepet_cons;[simpl;intuition discriminate|]);apply list_norepet_nil.
  - repeat (apply list_norepet_cons;[simpl;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros a b A B;destruct A as [A|A];
      repeat match goal with H : _ \/ _ |- _=>destruct H end;try contradiction;subst;discriminate.
  - econstructor;[exact H|constructor].
  - reflexivity.
Qed.
Lemma finish_parameter_copy_source : forall allocated copied local input ofs k,
  assign_loc result_ge result_type allocated local Ptrofs.zero Full (Vptr input (Ptrofs.repr ofs)) copied ->
  store_edge result_ge
    (State f_finish finish_copy k (finish_env local) (finish_temps input ofs) allocated)
    (State f_finish Sskip k (finish_env local) (finish_temps input ofs) copied).
Proof.
  intros;eapply assignment_source_edge;[finish_location|unfold finish_temps;finish_expression|reflexivity|exact H].
Qed.
Lemma finish_field_source : forall m local le r digest field ty chunk delta value,
  frame_result_owned m local 0 r digest ->
  field_offset result_ge field result_members=OK(delta,Full) -> access_mode ty=By_value chunk ->
  In {|scalar_chunk:=chunk;scalar_offset:=delta;scalar_value:=value|} (frame_result_cells r digest) ->
  expression_value result_ge (finish_env local) le m
    (Efield (Evar _result__1 result_type) field ty) (Val.load_result chunk value).
Proof.
  intros m local le r digest field ty chunk delta value OWN FIELD MODE CELL.
  pose proof (frame_result_cells_valid r digest) as VALID;rewrite Forall_forall in VALID.
  destruct (VALID _ CELL) as [LOW [HIGH ALIGN]];cbn in LOW,HIGH.
  eapply location_read_value.
  - eapply struct_location_value;[finish_expression|reflexivity|reflexivity|exact FIELD].
  - eapply deref_loc_value;[exact MODE|]. rewrite Ptrofs.add_zero_l;unfold Mem.loadv.
    rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;pose proof (size_chunk_pos chunk);lia).
    rewrite zle_true by (change Ptrofs.modulus with 18446744073709551616;lia).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 OWN))))) _ CELL).
Qed.
Ltac finish_field r OWN :=
  lazymatch goal with |- expression_value _ _ _ _ (Efield _ ?field _) _ =>
    let cell:=lazymatch field with | _kind=>constr:(cell32 0 (fr_kind r))|_detail=>constr:(cell32 8 (fr_detail r)) end in
    eapply (finish_field_source _ _ _ _ _ _ _ (scalar_chunk cell) (scalar_offset cell) (scalar_value cell));
    [exact OWN|reflexivity|reflexivity|cbn [frame_result_cells app In];tauto]
  end.
Theorem finish_send_symbol : exists b,
  Genv.find_symbol result_ge _send_frame=Some b /\
  Genv.find_funct result_ge (Vptr b Ptrofs.zero)=Some (Internal f_send_frame).
Proof. eexists;split;vm_compute;reflexivity. Qed.
Lemma finish_send_source : forall local le k m,
  store_edge result_ge
    (State f_finish (match finish_after_copy with Ssequence s _=>s|_=>Sskip end) (Kseq finish_after_send k) (finish_env local) le m)
    (sender_initial Int.one Int64.zero local 0 (finish_sender_cont local le k) m).
Proof.
  intros;destruct finish_send_symbol as [b [SYM FUN]].
  eapply certified_call_edge;[reflexivity|apply old_expression_value;eapply value_function;
    [unfold finish_env;cbn;reflexivity|exact SYM|reflexivity]| |exact FUN|reflexivity].
  repeat (eapply cons_argument_values;[finish_expression|reflexivity|]);apply no_argument_values.
Qed.
Lemma finish_source_return : forall m after local le k expr value word,
  expression_value result_ge (finish_env local) le m expr value ->
  sem_cast value (typeof expr) tint m=Some (Vint word) -> Mem.free m local 0 144=Some after ->
  store_edge result_ge (State f_finish (Sreturn (Some expr)) k (finish_env local) le m)
    (Returnstate (Vint word) (call_cont k) after).
Proof.
  intros;eapply certified_local_return_edge;[exact H|exact H0|].
  change (match Mem.free m local 0 144 with Some after=>Some after|None=>None end=Some after).
  rewrite H1;reflexivity.
Qed.
