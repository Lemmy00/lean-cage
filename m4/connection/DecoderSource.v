(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Source entry and complete result construction of decode_frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess CallPaths
  Library Readers ScalarMemory ResultLayout ResultSource FrameBytes DecoderLayout.
Import ListNotations.
Open Scope Z_scope.

Definition decoder_env := result_env.
Definition decoder_temps p sequence output ofs :=
  PTree.set _r (Vptr output (Ptrofs.repr ofs))
    (PTree.set _sequence (Vlong sequence)
      (PTree.set _p (address_value p) (create_undef_temps (fn_temps f_decode_frame)))).
Definition decoder_initial p sequence output ofs k m :=
  Callstate (Internal f_decode_frame) [address_value p;Vlong sequence;Vptr output (Ptrofs.repr ofs)] k m.
Definition decoder_header := match fn_body f_decode_frame with Ssequence s _ => s | _ => Sskip end.
Definition decoder_tail := match fn_body f_decode_frame with Ssequence _ s => s | _ => Sskip end.
Definition decoder_tail_reserved := match decoder_tail with Ssequence s _ => s | _ => Sskip end.
Definition decoder_payload := match decoder_tail with Ssequence _ s => s | _ => Sskip end.
Definition decoder_construction := match decoder_payload with Ssequence s _ => s | _ => Sskip end.
Definition decoder_postchecks := match decoder_payload with Ssequence _ s => s | _ => Sskip end.

Theorem decoder_source_parts : fn_body f_decode_frame =
  Ssequence decoder_header (Ssequence decoder_tail_reserved
    (Ssequence decoder_construction decoder_postchecks)).
Proof. reflexivity. Qed.

Lemma decoder_source_entry : forall m allocated local p sequence output ofs k,
  Mem.alloc m 0 144 = (allocated,local) ->
  store_edge result_ge (decoder_initial p sequence output ofs k m)
    (State f_decode_frame (fn_body f_decode_frame) k (decoder_env local)
      (decoder_temps p sequence output ofs) allocated).
Proof.
  intros. apply function_entry_source_edge. constructor.
  - repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); apply list_norepet_nil.
  - unfold list_disjoint, var_names; cbn. intros a b A B.
    destruct A as [A|[A|[A|A]]];
      repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction; subst; discriminate.
  - econstructor; [exact H|constructor].
  - reflexivity.
Qed.

Theorem decoder_reader_symbols : exists b32 b64,
  Genv.find_symbol result_ge _get32 = Some b32 /\
  Genv.find_funct result_ge (Vptr b32 Ptrofs.zero) = Some (Internal f_get32) /\
  Genv.find_symbol result_ge _get64 = Some b64 /\
  Genv.find_funct result_ge (Vptr b64 Ptrofs.zero) = Some (Internal f_get64).
Proof. eexists; eexists; split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. Qed.

Ltac decoder_location := first
  [eapply local_location_value; unfold decoder_env, result_env; WriteAll.lookup
  | eapply pointer_location_value; decoder_expression
  | eapply struct_location_value; [decoder_expression|reflexivity|reflexivity|reflexivity]]
with decoder_expression := first
  [solve [apply old_expression_value; WriteAll.expression]
  | eapply location_read_value;
      [decoder_location|
       first [apply deref_loc_reference; reflexivity|apply deref_loc_copy; reflexivity]]
  | eapply binary_expression_value; [decoder_expression|decoder_expression|reflexivity]
  | eapply cast_expression_value; [decoder_expression|reflexivity]].
Ltac decoder_arguments := first
  [apply no_argument_values
  | eapply cons_argument_values; [decoder_expression|reflexivity|decoder_arguments]].
Ltac decoder_route := eapply store_next; [assumption|apply unchanged_store_edge; WriteAll.structural|].
Ltac decoder_call symbol function := eapply store_next; [assumption| |];
  [eapply certified_call_edge; [reflexivity|
    apply old_expression_value; eapply value_function;
      [unfold decoder_env, result_env; cbn; reflexivity|exact symbol|reflexivity]|
    decoder_arguments|exact function|reflexivity]|].
Ltac decoder_scalar :=
  lazymatch goal with
  | STORES : scalar_stores ?local ?m (?cell :: ?rest) ?last,
    GOOD : ?P ?m,
    STABLE : forall chunk ofs value before after,
      ?P before -> Mem.store chunk before ?local ofs value = Some after -> ?P after |- _ =>
    inversion STORES; subst; clear STORES;
    lazymatch goal with STORE : Mem.store _ m local _ _ = Some ?nextmem |- _ =>
      let PRESERVED := fresh "PRESERVED" in
      pose proof (STABLE _ _ _ _ _ GOOD STORE) as PRESERVED;
      eapply store_next; [exact GOOD| |];
      [eapply assignment_source_edge with (after := nextmem);
        [decoder_location|decoder_expression|reflexivity|
         eapply assign_loc_value; [reflexivity|exact STORE]]|]
    end
  end.

Ltac decoder_reader cell p bytes READ LEN offset count INPUT symbol function :=
  repeat decoder_route; decoder_call symbol function;
  match goal with |- context [Ptrofs.mul ?a ?b] =>
    change (Ptrofs.mul a b) with (Ptrofs.repr (Z.of_nat offset)) end;
  rewrite pointer_add_representations;
  eapply store_path_trans with (n := count);
  [eapply (reader_caller_path result_ge cell);
    [apply (INPUT _ p bytes offset); [apply READ; assumption|rewrite LEN; lia]|assumption]|];
  repeat decoder_route; decoder_scalar.

Lemma decoder_construction_source_path : forall (cell : tls) (P : mem -> Prop)
    allocated local built copied output ofs p bytes k le,
  le ! _p = Some (address_value p) -> le ! _r = Some (Vptr output (Ptrofs.repr ofs)) ->
  length bytes = 160%nat ->
  scalar_stores local allocated (decoded_cells bytes) built ->
  assign_loc result_ge result_type built output (Ptrofs.repr ofs) Full (Vptr local Ptrofs.zero) copied ->
  P allocated -> P copied ->
  (forall m, P m -> readable_bytes m p bytes) ->
  (forall chunk offset value before after,
     P before -> Mem.store chunk before local offset value = Some after -> P after) ->
  exists count le', store_path result_ge P
    (State f_decode_frame decoder_construction k (decoder_env local) le allocated) count
    (State f_decode_frame Sskip k (decoder_env local) le' copied) /\
    le' ! _p = Some (address_value p) /\ le' ! _r = Some (Vptr output (Ptrofs.repr ofs)).
Proof.
  intros cell P allocated local built copied output ofs p bytes k le PTR OUT LEN STORES COPY PA PC READ STABLE.
  destruct decoder_reader_symbols as [b32 [b64 [S32 [F32 [S64 F64]]]]].
  eexists; eexists; split.
  { unfold decoder_construction, decoder_payload, decoder_tail; cbn [fn_body].
  cbn [decoded_cells app map seq] in STORES.
  repeat decoder_route.
  eapply store_next; [assumption|eapply certified_set_edge with (v := Vint (byte_word_at bytes 6))|].
  - apply old_expression_value. eapply value_load; [WriteAll.expression|reflexivity|].
    change (Mem.loadv Mint8unsigned allocated (Vptr (address_block p)
      (Ptrofs.add (Ptrofs.repr (address_offset p)) (Ptrofs.repr 6))) =
      Some (Vint (byte_word_at bytes 6))).
    rewrite pointer_add_representations.
    exact (readable_byte_load allocated p bytes 6 (READ allocated PA) ltac:(rewrite LEN; lia)).
  - repeat decoder_route. decoder_scalar.
    decoder_reader cell p bytes READ LEN 32%nat 59%nat frame_reader32_input S32 F32.
    decoder_reader cell p bytes READ LEN 36%nat 59%nat frame_reader32_input S32 F32.
    decoder_reader cell p bytes READ LEN 40%nat 59%nat frame_reader32_input S32 F32.
    decoder_reader cell p bytes READ LEN 44%nat 59%nat frame_reader32_input S32 F32.
    decoder_reader cell p bytes READ LEN 48%nat 59%nat frame_reader32_input S32 F32.
    decoder_reader cell p bytes READ LEN 52%nat 59%nat frame_reader32_input S32 F32.
    decoder_reader cell p bytes READ LEN 8%nat 103%nat frame_reader64_input S64 F64.
    decoder_reader cell p bytes READ LEN 56%nat 103%nat frame_reader64_input S64 F64.
    decoder_reader cell p bytes READ LEN 64%nat 103%nat frame_reader64_input S64 F64.
    decoder_reader cell p bytes READ LEN 72%nat 103%nat frame_reader64_input S64 F64.
    decoder_reader cell p bytes READ LEN 80%nat 103%nat frame_reader64_input S64 F64.
    decoder_reader cell p bytes READ LEN 88%nat 103%nat frame_reader64_input S64 F64.
    do 37 (repeat decoder_route; decoder_scalar).
    repeat decoder_route.
    match goal with S : scalar_stores _ _ [] _ |- _ => inversion S; subst; clear S end.
    eapply store_next; [assumption| |].
    + eapply assignment_source_edge; [decoder_location|decoder_expression|reflexivity|exact COPY].
    + apply store_done; exact PC. }
  split; WriteAll.lookup.
Qed.
