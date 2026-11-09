(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.values: Read the actual terminated argv and environment at the source image. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
Require Import Library.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffAllocation
  NativeHandoffInput NativeHandoffMemory NativeHandoffPrefix NativeHandoffInitial NativeHandoffLoop
  NativeHandoffSuffix NativeHandoffTables NativeHandoffGuest NativeHandoffStructure NativeHandoffExec.
From LeanCageMainNumber Require Import NumberMemory NumberMath.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Definition handoff_value_string m value bytes :=
  exists pointer,value=address_value pointer /\c_string m pointer bytes.

(* The NULL slot and every preceding load are part of this runtime interface.
   It contains bytes, with no inferred UTF-8/string interpretation. *)
Definition handoff_argv_bytes m output strings :=
  exists values,handoff_pointer_table m output(values++[Vlong Int64.zero]) /\
    Forall2(handoff_value_string m)values strings.

Definition handoff_worker_mode_bytes preflight :=
  if Int.eq preflight Int.zero then map Byte.repr[114;117;110]
  else map Byte.repr[99;104;101;99;107].

Lemma handoff_number_value_string m b offset bytes :
  number_input m b offset bytes -> (length bytes<32)%nat ->
  handoff_value_string m(Vptr b offset)bytes.
Proof.
  intros[BOUNDS[NONZERO LOAD]]LENGTH.
  exists{|address_block:=b;address_offset:=Ptrofs.unsigned offset|};split.
  - unfold address_value;cbn;rewrite Ptrofs.repr_unsigned;reflexivity.
  - split;[exact NONZERO|]. split;[|exact LOAD]. unfold span_bounds;cbn.
    split;[apply Ptrofs.unsigned_range|]. split;[exact BOUNDS|].
    rewrite length_app;cbn[length];change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Lemma handoff_owned_literal cell input m id bytes :
  handoff_borrowed_input cell m input -> In(id,bytes)handoff_literal_bytes ->
  handoff_value_string m(Vptr(handoff_symbol id)Ptrofs.zero)bytes.
Proof.
  intros INPUT MEMBER;exists(handoff_global_address id);split;[reflexivity|].
  pose proof(handoff_borrowed_literals _ _ _ INPUT)as LITERALS.
  rewrite Forall_forall in LITERALS;exact(LITERALS _ MEMBER).
Qed.

Lemma handoff_borrowed_strings cell input m :
  handoff_borrowed_input cell m input ->
  Forall2(handoff_value_string m)(map handoff_argument_value(handoff_borrowed_arguments input))
    (handoff_borrowed_argument_bytes input).
Proof.
  intros INPUT;pose proof(handoff_borrowed_argument_texts _ _ _ INPUT)as TEXTS.
  induction TEXTS;cbn;constructor;[|exact IHTEXTS].
  exists(handoff_pointer_address x);split;[|exact H].
  unfold handoff_argument_value,handoff_pointer_address,address_value;cbn;rewrite Ptrofs.repr_unsigned;reflexivity.
Qed.

Theorem handoff_snapshot_wire cell input input_fd output_fd errors_fd failure state :
  handoff_image_snapshot cell input input_fd output_fd errors_fd failure state ->
  exists b after caller suffix uidbytes inputbytes outputbytes errorsbytes failurebytes,
    state=Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))suffix))after /\
    caller!EntrySource._failure=Some(Vint failure) /\
    handoff_argv_bytes after(handoff_arguments b)
      (map Byte.repr[47;108;101;97;110;99;97;103;101;45;101;110;116;114;121]::
       handoff_worker_mode_bytes(handoff_borrowed_preflight input)::uidbytes::
       handoff_borrowed_root_bytes input::inputbytes::outputbytes::errorsbytes::failurebytes::
       handoff_normal_bytes::handoff_borrowed_argument_bytes input) /\
    handoff_argv_bytes after(handoff_environment b)[map Byte.repr[76;67;95;65;76;76;61;67]] /\
    decimal_number uidbytes=Some(Int.unsigned(handoff_borrowed_uid input)) /\
    decimal_number inputbytes=Some(Int.signed input_fd) /\
    decimal_number outputbytes=Some(Int.signed output_fd) /\
    decimal_number errorsbytes=Some(Int.signed errors_fd) /\
    decimal_number failurebytes=Some(Int.signed failure).
Proof.
  intros[b[after[caller[uidbytes[fdtexts[suffix[STATE[FAILURE[LIVE[MODE[UIDBOUND
    [UIDTEXT[UIDLENGTH[UIDPARSED[HISTORY[FDLENGTH[CHECKED[ARGSTABLE ENVTABLE]]]]]]]]]]]]]]]]]].
  destruct fdtexts as[|inputbytes[|outputbytes[|errorsbytes[|failurebytes[|extra rest]]]]];
    cbn[length]in FDLENGTH;try discriminate.
  cbn[handoff_fd_history]in HISTORY.
  destruct HISTORY as[IT[IL[IP[OT[OL[OP[ET[EL[EP[FT[FL[FP DONE]]]]]]]]]]]].
  pose proof(handoff_live_borrowed _ _ _ _ _ LIVE)as BORROWED.
  exists b,after,caller,suffix,uidbytes,inputbytes,outputbytes,errorsbytes,failurebytes.
  split;[exact STATE|]. split;[exact FAILURE|]. split.
  - exists(handoff_prefix_values b(handoff_borrowed_preflight input)
      (address_block(handoff_borrowed_mode input))(Ptrofs.repr(address_offset(handoff_borrowed_mode input)))++
      map handoff_argument_value(handoff_borrowed_arguments input)).
    split;[exact ARGSTABLE|].
    apply Forall2_app with(l1':=[map Byte.repr[47;108;101;97;110;99;97;103;101;45;101;110;116;114;121];
      handoff_worker_mode_bytes(handoff_borrowed_preflight input);uidbytes;handoff_borrowed_root_bytes input;
      inputbytes;outputbytes;errorsbytes;failurebytes;handoff_normal_bytes])
      (l2':=handoff_borrowed_argument_bytes input);[|eapply handoff_borrowed_strings;exact BORROWED].
    unfold handoff_prefix_values.
    apply Forall2_cons;[eapply handoff_owned_literal;[exact BORROWED|unfold handoff_literal_bytes;cbn;auto 8]|].
    apply Forall2_cons.
    { unfold handoff_worker_mode,handoff_worker_mode_bytes;destruct(Int.eq _ _);
        (eapply handoff_owned_literal;[exact BORROWED|unfold handoff_literal_bytes;cbn;auto 8]). }
    apply Forall2_cons;[eapply handoff_number_value_string;[exact UIDTEXT|lia]|].
    apply Forall2_cons.
    { exists(handoff_global_address EntrySource._root_path);split;[reflexivity|].
      exact(handoff_borrowed_root_text _ _ _ BORROWED). }
    apply Forall2_cons;[eapply handoff_number_value_string;[exact IT|lia]|].
    apply Forall2_cons;[eapply handoff_number_value_string;[exact OT|lia]|].
    apply Forall2_cons;[eapply handoff_number_value_string;[exact ET|lia]|].
    apply Forall2_cons;[eapply handoff_number_value_string;[exact FT|lia]|].
    apply Forall2_cons.
    { exists(handoff_borrowed_mode input);split;[reflexivity|].
      rewrite <- MODE;exact(handoff_borrowed_mode_text _ _ _ BORROWED). }
    apply Forall2_nil.
  - split.
    + exists[Vptr(handoff_symbol EntrySource.___stringlit_114)Ptrofs.zero];split;[exact ENVTABLE|].
      constructor;[|constructor]. eapply handoff_owned_literal;[exact BORROWED|unfold handoff_literal_bytes;cbn;auto 8].
    + repeat split;assumption.
Qed.
