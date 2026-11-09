(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The actual initial guest prefix preserves the descriptor table. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps ClightSteps Library WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffInitial NativeHandoffMemory NativeHandoffTracePaths.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.
Ltac handoff_trace_route := eapply handoff_trace_spec_edge;[apply unchanged_store_edge;WriteAll.structural|].

Theorem handoff_trace_initial cell input before input_fd output_fd errors_fd failure k R wanted :
  handoff_borrowed_input cell before input -> handoff_borrowed_mode_bytes input=handoff_normal_bytes ->
  100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 ->
  (forall b after final,handoff_private_layout cell input b ->
    handoff_live_data cell input b(handoff_original_words input_fd output_fd errors_fd failure)after ->
    final!EntrySource._failure=Some(Vint failure) ->
    handoff_trace_spec handoff_ge cell R wanted
      (State EntrySource.f_guest(guest_tail 6(fn_body EntrySource.f_guest))k(handoff_locals_env b)final after)) ->
  handoff_trace_spec handoff_ge cell R wanted
    (Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before).
Proof.
  intros INPUT MODE UIDBOUND NEXT.
  destruct(handoff_entry_allocates before input_fd output_fd errors_fd failure k)
    as[b[allocated[ENTRY[ALLOC OWN]]]].
  destruct(handoff_layout_allocated cell input before b allocated INPUT ALLOC)as[LAYOUT LOCALOWN].
  pose proof(handoff_borrowed_allocated cell input before b allocated INPUT ALLOC)as BORROWED.
  set(original:=handoff_parameter_env input_fd output_fd errors_fd failure).
  destruct(handoff_parameter_bindings input_fd output_fd errors_fd failure)as[INPUTPARAM[OUTPUTPARAM[ERRORSPARAM FAILUREPARAM]]].
  assert(NORMAL:c_string allocated handoff_normal_address handoff_normal_bytes).
  { pose proof(handoff_borrowed_literals _ _ _ BORROWED)as LITERALS;inversion LITERALS;subst;exact H1. }
  assert(MODETEXT:c_string allocated(handoff_borrowed_mode input)handoff_normal_bytes).
  { rewrite <- MODE;exact(handoff_borrowed_mode_text _ _ _ BORROWED). }
  set(returned:=handoff_mode_returned original(address_block(handoff_borrowed_mode input))
    (Ptrofs.repr(address_offset(handoff_borrowed_mode input)))Int.zero).
  assert(RI:returned!EntrySource._input=Some(Vint input_fd)).
  { unfold returned,handoff_mode_returned,handoff_mode_loaded;rewrite !PTree.gso by discriminate;exact INPUTPARAM. }
  assert(RO:returned!EntrySource._output=Some(Vint output_fd)).
  { unfold returned,handoff_mode_returned,handoff_mode_loaded;rewrite !PTree.gso by discriminate;exact OUTPUTPARAM. }
  assert(RE:returned!EntrySource._errors=Some(Vint errors_fd)).
  { unfold returned,handoff_mode_returned,handoff_mode_loaded;rewrite !PTree.gso by discriminate;exact ERRORSPARAM. }
  assert(RF:returned!EntrySource._failure=Some(Vint failure)).
  { unfold returned,handoff_mode_returned,handoff_mode_loaded;rewrite !PTree.gso by discriminate;exact FAILUREPARAM. }
  destruct(handoff_handle_stores_exist b allocated input_fd output_fd errors_fd failure
    (handoff_local_object b allocated(handoff_handles b)16 LOCALOWN ltac:(unfold handoff_objects;cbn;auto)))
    as[after STORES].
  assert(AFTER:handoff_live_data cell input b(handoff_original_words input_fd output_fd errors_fd failure)after)
    by(eapply handoff_live_initialized;[exact LAYOUT|exact BORROWED|exact LOCALOWN|exact STORES]).
  set(final:=handoff_uid_env returned(handoff_borrowed_uid input)).
  assert(BAD:handoff_uid_bad(handoff_borrowed_uid input)=false)by(apply handoff_uid_checked;exact UIDBOUND).
  pose proof(handoff_uid_guard_source b returned after(handoff_borrowed_uid input)
    (Kseq(guest_tail 6(fn_body EntrySource.f_guest))k)
    (handoff_borrowed_uid_load _ _ _ (handoff_live_borrowed _ _ _ _ _ AFTER)))as GUARDED.
  rewrite BAD in GUARDED.
  eapply handoff_trace_spec_edge;[exact ENTRY|].
  eapply handoff_trace_spec_source.
  - apply handoff_mode_source;exact(handoff_borrowed_mode_load _ _ _ BORROWED).
  - apply handoff_trace_spec_strcmp with(left:=handoff_borrowed_mode input)(right:=handoff_normal_address)(bytes:=handoff_normal_bytes);
      [exact MODETEXT|exact NORMAL|].
    eapply handoff_trace_spec_source;[apply handoff_mode_return_source with(value:=Int.zero)|].
    handoff_trace_route;eapply handoff_trace_spec_source.
    + apply handoff_handle_initialization_source with(input:=input_fd)(output:=output_fd)(errors:=errors_fd)(failure:=failure);
        [exact RI|exact RO|exact RE|exact RF|exact STORES].
    + handoff_trace_route;eapply handoff_trace_spec_source;[exact GUARDED|]. handoff_trace_route.
      apply NEXT with(b:=b);[exact LAYOUT|exact AFTER|].
      unfold final,returned;rewrite handoff_initial_temps_preserved by(cbn;intuition discriminate);exact FAILUREPARAM.
Qed.
