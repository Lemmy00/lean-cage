(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Actual decoder entry and initial comparison call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine
  ResultLayout ResultSource DecoderSource SequencePaths.
Import ListNotations.
Open Scope Z_scope.

Definition decoder_compare_cont local le := Kcall (Some _t'1) f_decode_frame (decoder_env local) le
  (sequence_continuation decoder_header (Kseq decoder_tail Kstop)).
Definition decoder_compare_state p magic local le m :=
  Callstate memcmp_definition (comparison_args p {|address_block:=magic;address_offset:=0|} 4)
    (decoder_compare_cont local le) m.

Theorem decoder_comparison_symbols : exists cb magic,
  Genv.find_symbol result_ge _memcmp = Some cb /\
  Genv.find_funct result_ge (Vptr cb Ptrofs.zero) = Some memcmp_definition /\
  Genv.find_symbol result_ge ___stringlit_2 = Some magic.
Proof. eexists; eexists; split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. Qed.

Theorem decoder_to_compare : forall (P : mem -> Prop) m allocated local p sequence output ofs magic,
  Mem.alloc m 0 144 = (allocated,local) -> P m -> P allocated ->
  Genv.find_symbol result_ge ___stringlit_2 = Some magic ->
  exists count, store_path result_ge P (decoder_initial p sequence output ofs Kstop m) count
    (decoder_compare_state p magic local (decoder_temps p sequence output ofs) allocated).
Proof.
  intros P m allocated local p sequence output ofs magic ALLOC PM PA MS.
  destruct decoder_comparison_symbols as [cb [lit [CS [CF LS]]]].
  assert (lit=magic) by congruence; subst lit.
  eexists. eapply store_next; [exact PM|apply decoder_source_entry; exact ALLOC|].
  rewrite decoder_source_parts. decoder_route.
  eapply store_path_trans; [apply source_sequence_path; exact PA|].
  change (sequence_statement decoder_header) with (Scall (Some _t'1)
    (Evar _memcmp (Tfunction [tptr tvoid;tptr tvoid;tulong] tint cc_default))
    [Etempvar _p (tptr tuchar);Evar ___stringlit_2 (tarray tschar 5);Econst_int (Int.repr 4) tint]).
  unfold decoder_compare_state, decoder_compare_cont, decoder_temps, comparison_args, address_value.
  eapply store_next; [exact PA| |].
  - eapply certified_call_edge; [reflexivity| | |exact CF|reflexivity].
    + apply old_expression_value; eapply value_function;
        [unfold decoder_env, result_env; cbn; reflexivity|exact CS|reflexivity].
    + eapply cons_argument_values; [decoder_expression|reflexivity|].
      eapply cons_argument_values.
      * apply old_expression_value; eapply value_function;
          [unfold decoder_env, result_env; cbn; reflexivity|exact MS|reflexivity].
      * reflexivity.
      * eapply cons_argument_values; [decoder_expression|reflexivity|apply no_argument_values].
  - apply store_done; exact PA.
Qed.
