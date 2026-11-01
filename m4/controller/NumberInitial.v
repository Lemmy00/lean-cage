(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageController Require Import NumberSlice NumberStructure NumberMath NumberWords NumberMemory NumberValues NumberEntry NumberControl NumberStorage NumberIterations.
Import ListNotations.
Open Scope Z_scope.
Definition number_started_env block ofs output b :=
 PTree.set _p (Vptr block ofs)
 (PTree.set _result (Vlong Int64.zero)
 (PTree.set _t'8 (Vint(Int.sign_ext 8 (byte_word b)))
 (number_env (Vptr block ofs) output))).
Lemma number_start_path ge m block ofs b bytes output k P :
 number_input m block ofs (b::bytes) -> P m ->
 store_path ge P (number_initial (Vptr block ofs) output k m) 14
 (State f_number number_loop (number_loop_cont k) empty_env
 (number_started_env block ofs output b) m).
Proof.
 intros INPUT GOOD.
 destruct(number_read_head m block ofs (b::bytes) b (bytes++[Byte.zero]) INPUT eq_refl) as [_ SIGNED].
 pose proof(number_input_head m block ofs b bytes INPUT) as NONZERO.
 pose proof(number_signed_nonzero_test b NONZERO) as NZ.
 number_next;[apply number_entry|].
 rewrite number_body_structure;number_route;number_unfold number_prefix;number_route.
 number_set;[exact SIGNED|]. number_route.
 number_branch false.
 - cbn [bool_val classify_bool typeof]. unfold byte_word in NZ;rewrite NZ;reflexivity.
 - number_route;number_unfold number_suffix.
   number_route;number_set;number_route;number_route;number_route;number_set;number_route.
   apply store_done;exact GOOD.
Qed.
Lemma number_started_registers block ofs output b :
 (number_started_env block ofs output b)!_p=Some(Vptr block ofs) /\
 (number_started_env block ofs output b)!_result=Some(Vlong(Int64.repr 0)) /\
 (number_started_env block ofs output b)!_value=Some output.
Proof. unfold number_started_env,number_env;repeat split;WriteAll.lookup. Qed.
Lemma number_path_implication ge (P Q : mem -> Prop) start count last :
 (forall m, P m -> Q m) -> store_path ge P start count last -> store_path ge Q start count last.
Proof. intros IMPL RUN;induction RUN;[constructor;auto|econstructor;eauto]. Qed.
