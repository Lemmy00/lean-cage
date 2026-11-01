(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageController Require Import NumberSlice NumberStructure NumberMath NumberWords NumberMemory NumberValues NumberEntry NumberControl.
Open Scope Z_scope.
Definition number_code (parsed : option Z) := Vint (match parsed with Some _ => Int.zero | None => Int.mone end).
Definition number_post before output ofs (parsed : option Z) after :=
 match parsed with
 | None => after=before
 | Some value => Mem.storev Mint64 before (Vptr output ofs) (Vlong(Int64.repr value))=Some after
 end.
Definition number_memory before output ofs parsed after := after=before \/ number_post before output ofs parsed after.
Lemma number_memory_initial before output ofs parsed : number_memory before output ofs parsed before.
Proof. left;reflexivity. Qed.
Lemma number_finish_path ge m out ofs acc le k P after :
 le ! _value=Some(Vptr out ofs) -> le ! _result=Some(Vlong(Int64.repr acc)) ->
 Mem.storev Mint64 m (Vptr out ofs) (Vlong(Int64.repr acc))=Some after -> P m -> P after ->
 store_path ge P (State f_number number_finish k empty_env le m) 4
 (Returnstate (Vint Int.zero) (call_cont k) after).
Proof.
 intros OUT ACC STORE BEFORE AFTER;number_unfold number_finish.
 number_route.
 number_next;[eapply assignment_source_edge;
 [apply pointer_location_value;apply old_expression_value;WriteAll.expression
 |apply old_expression_value;WriteAll.expression
 |reflexivity
 |eapply assign_loc_value;[reflexivity|exact STORE]]|].
 number_route.
 number_next;[apply unchanged_store_edge;eapply edge_return;[WriteAll.expression|reflexivity]|].
 apply store_done;exact AFTER.
Qed.
