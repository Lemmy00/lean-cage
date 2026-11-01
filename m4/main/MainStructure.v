(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Actual complete-helper layout, bindings and selected statements. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Errors Globalenvs Ctypes Ctypesdefs Cop Clight.
From LeanCageMain Require Import Main.
Import ListNotations.
Open Scope Z_scope.
Definition main_ge := Clight.globalenv Main.prog.
Definition policy_type := Tstruct _policy noattr.
Definition policy_members := match (genv_cenv main_ge) ! _policy with Some co => co_members co | None => [] end.
Definition policy_fields : list (Z*ident) :=
 [(0,_memory);(1,_tasks);(2,_quota);(3,_cpu);(4,_wall);(5,_space);(6,_inodes);(7,_in);(8,_out);(9,_err)].
Theorem policy_layout :
 sizeof main_ge policy_type=96 /\ alignof main_ge policy_type=8 /\
 map (fun id=>field_offset main_ge id policy_members)
 [_memory;_tasks;_quota;_cpu;_wall;_space;_inodes;_in;_out;_err;_export_files;_args]=
 map (fun ofs=>OK(ofs,Full)) [0;8;16;24;32;40;48;56;64;72;80;88].
Proof. repeat split;reflexivity. Qed.
Definition main_number_block := match Genv.find_symbol main_ge _number with Some b=>b|None=>1%positive end.
Definition main_policy_block := match Genv.find_symbol main_ge _policy__1 with Some b=>b|None=>1%positive end.
Theorem main_number_binding : Genv.find_symbol main_ge _number=Some main_number_block /\
 Genv.find_funct main_ge (Vptr main_number_block Ptrofs.zero)=Some(Internal f_number).
Proof. split;reflexivity. Qed.
Theorem main_policy_binding : Genv.find_symbol main_ge _policy__1=Some main_policy_block.
Proof. reflexivity. Qed.
Definition first_statement s := match s with Ssequence a _=>a|_=>Sskip end.
Definition second_statement s := match s with Ssequence _ b=>b|_=>Sskip end.
Fixpoint statement_at path s := match path with
 | []=>s | false::rest=>statement_at rest (first_statement s)
 | true::rest=>statement_at rest (second_statement s) end.
Definition numeric_region := statement_at [false;true;true;true;true] (fn_body f_main).
Definition numeric_tail := statement_at (repeat true 10) numeric_region.
Definition after_numeric := second_statement numeric_tail.
Definition numeric_loop := second_statement(first_statement numeric_tail).
Definition numeric_body := match numeric_loop with Sloop body _=>body|_=>Sskip end.
Definition numeric_increment := match numeric_loop with Sloop _ inc=>inc|_=>Sskip end.
Definition numeric_test := first_statement numeric_body.
Definition numeric_read := first_statement(second_statement numeric_body).
Definition numeric_check := second_statement(second_statement numeric_body).
Definition numeric_failure := match numeric_check with Sifthenelse _ fail _=>fail|_=>Sskip end.
Definition numeric_report := first_statement(first_statement numeric_failure).
Definition numeric_report_suffix := second_statement(first_statement numeric_failure).
Definition numeric_failure_return := second_statement numeric_failure.
Definition field_initializer (pair : Z*ident) :=
 Sassign (Ederef (Ebinop Oadd (Evar _fields (tarray (tptr tulong) 10))
  (Econst_int(Int.repr(fst pair)) tint) (tptr(tptr tulong))) (tptr tulong))
 (Eaddrof (Efield (Evar _policy__1 policy_type) (snd pair) tulong) (tptr tulong)).
Definition field_sequence fields tail := fold_right (fun pair rest=>Ssequence(field_initializer pair)rest) tail fields.
Theorem numeric_region_structure : numeric_region =
 field_sequence policy_fields (Ssequence (Ssequence (Sset _i (Econst_int Int.zero tint)) numeric_loop) after_numeric).
Proof. reflexivity. Qed.
Theorem numeric_loop_structure : numeric_loop=Sloop numeric_body numeric_increment /\
 numeric_body=Ssequence numeric_test(Ssequence numeric_read numeric_check) /\
 numeric_check=Sifthenelse(Etempvar _t'9 tint)numeric_failure Sskip /\
 numeric_failure=Ssequence(Ssequence numeric_report numeric_report_suffix)numeric_failure_return.
Proof. repeat split;reflexivity. Qed.
Ltac main_unfold s := let body := eval cbv [numeric_test numeric_read numeric_check
 numeric_failure numeric_report numeric_report_suffix numeric_failure_return numeric_loop
 numeric_body numeric_increment numeric_tail numeric_region first_statement second_statement
 statement_at repeat f_main] in s in change s with body.
