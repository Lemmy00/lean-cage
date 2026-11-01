(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Exact selected statements and ordered native guard descriptors. *)
From Stdlib Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib Maps Integers AST Values Ctypes Ctypesdefs Cop Clight.
From LeanCageMain Require Import Main MainStructure.
Import ListNotations.
Open Scope Z_scope.
Inductive bound_kind := lower | upper | aligned.
Record policy_guard := {
 guard_field : ident; guard_index : Z; guard_kind : bound_kind; guard_bound : Z;
 guard_wide : bool; guard_input : ident; guard_output : ident; guard_read : ident
}.
Definition policy_guards : list policy_guard :=
 [
  Build_policy_guard _memory 0 lower 16777216 false _t'36 _t'37 _t'273;
  Build_policy_guard _memory 0 upper 1073741824 false _t'37 _t'38 _t'272;
  Build_policy_guard _memory 0 aligned 4096 false _t'38 _t'39 _t'271;
  Build_policy_guard _tasks 1 lower 4 false _t'39 _t'40 _t'270;
  Build_policy_guard _tasks 1 upper 256 false _t'40 _t'41 _t'269;
  Build_policy_guard _quota 2 lower 1000 false _t'41 _t'42 _t'268;
  Build_policy_guard _quota 2 upper 100000 false _t'42 _t'43 _t'267;
  Build_policy_guard _cpu 3 lower 10000 false _t'43 _t'44 _t'266;
  Build_policy_guard _cpu 3 upper 3600000000 true _t'44 _t'45 _t'265;
  Build_policy_guard _wall 4 lower 10 false _t'45 _t'46 _t'264;
  Build_policy_guard _wall 4 upper 3600000 false _t'46 _t'47 _t'263;
  Build_policy_guard _space 5 lower 1048576 false _t'47 _t'48 _t'262;
  Build_policy_guard _space 5 upper 268435456 false _t'48 _t'49 _t'261;
  Build_policy_guard _space 5 aligned 4096 false _t'49 _t'50 _t'260;
  Build_policy_guard _inodes 6 lower 64 false _t'50 _t'51 _t'259;
  Build_policy_guard _inodes 6 upper 65536 false _t'51 _t'52 _t'258;
  Build_policy_guard _in 7 upper 67108864 false _t'52 _t'53 _t'257;
  Build_policy_guard _out 8 upper 16777216 false _t'53 _t'54 _t'256;
  Build_policy_guard _err 9 upper 16777216 false _t'54 _t'55 _t'255].
Definition guard_constant g := if guard_wide g then Econst_long(Int64.repr(guard_bound g))tulong
 else Econst_int(Int.repr(guard_bound g))tint.
Definition guard_operator g := match guard_kind g with lower=>Olt|upper=>Ogt|aligned=>Omod end.
Definition guard_type g := match guard_kind g with aligned=>tulong|_=>tint end.
Definition guard_statement g :=
 Sifthenelse(Etempvar(guard_input g)tint)
 (Sset(guard_output g)(Econst_int Int.one tint))
 (Ssequence
  (Sset(guard_read g)(Efield(Evar _policy__1 policy_type)(guard_field g)tulong))
  (Sset(guard_output g)(Ecast(Ebinop(guard_operator g)(Etempvar(guard_read g)tulong)
   (guard_constant g)(guard_type g))tbool))).
Fixpoint guard_sequence start guards := match guards with
 | []=>start | g::rest=>guard_sequence(Ssequence start(guard_statement g))rest end.
Definition bounds_suffix := statement_at(false::repeat true 25)(fn_body f_main).
Definition bounds_region := first_statement bounds_suffix.
Definition after_bounds := second_statement bounds_suffix.
Definition bounds_conditions := first_statement bounds_region.
Definition bounds_finish := second_statement bounds_region.
Definition bounds_start := statement_at(repeat false 19)bounds_conditions.
Definition bounds_failure := match bounds_finish with Sifthenelse _ fail _=>fail|_=>Sskip end.
Definition bounds_report := first_statement(first_statement bounds_failure).
Definition bounds_report_suffix := second_statement(first_statement bounds_failure).
Definition bounds_failure_return := second_statement bounds_failure.
Theorem bounds_exact_structure :
 bounds_suffix=Ssequence bounds_region after_bounds /\
 bounds_region=Ssequence(guard_sequence bounds_start policy_guards)bounds_finish /\
 bounds_finish=Sifthenelse(Etempvar _t'55 tint)bounds_failure Sskip /\
 bounds_failure=Ssequence(Ssequence bounds_report bounds_report_suffix)bounds_failure_return.
Proof. repeat split;reflexivity. Qed.
Theorem bounds_start_structure : bounds_start =
 Sifthenelse(Ebinop Ogt(Ebinop Osub(Etempvar _argc tint)(Econst_int(Int.repr 16)tint)tint)
  (Econst_int(Int.repr 64)tint)tint)
 (Sset _t'36(Econst_int Int.one tint))
 (Sset _t'36(Ecast(Ebinop Ogt(Etempvar _bytes tulong)(Econst_int(Int.repr 16384)tint)tint)tbool)).
Proof. reflexivity. Qed.
Definition guard_bad g x := match guard_kind g with
 | lower=>x<?guard_bound g | upper=>guard_bound g<?x
 | aligned=>negb(x mod guard_bound g =? 0) end.
Definition policy_rejected values := existsb(fun g=>guard_bad g(nth(Z.to_nat(guard_index g))values 0))policy_guards.
Definition bounds_rejected argc bytes values :=
 (64<?argc-16)||(16384<?bytes)||policy_rejected values.
Definition guard_valid g := In(guard_index g,guard_field g)policy_fields /\
 0<guard_bound g /\ guard_bound g<=if guard_wide g then 18446744073709551615 else 2147483647.
Theorem policy_guards_valid : Forall guard_valid policy_guards.
Proof. unfold policy_guards;repeat (apply Forall_cons;[unfold guard_valid;cbn;intuition (try discriminate;lia)|]);constructor. Qed.
Theorem policy_guard_count : length policy_guards=19%nat.
Proof. reflexivity. Qed.
