(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Actual source, owned argument strings and explicit loss. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Globalenvs Ctypes Ctypesdefs Cop Clight.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsStructure.
Import ListNotations.
Open Scope Z_scope.
Definition argument_suffix := statement_at(false::repeat true 23)(fn_body f_main).
Definition argument_bytes_init := first_statement argument_suffix.
Definition argument_tail := second_statement argument_suffix.
Definition argument_loop_region := first_statement argument_tail.
Definition after_arguments := second_statement argument_tail.
Definition argument_loop := second_statement argument_loop_region.
Definition argument_body := match argument_loop with Sloop b _=>b|_=>Sskip end.
Definition argument_increment := match argument_loop with Sloop _ inc=>inc|_=>Sskip end.
Definition argument_test := first_statement argument_body.
Definition argument_read := first_statement(second_statement argument_body).
Definition argument_check := first_statement(second_statement(second_statement argument_body)).
Definition argument_add := second_statement(second_statement(second_statement argument_body)).
Definition argument_size_check := first_statement argument_check.
Definition argument_reject := second_statement argument_check.
Definition argument_failure := match argument_reject with Sifthenelse _ fail _=>fail|_=>Sskip end.
Definition argument_report := first_statement(first_statement argument_failure).
Definition argument_finish := second_statement(first_statement argument_failure).
Definition argument_return := second_statement argument_failure.
Theorem argument_structure :
 argument_suffix=Ssequence argument_bytes_init(Ssequence argument_loop_region after_arguments) /\
 argument_bytes_init=Sset _bytes(Ecast(Econst_int(Int.repr 0)tint)tulong) /\
 argument_loop_region=Ssequence(Sset _i__1(Econst_int(Int.repr 16)tint))argument_loop /\
 argument_loop=Sloop argument_body argument_increment /\
 argument_body=Ssequence argument_test(Ssequence argument_read(Ssequence argument_check argument_add)) /\
 argument_check=Ssequence argument_size_check argument_reject /\
 argument_reject=Sifthenelse(Etempvar _t'34 tint)argument_failure Sskip /\
 argument_failure=Ssequence(Ssequence argument_report argument_finish)argument_return /\
 after_arguments=bounds_suffix.
Proof. repeat split;reflexivity. Qed.
Ltac argument_unfold s := let body := eval cbv [argument_suffix argument_bytes_init argument_tail
 argument_loop_region after_arguments argument_loop argument_body argument_increment argument_test
 argument_read argument_check argument_add argument_size_check argument_reject argument_failure
 argument_report argument_finish argument_return statement_at first_statement second_statement repeat f_main] in s in change s with body.
Theorem argument_size_structure : argument_size_check=
 Sifthenelse(Eunop Onotbool(Etempvar _n tulong)tint)
 (Sset _t'34(Econst_int(Int.repr 1)tint))
 (Sset _t'34(Ecast(Ebinop Ogt(Etempvar _n tulong)(Econst_int(Int.repr 4096)tint)tint)tbool)).
Proof. reflexivity. Qed.
Theorem argument_report_structure : argument_report=
 Scall None(Evar _result_of(Tfunction[tptr(Tstruct _result noattr);tuint;tuint;tuint;tuint]
 tvoid {|cc_vararg:=None;cc_unproto:=false;cc_structret:=true|}))
 [Eaddrof(Evar __res__10(Tstruct _result noattr))(tptr(Tstruct _result noattr));
 Econst_int(Int.repr 1)tint;Econst_int(Int.repr 1)tint;Econst_int(Int.repr 7)tint;Econst_int(Int.repr 0)tint].
Proof. reflexivity. Qed.
