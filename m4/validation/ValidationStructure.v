(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Bool.
From compcert Require Import Coqlib Maps Integers AST Values Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Library LibraryMachine.
From LeanCageMain Require Import Main MainStructure.
Import ListNotations.
Open Scope Z_scope.
Definition symbol_block id := match Genv.find_symbol main_ge id with Some b=>b|None=>1%positive end.
Definition literal_address id := {|address_block:=symbol_block id;address_offset:=0|}.
Definition none_bytes := map Byte.repr[110;111;110;101].
Definition discard_bytes := map Byte.repr[100;105;115;99;97;114;100].
Definition files_bytes := map Byte.repr[114;101;103;117;108;97;114;45;102;105;108;101;115].
Definition shell_bytes := map Byte.repr[47;98;105;110;47;115;104].
Definition python_bytes := map Byte.repr[47;117;115;114;47;108;111;99;97;108;47;98;105;110;47;112;121;116;104;111;110;51].
Definition plan_bytes := map Byte.repr[77;51;80;76;65;78;49].
Definition check_bytes := map Byte.repr[77;51;67;72;69;67;75;49].
Definition strcmp_type := Tfunction[tptr tschar;tptr tschar]tint cc_default.
Definition digest_type := Tfunction[tptr tschar]tint cc_default.
Lemma validation_function_bindings :
 Genv.find_symbol main_ge _strcmp=Some(symbol_block _strcmp) /\
 Genv.find_funct main_ge(Vptr(symbol_block _strcmp)Ptrofs.zero)=Some strcmp_definition /\
 Genv.find_symbol main_ge _digest_text=Some(symbol_block _digest_text) /\
 Genv.find_funct main_ge(Vptr(symbol_block _digest_text)Ptrofs.zero)=Some(Internal f_digest_text).
Proof. repeat split;reflexivity. Qed.
Definition comparison_call input output literal size :=
 Scall(Some output)(Evar _strcmp strcmp_type)
 [Etempvar input(tptr tschar);Evar literal(tarray tschar size)].
Definition argv_read output index := Sset output
 (Ederef(Ebinop Oadd(Etempvar _argv(tptr(tptr tschar)))(Econst_int(Int.repr index)tint)(tptr(tptr tschar)))(tptr tschar)).
Definition comparison_pair first second value1 value2 result :=
 Ssequence first(Sifthenelse(Etempvar value1 tint)
 (Ssequence second(Sset result(Ecast(Etempvar value2 tint)tbool)))
 (Sset result(Econst_int Int.zero tint))).
Definition validation_suffix index := statement_at(false::repeat true index)(fn_body f_main).
Definition export_check := first_statement(validation_suffix 16).
Definition export_conditions := first_statement export_check.
Definition export_finish := second_statement export_check.
Definition executable_check := first_statement(validation_suffix 22).
Definition executable_conditions := first_statement executable_check.
Definition executable_finish := second_statement executable_check.
Definition digest_check := first_statement(validation_suffix 20).
Definition digest_conditions := first_statement digest_check.
Definition digest_tree := first_statement digest_conditions.
Definition digest_stdin := second_statement digest_conditions.
Definition digest_finish := second_statement digest_check.
Definition digest_failure := match digest_finish with Sifthenelse _ fail _=>fail|_=>Sskip end.
Definition digest_report := first_statement(first_statement digest_failure).
Definition digest_report_rest := second_statement(first_statement digest_failure).
Definition digest_return := second_statement digest_failure.
Theorem export_conditions_identity : export_conditions=
 comparison_pair(Ssequence(argv_read _t'287 13)(comparison_call _t'287 _t'17 ___stringlit_133 8))
 (Ssequence(argv_read _t'286 13)(comparison_call _t'286 _t'19 ___stringlit_132 14)) _t'17 _t'19 _t'18.
Proof. reflexivity. Qed.
Theorem digest_check_identity :
 digest_check=Ssequence(Ssequence digest_tree digest_stdin)digest_finish /\
 digest_finish=Sifthenelse(Etempvar _t'25 tint)digest_failure Sskip /\
 digest_failure=Ssequence(Ssequence digest_report digest_report_rest)digest_return.
Proof. repeat split;reflexivity. Qed.
Ltac validation_unfold s := let body := eval cbv [export_check export_conditions export_finish
 executable_check executable_conditions executable_finish digest_check digest_conditions digest_tree digest_stdin
 digest_finish digest_failure digest_report digest_report_rest digest_return validation_suffix statement_at
 first_statement second_statement repeat f_main] in s in change s with body.
Definition selection_check index := first_statement(validation_suffix index).
Definition selection_finish index := second_statement(selection_check index).
Definition selection_failure index := match selection_finish index with Sifthenelse _ fail _=>fail|_=>Sskip end.
Definition selection_report index := first_statement(first_statement(selection_failure index)).
Definition selection_report_rest index := second_statement(first_statement(selection_failure index)).
Definition selection_return index := second_statement(selection_failure index).
Definition selection_after index := second_statement(validation_suffix index).
Definition selection_shape index result :=
 selection_finish index=Sifthenelse(Etempvar result tint)(selection_failure index)Sskip /\
 selection_failure index=Ssequence(Ssequence(selection_report index)(selection_report_rest index))(selection_return index).
Lemma export_selection_shape : selection_shape 16 _t'18.
Proof. split;reflexivity. Qed.
Lemma executable_selection_shape : selection_shape 22 _t'30.
Proof. split;reflexivity. Qed.
Lemma mode_selection_shape : selection_shape 2 _t'4.
Proof. split;reflexivity. Qed.
Definition setup_error_report local code :=
 Scall None(Evar _result_of(Tfunction[tptr(Tstruct _result noattr);tuint;tuint;tuint;tuint]
 tvoid {|cc_vararg:=None;cc_unproto:=false;cc_structret:=true|}))
 [Eaddrof(Evar local(Tstruct _result noattr))(tptr(Tstruct _result noattr));
 Econst_int(Int.repr 1)tint;Econst_int(Int.repr 1)tint;Econst_int(Int.repr code)tint;Econst_int(Int.repr 0)tint].
Lemma selection_reports_exact :
 selection_report 16=setup_error_report __res__13 22 /\
 selection_report 20=setup_error_report __res__12 22 /\
 selection_report 22=setup_error_report __res__11 22 /\
 selection_report 2=setup_error_report __res__16 22.
Proof. repeat split;reflexivity. Qed.
Definition mode_conditions := first_statement(selection_check 2).
Definition mode_pair := match mode_conditions with Sifthenelse _ _ no=>no|_=>Sskip end.
Theorem mode_condition_structure : mode_conditions=
 Sifthenelse(Ebinop Olt(Etempvar _argc tint)(Econst_int(Int.repr 17)tint)tint)
 (Sset _t'4(Econst_int Int.one tint))mode_pair.
Proof. reflexivity. Qed.
Ltac mode_unfold := let body := eval cbv [mode_pair mode_conditions selection_check validation_suffix statement_at
 first_statement second_statement repeat f_main]in mode_pair in change mode_pair with body.
Lemma digest_selection_shape : selection_shape 20 _t'25.
Proof. split;reflexivity. Qed.
