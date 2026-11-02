(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Ctypes Ctypesdefs Cop Clight.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import ValidationStructure.
Import ListNotations.
Open Scope Z_scope.
Definition parent_parse := Ssequence(argv_read _t'291 12)
 (Scall(Some _t'11)(Evar _number(Tfunction[tptr tschar;tptr tulong]tint cc_default))
 [Etempvar _t'291(tptr tschar);Eaddrof(Evar _parent tulong)(tptr tulong)]).
Definition parent_zero := Sifthenelse(Etempvar _t'11 tint)(Sset _t'12(Econst_int Int.one tint))
 (Ssequence(Sset _t'290(Evar _parent tulong))
 (Sset _t'12(Ecast(Eunop Onotbool(Etempvar _t'290 tulong)tint)tbool))).
Definition parent_upper := Sifthenelse(Etempvar _t'12 tint)(Sset _t'13(Econst_int Int.one tint))
 (Ssequence(Sset _t'289(Evar _parent tulong))
 (Sset _t'13(Ecast(Ebinop Ogt(Etempvar _t'289 tulong)(Econst_int(Int.repr 2147483647)tint)tint)tbool))).
Definition parent_compare := Ssequence(Sset _t'288(Evar _parent tulong))
 (Sset _t'14(Ecast(Ebinop One(Etempvar _t'15 tint)(Ecast(Etempvar _t'288 tulong)tint)tint)tbool)).
Definition parent_call := Scall(Some _t'15)(Evar _getppid(Tfunction [] tint cc_default))[].
Definition parent_observe := Sifthenelse(Etempvar _t'13 tint)(Sset _t'14(Econst_int Int.one tint))
 (Ssequence parent_call parent_compare).
Definition parent_conditions := Ssequence(Ssequence(Ssequence parent_parse parent_zero)parent_upper)parent_observe.
Theorem parent_source_structure : selection_check 15=Ssequence parent_conditions(selection_finish 15) /\
 selection_shape 15 _t'14 /\selection_report 15=setup_error_report __res__14 10.
Proof. repeat split;reflexivity. Qed.
Definition parent_guard_bad parsed := match parsed with
 |None=>true|Some value=>(value=?0)||(2147483647<?value)end.
Definition parent_parse_cont k := Kseq parent_zero(Kseq parent_upper(Kseq parent_observe(Kseq(selection_finish 15)(Kseq(selection_after 15)k)))).
Definition parent_observation_cont k := Kseq parent_compare(Kseq(selection_finish 15)(Kseq(selection_after 15)k)).
