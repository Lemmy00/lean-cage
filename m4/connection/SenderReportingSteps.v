(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Actual write calls and local returns used by reporting branches. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine
  ResultLayout SenderSource SenderAccess SenderReportMemory SenderReturn
  CallContexts WriteCallers ReportPaths SenderGuards.
Import ListNotations.
Open Scope Z_scope.
Lemma sizeof_expression_value : forall ge e le m ty result_type,
  expression_value ge e le m (Esizeof ty result_type) (Vptrofs (Ptrofs.repr (sizeof ge ty))).
Proof.
  intros;split;[constructor|]. intros other EV;inversion EV;subst;[reflexivity|].
  match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _=>inversion LV end.
Qed.
Theorem sender_write_call_edge : forall cell m result_local bytes_local fd le k opt count count_expr count_value,
  le ! _fd=Some (Vint fd) ->
  expression_value result_ge (sender_env result_local bytes_local) le m count_expr count_value ->
  sem_cast count_value (typeof count_expr) tulong m=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  store_edge result_ge
    (State f_send_frame (Scall opt (Evar _write_all (Tfunction [tint;tptr tvoid;tulong] tint cc_default))
      [Etempvar _fd tint;Evar _bytes (tarray tuchar 160);count_expr]) k (sender_env result_local bytes_local) le m)
    (write_call_initial (sender_request cell fd bytes_local count)
      (Kcall opt f_send_frame (sender_env result_local bytes_local) le k) m).
Proof.
  intros cell m result_local bytes_local fd le k opt count count_expr count_value FD COUNT CAST.
  destruct sender_report_symbols as [fb [wb [FS [FF [WS WF]]]]].
  unfold write_call_initial,WriteAll.initial_state,plug_state,sender_request;cbn [descriptor buffer_block buffer_offset requested].
  eapply certified_call_edge;[reflexivity| | |exact WF|reflexivity].
  - apply old_expression_value;eapply value_function;[unfold sender_env;cbn;reflexivity|exact WS|reflexivity].
  - eapply cons_argument_values;[sender_expression|reflexivity|].
    eapply cons_argument_values;[sender_expression|reflexivity|].
    eapply cons_argument_values;[exact COUNT|exact CAST|apply no_argument_values].
Qed.

Theorem sender_return_certificate : forall allow_errors cell base m result_local bytes_local r digest bytes le a k v w R,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_live_memory cell base result_local bytes_local r digest bytes m -> call_cont k=Kstop ->
  expression_value result_ge (sender_env result_local bytes_local) le m a v ->
  sem_cast v (typeof a) tint m=Some w ->
  (forall after,sender_freed base result_local bytes_local after -> R [] w after) ->
  report_returns_allow allow_errors cell (sender_preserved cell base) R
    (State f_send_frame (Sreturn (Some a)) k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell base m result_local bytes_local r digest bytes le a k v w R FR FB NE
    [OLD [OWN [READ [RFREE BFREE]]]] STOP VALUE CAST POST.
  destruct (sender_free_exists cell base m result_local bytes_local FR FB NE OLD RFREE BFREE)
    as [after [FREE [PRESERVED FREED]]].
  eapply report_returns_source;[exact OLD|eapply sender_source_return;[exact VALUE|exact CAST|exact FREE]|].
  rewrite STOP;apply report_returns_done;[exact PRESERVED|apply POST;exact FREED].
Qed.
