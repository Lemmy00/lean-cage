(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Other actual receive errors cannot produce successful bytes. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayControlPaths GatewayCalls
  GatewayOperations GatewayTransferSource GatewayTransferErrno GatewayTransferProgress GatewayTransferFailure
  GatewayTransferRetry.
Import ListNotations.
Open Scope Z_scope.

Definition transfer_nonretry_errno_values temporaries:=PTree.set _t'10(Vint Int.zero)temporaries.
Definition transfer_nonretry_values temporaries:=PTree.set _t'9(Vint Int.zero)(transfer_nonretry_errno_values temporaries).
Definition transfer_nonretry_count_values temporaries:=PTree.set _t'11(Vint Int.one)(transfer_nonretry_values temporaries).
Definition transfer_errno_else:=match transfer_errno_second with Sifthenelse _ _ other=>other|_=>Sskip end.
Definition transfer_errno_else_first:=match transfer_errno_else with Ssequence first _=>first|_=>Sskip end.
Definition transfer_errno_else_second:=match transfer_errno_else with Ssequence _ second=>second|_=>Sskip end.

Lemma actual_other_errno_false ge environment temporaries memory number literal :
  temporaries!_number=Some(Vint number) ->number<>literal ->
  expression_value ge environment temporaries memory
    (Ebinop Oeq(Etempvar _number tint)(Econst_int literal tint)tint)(Vint Int.zero).
Proof.
  intros LOOK DIFFERENT;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact LOOK.
  - constructor.
  - change(Some(Val.of_bool(Int.eq number literal))=Some(Vint Int.zero)).
    rewrite Int.eq_false by exact DIFFERENT;reflexivity.
Qed.

Local Ltac error_prefix target:=
  eapply gateway_prefix_next with(next:=target);[cbn;tauto|intro another|].

Lemma actual_nonretry_errno_prefix ge temporaries number memory :
  temporaries!_number=Some(Vint number) ->number<>Int.repr 4 ->number<>Int.repr 11 ->
  gateway_retained_prefix ge
    (State f_host_transfer transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)empty_env
      (transfer_nonretry_values temporaries)memory)
    (State f_host_transfer transfer_errno_first
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env temporaries memory).
Proof.
  intros NUMBER FOUR ELEVEN.
  error_prefix(State f_host_transfer
    (Sset _t'10(Ecast(Ebinop Oeq(Etempvar _number tint)(Econst_int(Int.repr 11)tint)tint)tbool))
    (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
    empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply actual_other_errno_false with(number:=number);assumption|reflexivity]. }
  error_prefix(State f_host_transfer Sskip
    (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
    empty_env(transfer_nonretry_errno_values temporaries)memory).
  { apply certified_set_edge;apply cast_expression_value with(v:=Vint Int.zero);
      [apply actual_other_errno_false with(number:=number);assumption|reflexivity]. }
  error_prefix(State f_host_transfer transfer_errno_second
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
    (transfer_nonretry_errno_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  error_prefix(State f_host_transfer transfer_errno_else
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
    (transfer_nonretry_errno_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  error_prefix(State f_host_transfer transfer_errno_else_first
    (Kseq transfer_errno_else_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
    empty_env(transfer_nonretry_errno_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  error_prefix(State f_host_transfer Sskip
    (Kseq transfer_errno_else_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
    empty_env(transfer_nonretry_values temporaries)memory).
  { apply certified_set_edge;apply cast_expression_value with(v:=Vint Int.zero);[|reflexivity].
    apply actual_other_errno_false with(number:=number);[|exact ELEVEN].
    unfold transfer_nonretry_errno_values;rewrite PTree.gso by discriminate;exact NUMBER. }
  error_prefix(State f_host_transfer transfer_errno_else_second
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
    (transfer_nonretry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  error_prefix(State f_host_transfer Sskip
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
    (transfer_nonretry_values temporaries)memory).
  { replace(transfer_nonretry_values temporaries)with
      (PTree.set _t'9(Vint Int.zero)(transfer_nonretry_values temporaries))at 2
      by(unfold transfer_nonretry_values;rewrite PTree.set2;reflexivity).
    apply certified_set_edge;apply cast_expression_value with(v:=Vint Int.zero);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  error_prefix(State f_host_transfer transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env(transfer_nonretry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)empty_env
      (transfer_nonretry_values temporaries)memory)
    (gateway_replace_memory(State f_host_transfer transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)empty_env
      (transfer_nonretry_values temporaries)memory)memory));constructor.
Qed.

Lemma actual_negative_count_error_tail ge temporaries memory :
  temporaries!_count=Some(Vlong(Int64.repr(-1))) ->
  gateway_retained_prefix ge
    (State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)empty_env
      (transfer_nonretry_count_values temporaries)memory)
    (State f_host_transfer transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)empty_env
      (transfer_nonretry_values temporaries)memory).
Proof.
  intro COUNT.
  error_prefix(State f_host_transfer Sskip(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env(transfer_nonretry_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  error_prefix(State f_host_transfer transfer_after_retry transfer_iteration_cont
    empty_env(transfer_nonretry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  error_prefix(State f_host_transfer transfer_count_sequence(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_nonretry_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  error_prefix(State f_host_transfer transfer_count_choice
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))empty_env
    (transfer_nonretry_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  error_prefix(State f_host_transfer(Sset _t'11(Econst_int Int.one tint))
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))empty_env
    (transfer_nonretry_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true).
    - apply old_expression_value;eapply value_binary.
      + apply value_temp;unfold transfer_nonretry_values,transfer_nonretry_errno_values;
          rewrite !PTree.gso by discriminate;exact COUNT.
      + constructor.
      + reflexivity.
    - reflexivity. }
  error_prefix(State f_host_transfer Sskip
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))empty_env
    (transfer_nonretry_count_values temporaries)memory).
  { apply certified_set_edge;apply old_expression_value;constructor. }
  error_prefix(State f_host_transfer transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_nonretry_count_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  error_prefix(State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_nonretry_count_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)empty_env
      (transfer_nonretry_count_values temporaries)memory)
    (gateway_replace_memory(State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)
      empty_env(transfer_nonretry_count_values temporaries)memory)memory));constructor.
Qed.

Theorem actual_negative_nonretry_error_prefix ge temporaries number memory :
  temporaries!_count=Some(Vlong(Int64.repr(-1))) ->temporaries!_number=Some(Vint number) ->
  number<>Int.repr 4 ->number<>Int.repr 11 ->
  gateway_retained_prefix ge
    (State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)empty_env
      (transfer_nonretry_count_values temporaries)memory)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries memory).
Proof.
  intros COUNT NUMBER FOUR ELEVEN.
  error_prefix(State f_host_transfer transfer_retry_sequence(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  error_prefix(State f_host_transfer transfer_retry_prefix
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  error_prefix(State f_host_transfer transfer_errno_sequence
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply actual_negative_count_comparison;exact COUNT|reflexivity]. }
  error_prefix(State f_host_transfer transfer_errno_first
    (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
    empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  eapply gateway_retained_prefix_transitive.
  - exact(actual_nonretry_errno_prefix ge temporaries number memory NUMBER FOUR ELEVEN).
  - exact(actual_negative_count_error_tail ge temporaries memory COUNT).
Qed.

Theorem actual_negative_nonretry_returns_failure {World Event}(backend:gateway_backend World Event)ge
    temporaries number before world events returned after next :
  temporaries!_count=Some(Vlong(Int64.repr(-1))) ->temporaries!_number=Some(Vint number) ->
  number<>Int.repr 4 ->number<>Int.repr 11 ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->returned=Vint(Int.neg Int.one).
Proof.
  intros COUNT NUMBER FOUR ELEVEN RUN.
  destruct(gateway_prefix_side_cut backend ge(fun _ _=>True)
    ltac:(unfold gateway_runtime_discipline;intros;exact I)
    (State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)empty_env
      (transfer_nonretry_count_values temporaries)before)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries before)
    (actual_negative_nonretry_error_prefix ge temporaries number before COUNT NUMBER FOUR ELEVEN)
    before world events returned after next I RUN)
    as[prefix[suffix[memory[current[EVENTS[QUIET[PREFIX[READY REST]]]]]]]].
  cbn[GatewayMachine.gateway_replace_memory]in REST.
  eapply gateway_error_sequence_returns_failure with(function:=f_host_transfer)
    (continuation:=Kseq transfer_advance_sequence transfer_iteration_cont);[reflexivity|reflexivity|exact REST].
Qed.
