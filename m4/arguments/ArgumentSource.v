(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Complete selected block and all actual bounded prefixes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
Require Import Machine Deterministic Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath ArgumentStructure ArgumentWords
 ArgumentValues ArgumentControl ArgumentMemory ArgumentLoop ArgumentEntry.
Import ListNotations.
Open Scope Z_scope.
Definition argument_endpoint result e le k m := match result with
|arguments_accepted _=>State f_main after_arguments k e le m
|arguments_rejected _ _=>argument_failure_state e le(Kseq after_arguments k)m end.
Theorem argument_region_source cell m argv ofs argc inputs e le k :
 17<=argc<=2147483647 -> 16+Z.of_nat(length inputs)=argc -> guest_table_span ofs argc ->
 guest_arguments_owned m argv ofs 16 inputs -> e!_strlen=None ->
 le!_argv=Some(Vptr argv ofs) -> le!_argc=Some(Vint(Int.repr argc)) ->
 exists count final,(count<=26*length inputs+13)%nat /\
 argument_registers final argv ofs argc(outcome_index argc(argument_scan 16 0 inputs))
 (outcome_total(argument_scan 16 0 inputs)) /\
 string_path main_ge cell(State f_main argument_suffix k e le m)count
 (argument_endpoint(argument_scan 16 0 inputs)e final k m).
Proof.
 intros COUNT SIZE SPAN OWN GLOBAL ARGV ARGC.
 destruct(argument_loop_source cell m argv ofs argc 16 0 inputs e(argument_initial_env le)
 (Kseq after_arguments k)ltac:(lia)ltac:(lia)SIZE ltac:(lia)OWN GLOBAL
 (argument_initialize_registers _ _ _ _ ARGV ARGC))as[n[final[BOUND[REG PATH]]]].
 destruct(argument_scan 16 0 inputs)as[total|index total]eqn:RESULT.
 - exists(7+n+1)%nat,final;split;[lia|];split;[exact REG|].
   cbn[argument_endpoint];eapply string_path_trans with(n:=7%nat).
   + apply string_store_path with(m:=m);apply argument_initialize.
   + replace(n+1)%nat with(n+1)%nat by reflexivity.
     eapply string_path_trans;[exact PATH|apply string_store_path with(m:=m);apply argument_to_bounds].
 - exists(7+n)%nat,final;split;[lia|];split;[exact REG|].
   cbn[argument_endpoint];eapply string_path_trans with(n:=7%nat);
   [apply string_store_path with(m:=m);apply argument_initialize|exact PATH].
Qed.
Theorem argument_region_execution cell m argv ofs argc inputs e le k :
 17<=argc<=2147483647 -> 16+Z.of_nat(length inputs)=argc -> guest_table_span ofs argc ->
 guest_arguments_owned m argv ofs 16 inputs -> e!_strlen=None ->
 le!_argv=Some(Vptr argv ofs) -> le!_argc=Some(Vint(Int.repr argc)) ->
 exists count final,(count<=26*length inputs+13)%nat /\
 argument_registers final argv ofs argc(outcome_index argc(argument_scan 16 0 inputs))
 (outcome_total(argument_scan 16 0 inputs)) /\
 (exists events,string_cost events=count /\ string_steps main_ge cell
  (live(State f_main argument_suffix k e le m))events(live(argument_endpoint(argument_scan 16 0 inputs)e final k m))) /\
 (forall events target,string_steps main_ge cell(live(State f_main argument_suffix k e le m))events target ->
  (string_cost events<=count)%nat -> routine_memory target=m) /\
 (forall events state,string_steps main_ge cell(live(State f_main argument_suffix k e le m))events(live state) ->
  (string_cost events<count)%nat -> exists event next,string_waiting event=false /\ event<>string_loss /\
   string_step main_ge cell(live state)event(live next)) /\
 (forall events state,string_steps main_ge cell(live(State f_main argument_suffix k e le m))events(live state) ->
  string_cost events=count -> state=argument_endpoint(argument_scan 16 0 inputs)e final k m) /\
 (forall n,(n<=count)%nat -> exists events,string_cost events=n /\
  string_steps main_ge cell(live(State f_main argument_suffix k e le m))(events++[string_loss])(dead m)).
Proof.
 intros COUNT SIZE SPAN OWN GLOBAL ARGV ARGC.
 destruct(argument_region_source cell m argv ofs argc inputs e le k COUNT SIZE SPAN OWN GLOBAL ARGV ARGC)
 as[n[final[BOUND[REG PATH]]]]. exists n,final;split;[exact BOUND|];split;[exact REG|].
 split;[eapply string_path_actual;exact PATH|].
 split;[intros events target RUN N;exact(string_path_prefix_memory _ _ _ _ _ _ _ PATH RUN N)|].
 split;[intros events state RUN N;exact(string_path_prefix_progress _ _ _ _ _ _ _ PATH RUN N)|].
 split;[intros events state RUN N;exact(string_path_prefix_endpoint _ _ _ _ _ _ _ PATH RUN N)|].
 intros prefix N;exact(string_path_loss_every_prefix _ _ _ _ _ PATH prefix N).
Qed.
Theorem argument_initial_wait_loss cell m argv ofs argc x rest e le k waits :
 17<=argc<=2147483647 ->
 guest_arguments_owned m argv ofs 16(x::rest) -> e!_strlen=None ->
 le!_argv=Some(Vptr argv ofs) -> le!_argc=Some(Vint(Int.repr argc)) ->
 exists prefix,string_cost prefix=17%nat /\
 string_steps main_ge cell(live(State f_main argument_suffix k e le m))
 (prefix++repeat string_wait waits++[string_loss])(dead m).
Proof.
 intros COUNT[STRING[LOAD REST]]GLOBAL ARGV ARGC.
 assert(PREFIX:string_path main_ge cell(State f_main argument_suffix k e le m)17
 (Callstate strlen_definition[address_value(guest_pointer x)]
 (argument_call_cont e(argument_loaded(argument_initial_env le)(guest_pointer x))(Kseq after_arguments k))m)).
 { eapply string_path_trans with(n:=7%nat).
   - apply string_store_path with(m:=m);apply argument_initialize.
   - apply string_store_path with(m:=m);eapply argument_to_call with(argv:=argv)(ofs:=ofs)(argc:=argc)(i:=16)(total:=0);
     [exact GLOBAL|apply argument_initialize_registers;assumption|lia|lia|exact LOAD]. }
 destruct(string_path_actual _ _ _ _ _ PREFIX)as[prefix[COST RUN]].
 exists prefix;split;[exact COST|].
 eapply string_steps_trans;[exact RUN|];apply strlen_wait_then_loss with(bytes:=guest_bytes x);exact STRING.
Qed.
