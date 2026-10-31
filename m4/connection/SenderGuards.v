(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Exact short-circuit guards for all five source fault selectors. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine Fault
  ResultLayout GlobalReads DecoderControl FrameRecord SenderSource SenderAccess SenderEncodingPrefix
  SenderSelectors CallContexts ReportPaths.
Import ListNotations.
Open Scope Z_scope.
Definition guard_kind_temp tag := match tag with
  | wrong_sequence=>_t'23
  | bad_reserved=>_t'22
  | duplicate_frame=>_t'21
  | short_frame=>_t'20
  | drop_frame=>_t'19
end.
Definition guard_enabled_temp tag := match tag with
  | wrong_sequence=>_t'1
  | bad_reserved=>_t'4
  | duplicate_frame=>_t'8
  | short_frame=>_t'12
  | drop_frame=>_t'15
end.
Definition guard_flag_temp tag := match tag with
  | wrong_sequence=>_t'2
  | bad_reserved=>_t'5
  | duplicate_frame=>_t'9
  | short_frame=>_t'13
  | drop_frame=>_t'16
end.
Definition guard_reply_temp tag := match tag with
  | wrong_sequence=>_t'3
  | bad_reserved=>_t'6
  | duplicate_frame=>_t'10
  | short_frame=>_t'14
  | drop_frame=>_t'17
end.
Definition report_stage_index tag : nat := match tag with
  | wrong_sequence=>0%nat
  | bad_reserved=>1%nat
  | duplicate_frame=>2%nat
  | short_frame=>3%nat
  | drop_frame=>4%nat
end.
Definition guard_prefix tag := Ssequence
  (Sifthenelse (Ebinop One (Etempvar _fd tint) (Econst_int Int.one tint) tint)
    (Ssequence
      (Sset (guard_kind_temp tag) (Efield (Evar _result__1 result_type) _kind tuint))
      (Sset (guard_enabled_temp tag) (Ecast
        (Ebinop Ole (Etempvar (guard_kind_temp tag) tuint) (Econst_int (Int.repr 4) tint) tint) tbool)))
    (Sset (guard_enabled_temp tag) (Econst_int Int.zero tint)))
  (Sifthenelse (Etempvar (guard_enabled_temp tag) tint)
    (Ssequence
      (Scall (Some (guard_reply_temp tag)) (Evar _fault (Tfunction [tptr tschar] tint cc_default))
        [Evar (report_literal tag) (tarray tschar (Z.of_nat (length (report_name tag)+1)))])
      (Sset (guard_flag_temp tag) (Ecast (Etempvar (guard_reply_temp tag) tint) tbool)))
    (Sset (guard_flag_temp tag) (Econst_int Int.zero tint))).
Definition report_stage tag := match statement_drop (report_stage_index tag) sender_reporting with
  Ssequence first _=>first|_=>Sskip end.
Definition report_action tag := match report_stage tag with
  Ssequence _ (Sifthenelse _ action _)=>action|_=>Sskip end.
Theorem report_stage_source : forall tag,
  report_stage tag=Ssequence (guard_prefix tag)
    (Sifthenelse (Etempvar (guard_flag_temp tag) tint) (report_action tag) Sskip).
Proof. intros tag;destruct tag;reflexivity. Qed.
Theorem sender_report_symbols : exists fb wb,
  Genv.find_symbol result_ge _fault=Some fb /\
  Genv.find_funct result_ge (Vptr fb Ptrofs.zero)=Some (Internal f_fault) /\
  Genv.find_symbol result_ge _write_all=Some wb /\
  Genv.find_funct result_ge (Vptr wb Ptrofs.zero)=Some (Internal f_write_all).
Proof. eexists;eexists;split;[vm_compute;reflexivity|]. split;[vm_compute;reflexivity|]. split;vm_compute;reflexivity. Qed.
Lemma fault_report_value : forall mode_bytes tag,
  fault_value mode_bytes (report_name tag)=Val.of_bool (report_matches mode_bytes tag).
Proof. intros;unfold fault_value,report_matches;destruct (compare_bytes mode_bytes (report_name tag));reflexivity. Qed.

Ltac guard_lookup tag := cbn [set_opttemp];repeat first
  [rewrite PTree.gss|rewrite PTree.gso by (destruct tag;discriminate)];first [reflexivity|eassumption].
Ltac guard_expression tag := first
  [apply value_int
  |eapply value_temp;guard_lookup tag
  |eapply value_binary;[guard_expression tag|guard_expression tag|reflexivity]
  |eapply value_unary;[guard_expression tag|reflexivity]
  |eapply value_cast;[guard_expression tag|first [reflexivity|apply cast_boolean_boolean|apply bool_int_cast]]].

Theorem sender_guard_source : forall allow_errors cell (P : mem -> Prop) R m result_local bytes_local r digest
    fd sequence mode mode_bytes locations tag le tail k,
  P m -> frame_result_owned m result_local 0 r digest ->
  sender_selectors cell m mode mode_bytes locations ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  (forall next_le,next_le ! _fd=Some (Vint fd) -> next_le ! _sequence=Some (Vlong sequence) ->
    next_le ! (guard_flag_temp tag)=Some (Val.of_bool (report_selected fd r mode_bytes tag)) ->
    report_returns_allow allow_errors cell P R (State f_send_frame tail k (sender_env result_local bytes_local) next_le m)) ->
  report_returns_allow allow_errors cell P R (State f_send_frame (guard_prefix tag) (Kseq tail k)
    (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell P R m result_local bytes_local r digest fd sequence mode mode_bytes locations tag le tail k
    PM OWN SELECTORS FD SEQ NEXT.
  destruct sender_report_symbols as [fb [wb [FS [FF [WS WF]]]]].
  pose proof (proj1 ((proj2 (proj2 (proj2 SELECTORS))) tag)) as LITERAL.
  pose proof (sender_selector_input _ _ _ _ _ tag SELECTORS) as INPUT.
  unfold guard_prefix.
  Ltac guard_truth := unfold report_selected,report_enabled;
    cbn [Int.cmp Int.cmpu cast_int_int] in *;
    try solve [match goal with CHOICE : _=true |- _=>discriminate CHOICE | CHOICE : _=false |- _=>discriminate CHOICE end];
    repeat rewrite bool_value_zero_test in *;
    repeat match goal with
      | CHOICE : ?b=true |- _=>progress rewrite CHOICE
      | CHOICE : ?b=false |- _=>progress rewrite CHOICE
    end;reflexivity.
  Ltac guard_run allow_errors cell P R m result_local bytes_local r digest fd sequence mode mode_bytes locations tag tail k PM OWN NEXT FS FF LITERAL INPUT :=
    lazymatch goal with |- report_returns_allow _ _ _ _ (State _ ?stmt _ _ _ _) =>
      first [constr_eq stmt tail;
        apply NEXT;[guard_lookup tag|guard_lookup tag|
          cbn [set_opttemp];repeat first [rewrite PTree.gss|rewrite PTree.gso by (destruct tag;discriminate)];guard_truth]|
        lazymatch stmt with
        | Sset _ (Efield _ _ _) =>
          eapply report_returns_source;[exact PM|eapply certified_set_edge;sender_field r OWN|]
        | Sset _ _ =>
          eapply report_returns_source;[exact PM|apply unchanged_store_edge;eapply edge_set;guard_expression tag|]
        | Sifthenelse _ _ _ =>
          eapply report_returns_source;[exact PM|apply unchanged_store_edge;eapply edge_if;
            [guard_expression tag|first [apply boolean_condition|apply boolean_typed_condition|reflexivity]]|];
          try lazymatch goal with |- report_returns_allow _ _ _ _ (State _ (if ?b then _ else _) _ _ _ _) =>
            let CHOICE:=fresh "CHOICE" in destruct b eqn:CHOICE end
        | Scall _ _ _ =>
          eapply report_returns_source;[exact PM| |];
          [eapply certified_call_edge;[reflexivity|
            apply old_expression_value;eapply value_function;[unfold sender_env;cbn;reflexivity|exact FS|reflexivity]|
            eapply cons_argument_values;
              [apply old_expression_value;eapply value_function;
                [unfold sender_env;destruct tag;reflexivity|exact LITERAL|reflexivity]|
               reflexivity|apply no_argument_values]|exact FF|reflexivity]|];
          lazymatch goal with |- report_returns_allow _ _ _ _ (Callstate _ _ ?suffix _) =>
            apply (report_returns_selector allow_errors cell P R m mode
              {|address_block:=locations tag;address_offset:=0|} mode_bytes (report_name tag) suffix
              I ltac:(discriminate) PM INPUT)
          end;rewrite fault_report_value
        | _ =>eapply report_returns_source;[exact PM|apply unchanged_store_edge;WriteAll.structural|]
        end;
        guard_run allow_errors cell P R m result_local bytes_local r digest fd sequence mode mode_bytes locations tag tail k PM OWN NEXT FS FF LITERAL INPUT]
    | |- report_returns_allow _ _ _ _ (Returnstate _ _ _) =>
      eapply report_returns_source;[exact PM|apply unchanged_store_edge;WriteAll.structural|];
      guard_run allow_errors cell P R m result_local bytes_local r digest fd sequence mode mode_bytes locations tag tail k PM OWN NEXT FS FF LITERAL INPUT
    end.
  guard_run allow_errors cell P R m result_local bytes_local r digest fd sequence mode mode_bytes locations tag tail k PM OWN NEXT FS FF LITERAL INPUT.
Qed.
