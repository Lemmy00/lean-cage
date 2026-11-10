(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual source orders readiness before every native transfer
   attempt. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCallPath GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Definition transfer_tail:=match fn_body f_host_transfer with Ssequence _ tail=>tail|_=>Sskip end.
Definition transfer_loop:=match transfer_tail with Ssequence loop _=>loop|_=>Sskip end.
Definition transfer_return:=match transfer_tail with Ssequence _ result=>result|_=>Sskip end.
Definition transfer_loop_first:=match transfer_loop with Sloop first _=>first|_=>Sskip end.
Definition transfer_iteration:=match transfer_loop_first with Ssequence _ body=>body|_=>Sskip end.
Definition transfer_ready_sequence:=match transfer_iteration with Ssequence ready _=>ready|_=>Sskip end.
Definition transfer_after_ready:=match transfer_iteration with Ssequence _ rest=>rest|_=>Sskip end.
Definition transfer_ready_prefix:=match transfer_ready_sequence with Ssequence prefix _=>prefix|_=>Sskip end.
Definition transfer_ready_test:=match transfer_ready_sequence with Ssequence _ test=>test|_=>Sskip end.
Definition transfer_ready_direction:=match transfer_ready_prefix with Ssequence direction _=>direction|_=>Sskip end.
Definition transfer_ready_call:=match transfer_ready_prefix with Ssequence _ call=>call|_=>Sskip end.
Definition transfer_loop_cont:=Kseq transfer_return Kstop.
Definition transfer_iteration_cont:=Kloop1 transfer_loop_first Sskip transfer_loop_cont.
Definition transfer_ready_cont temporaries:=Kcall(Some _t'2)f_host_transfer empty_env
  (PTree.set _t'1(Vint Int.one)temporaries)
  (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)).

Definition transfer_parameters stream data amount:=
  PTree.set _sending(Vint Int.zero)(PTree.set _size(Vlong(Int64.repr amount))
    (PTree.set _data data(PTree.set _stream stream(create_undef_temps(fn_temps f_host_transfer))))).
Definition transfer_loop_values stream data amount:=PTree.set _cursor data(transfer_parameters stream data amount).

Lemma actual_receive_transfer_entry ge stream data amount memory :
  function_entry2 ge f_host_transfer[stream;data;Vlong(Int64.repr amount);Vint Int.zero]memory
    empty_env(transfer_parameters stream data amount)memory.
Proof.
  constructor.
  - apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros a b LEFT RIGHT.
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst a;
      repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst b;discriminate.
  - constructor.
  - reflexivity.
Qed.

Theorem actual_transfer_source_structure :
  transfer_loop=Sloop(Ssequence(Sifthenelse(Etempvar _size tulong)Sskip Sbreak)transfer_iteration)Sskip /\
  transfer_iteration=Ssequence transfer_ready_sequence transfer_after_ready /\
  transfer_ready_sequence=Ssequence transfer_ready_prefix transfer_ready_test /\
  transfer_ready_prefix=Ssequence transfer_ready_direction transfer_ready_call /\
  transfer_ready_direction=Sifthenelse(Etempvar _sending tint)
    (Sset _t'1(Ecast(Econst_int(Int.repr 4)tint)tint))
    (Sset _t'1(Ecast(Econst_int Int.one tint)tint)).
Proof. repeat split;reflexivity. Qed.

Lemma actual_transfer_receive_ready_call (ge:Clight.genv) temporaries stream_block stream_offset memory symbol :
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  store_edge ge
    (State f_host_transfer transfer_ready_call
      (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont))empty_env
      (PTree.set _t'1(Vint Int.one)temporaries)memory)
    (Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
      (transfer_ready_cont temporaries)memory).
Proof.
  intros STREAM SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr stream_block stream_offset).
    + apply old_expression_value,value_temp;rewrite PTree.gso by discriminate;exact STREAM.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint Int.one).
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_transfer_iteration_receive_ready_path (ge:Clight.genv)temporaries stream_block stream_offset memory symbol :
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  gateway_retained_call_path ge(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
    (transfer_ready_cont temporaries)
    (State f_host_transfer transfer_iteration transfer_iteration_cont empty_env temporaries memory).
Proof.
  intros STREAM RECEIVE SYMBOL FUNCTION.
  eapply gateway_retained_next with(next:=State f_host_transfer transfer_ready_sequence
    (Kseq transfer_after_ready transfer_iteration_cont)empty_env temporaries memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_seq.
  - eapply gateway_retained_next with(next:=State f_host_transfer transfer_ready_prefix
      (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont))empty_env temporaries memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_seq.
    + eapply gateway_retained_next with(next:=State f_host_transfer transfer_ready_direction
        (Kseq transfer_ready_call(Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)))
        empty_env temporaries memory).
      * cbn;tauto.
      * intro another;apply unchanged_store_edge,edge_seq.
      * eapply gateway_retained_next with(next:=State f_host_transfer
          (Sset _t'1(Ecast(Econst_int Int.one tint)tint))
          (Kseq transfer_ready_call(Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)))
          empty_env temporaries memory).
        -- cbn;tauto.
        -- intro another;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
           ++ apply old_expression_value,value_temp;exact RECEIVE.
           ++ reflexivity.
        -- eapply gateway_retained_next with(next:=State f_host_transfer Sskip
            (Kseq transfer_ready_call(Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)))
            empty_env(PTree.set _t'1(Vint Int.one)temporaries)memory).
           ++ cbn;tauto.
           ++ intro another;apply certified_set_edge.
              apply cast_expression_value with(v:=Vint Int.one);[apply old_expression_value;constructor|reflexivity].
           ++ eapply gateway_retained_next with(next:=State f_host_transfer transfer_ready_call
               (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont))
               empty_env(PTree.set _t'1(Vint Int.one)temporaries)memory).
              ** cbn;tauto.
              ** intro another;apply unchanged_store_edge,edge_skip_seq.
              ** eapply gateway_retained_next with(next:=Callstate(Internal f_host_ready)
                  [Vptr stream_block stream_offset;Vint Int.one](transfer_ready_cont temporaries)memory).
                 --- cbn;tauto.
                 --- intro another;apply actual_transfer_receive_ready_call with(symbol:=symbol);assumption.
                 --- constructor.
Qed.

Lemma actual_positive_transfer_call_ready_path (ge:Clight.genv) stream_block stream_offset data_block data_offset
    amount memory symbol :
  0<amount<=Int64.max_unsigned ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  gateway_retained_call_path ge(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
    (transfer_ready_cont(transfer_loop_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount))
    (Callstate(Internal f_host_transfer)
      [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]Kstop memory).
Proof.
  intros AMOUNT SYMBOL FUNCTION.
  set(stream:=Vptr stream_block stream_offset).
  set(data:=Vptr data_block data_offset).
  eapply gateway_retained_next with(next:=State f_host_transfer(fn_body f_host_transfer)Kstop
    empty_env(transfer_parameters stream data amount)memory).
  - cbn;tauto.
  - intro another;apply function_entry_source_edge,actual_receive_transfer_entry.
  - eapply gateway_retained_next with(next:=State f_host_transfer(Sset _cursor(Etempvar _data(tptr tvoid)))
      (Kseq transfer_tail Kstop)empty_env(transfer_parameters stream data amount)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_seq.
    + eapply gateway_retained_next with(next:=State f_host_transfer Sskip(Kseq transfer_tail Kstop)
        empty_env(transfer_loop_values stream data amount)memory).
      * cbn;tauto.
      * intro another;apply certified_set_edge;apply old_expression_value,value_temp;reflexivity.
      * eapply gateway_retained_next with(next:=State f_host_transfer transfer_tail Kstop
          empty_env(transfer_loop_values stream data amount)memory).
        -- cbn;tauto.
        -- intro another;apply unchanged_store_edge,edge_skip_seq.
        -- eapply gateway_retained_next with(next:=State f_host_transfer transfer_loop transfer_loop_cont
            empty_env(transfer_loop_values stream data amount)memory).
           ++ cbn;tauto.
           ++ intro another;apply unchanged_store_edge,edge_seq.
           ++ eapply gateway_retained_next with(next:=State f_host_transfer transfer_loop_first transfer_iteration_cont
               empty_env(transfer_loop_values stream data amount)memory).
              ** cbn;tauto.
              ** intro another;apply unchanged_store_edge,edge_loop.
              ** eapply gateway_retained_next with(next:=State f_host_transfer
                  (Sifthenelse(Etempvar _size tulong)Sskip Sbreak)(Kseq transfer_iteration transfer_iteration_cont)
                  empty_env(transfer_loop_values stream data amount)memory).
                 --- cbn;tauto.
                 --- intro another;apply unchanged_store_edge,edge_seq.
                 --- eapply gateway_retained_next with(next:=State f_host_transfer Sskip
                     (Kseq transfer_iteration transfer_iteration_cont)empty_env(transfer_loop_values stream data amount)memory).
                     +++ cbn;tauto.
                     +++ intro another;apply certified_if_edge with(v:=Vlong(Int64.repr amount))(b:=true).
                         *** apply old_expression_value,value_temp;reflexivity.
                         *** change(Some(negb(Int64.eq(Int64.repr amount)Int64.zero))=Some true).
                             rewrite Int64.eq_false;[reflexivity|].
                             intro ZERO;apply(f_equal Int64.unsigned)in ZERO.
                             rewrite Int64.unsigned_repr in ZERO by lia.
                             rewrite Int64.unsigned_zero in ZERO;lia.
                     +++ eapply gateway_retained_next with(next:=State f_host_transfer transfer_iteration
                         transfer_iteration_cont empty_env(transfer_loop_values stream data amount)memory).
                         *** cbn;tauto.
                         *** intro another;apply unchanged_store_edge,edge_skip_seq.
                         *** apply actual_transfer_iteration_receive_ready_path with(symbol:=symbol);
                               try reflexivity;assumption.
Qed.
