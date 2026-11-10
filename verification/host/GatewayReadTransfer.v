(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: A successful read uses the same checked transfer and caller
   continuation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayReturns GatewayCallPath
  GatewayReadGuard GatewayReturnTypes GatewayStreamInterface GatewayStreamLayout GatewayStreamMemory GatewayFrames.
Import ListNotations.
Open Scope Z_scope.

Definition read_transfer_return_values stream data amount remaining returned:=
  PTree.set _t'1 returned(read_guard_values stream data amount remaining).

Lemma read_failed_transfer_path ge stream data amount remaining memory returned :
  returned<>Int.zero ->gateway_constant_path ge(Vint(Int.neg Int.one))
    (Returnstate(Vint returned)(read_transfer_cont stream data amount remaining)memory).
Proof.
  intro NONZERO.
  eapply gateway_constant_next with(next:=State f_host_read Sskip
    (Kseq read_transfer_test(Kseq read_after_transfer Kstop))empty_env
    (read_transfer_return_values stream data amount remaining(Vint returned))memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_constant_next with(next:=State f_host_read read_transfer_test(Kseq read_after_transfer Kstop)empty_env
      (read_transfer_return_values stream data amount remaining(Vint returned))memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_constant_next with(next:=State f_host_read
        (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))(Kseq read_after_transfer Kstop)empty_env
        (read_transfer_return_values stream data amount remaining(Vint returned))memory).
      * cbn;tauto.
      * intro another;apply certified_if_edge with(v:=Vint returned)(b:=true).
        -- apply old_expression_value;apply value_temp;reflexivity.
        -- change(Some(negb(Int.eq returned Int.zero))=Some true).
           rewrite Int.eq_false by exact NONZERO;reflexivity.
      * eapply gateway_constant_at_return with(value:=Vint(Int.neg Int.one)).
        -- reflexivity.
        -- intro another;apply old_expression_value;eapply value_unary;[constructor|reflexivity].
        -- reflexivity.
Qed.

Lemma read_undefined_transfer_path ge stream data amount remaining memory :
  gateway_blocked_path ge(Returnstate Vundef(read_transfer_cont stream data amount remaining)memory).
Proof.
  eapply gateway_blocked_next with(next:=State f_host_read Sskip
    (Kseq read_transfer_test(Kseq read_after_transfer Kstop))empty_env
    (read_transfer_return_values stream data amount remaining Vundef)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_blocked_next with(next:=State f_host_read read_transfer_test(Kseq read_after_transfer Kstop)empty_env
      (read_transfer_return_values stream data amount remaining Vundef)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + apply gateway_blocked_at.
      * cbn;tauto.
      * intros;discriminate.
      * intros another trace target STEP;inversion STEP;subst;
          try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
        match goal with VALUE:eval_expr _ _ _ _(Etempvar _t'1 _) _|-_=>
          pose proof(evaluated_unique _ _ _ _ _ _
            (value_temp _ _ _ _ _ tint Vundef ltac:(apply PTree.gss))_ VALUE)as SAME;subst end.
        discriminate.
Qed.

Theorem actual_successful_read_transfer_return {World Event}(backend:gateway_backend World Event)ge
    stream data amount remaining memory world events returned after next :
  gateway_int_return_value returned ->
  gateway_steps backend ge
    (gateway_live(Returnstate returned(read_transfer_cont stream data amount remaining)memory)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->returned=Vint Int.zero.
Proof.
  intros[UNDEFINED|[ZERO|FAILED]]RUN;[subst returned|exact ZERO|subst returned].
  - exfalso;eapply gateway_blocked_cannot_return;[apply read_undefined_transfer_path|exact RUN].
  - pose proof(gateway_constant_path_actual backend ge _ _ world events(Vint Int.zero)after next
      (read_failed_transfer_path ge stream data amount remaining memory(Int.neg Int.one)ltac:(discriminate))RUN)as BAD.
    discriminate BAD.
Qed.

Theorem actual_successful_read_body_transfer_execution {World Event}(backend:gateway_backend World Event)ge
    stream_block stream_offset data_block data_offset amount initial before world events after next active
    (private:gateway_private_contract backend(gateway_stream_region stream_block stream_offset)active)symbol :
  active world ->gateway_stream_memory before stream_block stream_offset initial ->
  stream_member_layout ge _remaining 24 ->Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->
  0<=amount<=Int64.max_unsigned ->Genv.find_symbol ge _host_transfer=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_transfer) ->
  gateway_steps backend ge
    (gateway_live(State f_host_read(fn_body f_host_read)Kstop empty_env
      (read_parameters(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  amount<=Int64.unsigned(stream_remaining initial) /\
  exists prefix transfer_events caller_events called_memory called_world transferred transferred_world,
    events=prefix++transfer_events++caller_events /\
    gateway_steps backend ge
      (gateway_live(State f_host_read(fn_body f_host_read)Kstop empty_env
        (read_parameters(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount)before)world)prefix
      (gateway_live(Callstate(Internal f_host_transfer)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
        (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
          (stream_remaining initial))called_memory)called_world) /\
    gateway_stream_memory called_memory stream_block stream_offset initial /\active called_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_transfer)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]Kstop
        called_memory)called_world)transfer_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop transferred)transferred_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)
        (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
          (stream_remaining initial))transferred)transferred_world)caller_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros ACTIVE CELLS LAYOUT BOUND AMOUNT SYMBOL FUNCTION RUN.
  destruct(actual_successful_read_body_calls_transfer backend ge stream_block stream_offset data_block data_offset
    amount initial before world events after next active private symbol ACTIVE CELLS LAYOUT BOUND AMOUNT
    SYMBOL FUNCTION RUN)as[FITS[prefix[suffix[memory[called_world[EVENTS[PREFIX[CELLS1[ACTIVE1 REST]]]]]]]]].
  split;[exact FITS|].
  destruct(gateway_return_cut backend ge(Internal f_host_transfer)
    [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
    (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount(stream_remaining initial))
    memory called_world suffix(Returnstate(Vint Int.zero)Kstop after)next ltac:(reflexivity)
    ltac:(cbn[read_transfer_cont gateway_continuation gateway_cont_weight];lia)REST)
    as[transfer_events[caller_events[returned[transferred[transferred_world[SUFFIX[TRANSFER CALLER]]]]]]].
  pose proof(gateway_actual_int_return backend ge f_host_transfer _ _ _ _ _ _ _
    actual_host_transfer_return_profile TRANSFER)as TYPE.
  pose proof(actual_successful_read_transfer_return backend ge(Vptr stream_block stream_offset)
    (Vptr data_block data_offset)amount(stream_remaining initial)transferred transferred_world caller_events
    returned after next TYPE CALLER)as ZERO;subst returned.
  exists prefix,transfer_events,caller_events,memory,called_world,transferred,transferred_world.
  split;[rewrite EVENTS,SUFFIX;reflexivity|]. split;[exact PREFIX|].
  split;[exact CELLS1|]. split;[exact ACTIVE1|]. split;assumption.
Qed.
