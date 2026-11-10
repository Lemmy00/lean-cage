(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual outgoing callbacks retain one caller and trace. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayOperations GatewayReadonly
  GatewayCallPath GatewayGuardedCuts GatewayTransferSource GatewayTransferChunk GatewayTransferReceive
  GatewayTransferErrno GatewayTransferRestore GatewayTransferCalls GatewayRuntimeABI GatewayStreamInterface
  GatewayStreamLayout GatewayTransferMath GatewaySendSource GatewaySendChunk GatewaySendOperation
  GatewaySendErrno GatewaySendRestore.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_send_ready_callback_saves_thread {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)temporaries amount before world events returned after next symbol :
  ready before world ->0<=amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  Genv.find_symbol ge _PyEval_SaveThread=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_save_thread_definition ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(transfer_send_ready_cont temporaries)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready
    (Returnstate(Vint Int.zero)(transfer_send_ready_cont temporaries)before)world events returned after next
    gateway_save_thread_definition[](send_save_cont temporaries amount).
Proof.
  intros READY AMOUNT SIZE SYMBOL FUNCTION RUN.
  eapply gateway_retained_callback_execution;
    [exact discipline|reflexivity|cbn[send_save_cont gateway_cont_weight];lia|exact READY| |exact RUN].
  apply actual_send_ready_zero_save_thread_path with(symbol:=symbol);assumption.
Qed.

Theorem actual_saved_callback_sends {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)temporaries amount saved initial
    stream_block stream_offset data_block data_offset before world events returned after next symbol :
  ready before world ->
  (forall memory current,ready memory current->gateway_stream_memory memory stream_block stream_offset initial) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.one) ->
  temporaries!_cursor=Some(Vptr data_block data_offset) ->stream_member_layout ge _descriptor 0 ->
  Genv.find_symbol ge _send=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_send_definition ->
  gateway_steps backend ge
    (gateway_live(Returnstate saved(send_save_cont temporaries amount)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready(Returnstate saved(send_save_cont temporaries amount)before)
    world events returned after next gateway_send_definition
    [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr(transfer_chunk amount));Vint(Int.repr 16384)]
    (send_transfer_cont temporaries amount saved(stream_descriptor initial)).
Proof.
  intros READY CELLS STREAM SENDING CURSOR LAYOUT SYMBOL FUNCTION RUN.
  eapply gateway_guarded_callback_execution with
    (property:=fun memory=>gateway_stream_memory memory stream_block stream_offset initial).
  - exact discipline.
  - exact CELLS.
  - reflexivity.
  - cbn[send_transfer_cont gateway_cont_weight];lia.
  - exact READY.
  - apply actual_saved_thread_send_path with(symbol:=symbol);assumption.
  - exact RUN.
Qed.

Theorem actual_sent_callback_reads_errno {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)temporaries amount saved descriptor count
    before world events returned after next symbol :
  ready before world ->Genv.find_symbol ge ___errno_location=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_errno_location_definition ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vlong count)(send_transfer_cont temporaries amount saved descriptor)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready
    (Returnstate(Vlong count)(send_transfer_cont temporaries amount saved descriptor)before)world events returned after next
    gateway_errno_location_definition[](send_errno_cont temporaries amount saved descriptor count).
Proof.
  intros READY SYMBOL FUNCTION RUN.
  eapply gateway_retained_callback_execution;
    [exact discipline|reflexivity|cbn[send_errno_cont gateway_cont_weight];lia|exact READY| |exact RUN].
  apply actual_sent_count_errno_path with(symbol:=symbol);assumption.
Qed.

Theorem actual_send_captured_callback_restores_thread {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)temporaries amount saved descriptor count pointer number
    before world events returned after next symbol :
  ready before world ->(exists block offset,saved=Vptr block offset) ->
  Genv.find_symbol ge _PyEval_RestoreThread=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_restore_thread_definition ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer Sskip(Kseq transfer_after_errno transfer_iteration_cont)empty_env
      (send_number_values temporaries amount saved descriptor count pointer number)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready
    (State f_host_transfer Sskip(Kseq transfer_after_errno transfer_iteration_cont)empty_env
      (send_number_values temporaries amount saved descriptor count pointer number)before)world events returned after next
    gateway_restore_thread_definition[saved](send_restore_cont temporaries amount saved descriptor count pointer number).
Proof.
  intros READY SAVED SYMBOL FUNCTION RUN.
  eapply gateway_retained_callback_execution;
    [exact discipline|reflexivity|cbn[send_restore_cont gateway_cont_weight];lia|exact READY| |exact RUN].
  apply actual_send_captured_restore_path with(symbol:=symbol);assumption.
Qed.
