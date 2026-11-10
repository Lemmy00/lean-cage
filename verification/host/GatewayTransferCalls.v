(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Source call cuts retain one caller, trace, memory and world. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayOperations GatewayReadonly
  GatewayCallPath GatewayGuardedCuts GatewayTransferSource GatewayTransferChunk GatewayTransferReceive
  GatewayTransferErrno GatewayTransferRestore GatewayRuntimeABI GatewayStreamInterface GatewayStreamLayout GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_call_body_prefix {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    source world prefix definition arguments continuation called called_world operation result changed changed_world :
  is_call_cont continuation ->
  gateway_steps backend ge(gateway_live source world)prefix
    (gateway_live(Callstate definition arguments continuation called)called_world) ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop called)called_world)operation
    (gateway_live(Returnstate result Kstop changed)changed_world) ->
  gateway_steps backend ge(gateway_live source world)(prefix++operation)
    (gateway_live(Returnstate result continuation changed)changed_world).
Proof.
  intros CALL PREFIX OPERATION;eapply gateway_steps_append;[exact PREFIX|].
  exact(gateway_plug_steps backend ge(gateway_live(Callstate definition arguments Kstop called)called_world)
    operation(gateway_live(Returnstate result Kstop changed)changed_world)continuation CALL OPERATION).
Qed.

Definition gateway_callback_execution {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (ready:mem->World->Prop)source world events returned after next definition arguments continuation :Prop:=
  exists prefix operation caller called called_world result changed changed_world,
    events=prefix++operation++caller /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge(gateway_live source world)prefix
      (gateway_live(Callstate definition arguments continuation called)called_world) /\ready called called_world /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop called)called_world)operation
      (gateway_live(Returnstate result Kstop changed)changed_world) /\
    gateway_steps backend ge(gateway_live(Returnstate result continuation changed)changed_world)caller
      (gateway_live(Returnstate returned Kstop after)next).

Theorem gateway_retained_callback_execution {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)source world events returned after next
    definition arguments continuation :
  is_call_cont continuation ->(0<gateway_cont_weight continuation)%nat ->
  ready(memory_of source)world ->gateway_retained_call_path ge definition arguments continuation source ->
  gateway_steps backend ge(gateway_live source world)events(gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready source world events returned after next definition arguments continuation.
Proof.
  intros CALL WEIGHT READY SCRIPT RUN.
  destruct(gateway_retained_call_ready_cut backend ge ready discipline definition arguments continuation source
    world events returned after next SCRIPT READY RUN)
    as[prefix[suffix[called[called_world[EVENTS[QUIET[PREFIX[CALLED REST]]]]]]]].
  destruct(gateway_return_cut backend ge definition arguments continuation called called_world suffix
    (Returnstate returned Kstop after)next CALL ltac:(cbn[gateway_continuation gateway_cont_weight];exact WEIGHT)REST)
    as[operation[caller[result[changed[changed_world[SUFFIX[OPERATION CALLER]]]]]]].
  exists prefix,operation,caller,called,called_world,result,changed,changed_world.
  split;[rewrite EVENTS,SUFFIX;reflexivity|]. split;[exact QUIET|]. split;[exact PREFIX|].
  split;[exact CALLED|]. split;assumption.
Qed.

Theorem gateway_guarded_callback_execution {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)property
    (sufficient:forall memory current,ready memory current->property memory)
    source world events returned after next definition arguments continuation :
  is_call_cont continuation ->(0<gateway_cont_weight continuation)%nat ->
  ready(memory_of source)world ->gateway_guarded_retained_path ge property definition arguments continuation source ->
  gateway_steps backend ge(gateway_live source world)events(gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready source world events returned after next definition arguments continuation.
Proof.
  intros CALL WEIGHT READY SCRIPT RUN.
  destruct(gateway_guarded_ready_cut backend ge property definition arguments continuation ready discipline sufficient
    source world events returned after next READY SCRIPT RUN)
    as[prefix[suffix[called[called_world[EVENTS[QUIET[PREFIX[CALLED REST]]]]]]]].
  destruct(gateway_return_cut backend ge definition arguments continuation called called_world suffix
    (Returnstate returned Kstop after)next CALL ltac:(cbn[gateway_continuation gateway_cont_weight];exact WEIGHT)REST)
    as[operation[caller[result[changed[changed_world[SUFFIX[OPERATION CALLER]]]]]]].
  exists prefix,operation,caller,called,called_world,result,changed,changed_world.
  split;[rewrite EVENTS,SUFFIX;reflexivity|]. split;[exact QUIET|]. split;[exact PREFIX|].
  split;[exact CALLED|]. split;assumption.
Qed.

Theorem actual_ready_callback_saves_thread {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)temporaries amount before world events returned after next symbol :
  ready before world ->0<=amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  Genv.find_symbol ge _PyEval_SaveThread=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_save_thread_definition ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(transfer_ready_cont temporaries)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready
    (Returnstate(Vint Int.zero)(transfer_ready_cont temporaries)before)world events returned after next
    gateway_save_thread_definition[](transfer_save_cont temporaries amount).
Proof.
  intros READY AMOUNT SIZE SYMBOL FUNCTION RUN.
  eapply gateway_retained_callback_execution;
    [exact discipline|reflexivity|cbn[transfer_save_cont gateway_cont_weight];lia|exact READY| |exact RUN].
  apply actual_ready_zero_save_thread_path with(symbol:=symbol);assumption.
Qed.

Theorem actual_saved_callback_receives {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)temporaries amount saved initial
    stream_block stream_offset data_block data_offset before world events returned after next symbol :
  ready before world ->
  (forall memory current,ready memory current->gateway_stream_memory memory stream_block stream_offset initial) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  temporaries!_cursor=Some(Vptr data_block data_offset) ->stream_member_layout ge _descriptor 0 ->
  Genv.find_symbol ge _recv=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_receive_definition ->
  gateway_steps backend ge
    (gateway_live(Returnstate saved(transfer_save_cont temporaries amount)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready(Returnstate saved(transfer_save_cont temporaries amount)before)
    world events returned after next gateway_receive_definition
    [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr(transfer_chunk amount));Vint Int.zero]
    (transfer_receive_cont temporaries amount saved(stream_descriptor initial)).
Proof.
  intros READY CELLS STREAM RECEIVE CURSOR LAYOUT SYMBOL FUNCTION RUN.
  eapply gateway_guarded_callback_execution with
    (property:=fun memory=>gateway_stream_memory memory stream_block stream_offset initial).
  - exact discipline.
  - exact CELLS.
  - reflexivity.
  - cbn[transfer_receive_cont gateway_cont_weight];lia.
  - exact READY.
  - apply actual_saved_thread_receive_path with(symbol:=symbol);assumption.
  - exact RUN.
Qed.

Theorem actual_received_callback_reads_errno {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)temporaries amount saved descriptor count
    before world events returned after next symbol :
  ready before world ->Genv.find_symbol ge ___errno_location=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_errno_location_definition ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vlong count)(transfer_receive_cont temporaries amount saved descriptor)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready
    (Returnstate(Vlong count)(transfer_receive_cont temporaries amount saved descriptor)before)world events returned after next
    gateway_errno_location_definition[](transfer_errno_cont temporaries amount saved descriptor count).
Proof.
  intros READY SYMBOL FUNCTION RUN.
  eapply gateway_retained_callback_execution;
    [exact discipline|reflexivity|cbn[transfer_errno_cont gateway_cont_weight];lia|exact READY| |exact RUN].
  apply actual_received_count_errno_path with(symbol:=symbol);assumption.
Qed.

Theorem actual_captured_callback_restores_thread {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) ready
    (discipline:gateway_runtime_discipline backend ready)temporaries amount saved descriptor count pointer number
    before world events returned after next symbol :
  ready before world ->(exists block offset,saved=Vptr block offset) ->
  Genv.find_symbol ge _PyEval_RestoreThread=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_restore_thread_definition ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer Sskip(Kseq transfer_after_errno transfer_iteration_cont)empty_env
      (transfer_number_values temporaries amount saved descriptor count pointer number)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_callback_execution backend ge ready
    (State f_host_transfer Sskip(Kseq transfer_after_errno transfer_iteration_cont)empty_env
      (transfer_number_values temporaries amount saved descriptor count pointer number)before)world events returned after next
    gateway_restore_thread_definition[saved](transfer_restore_cont temporaries amount saved descriptor count pointer number).
Proof.
  intros READY SAVED SYMBOL FUNCTION RUN.
  eapply gateway_retained_callback_execution;
    [exact discipline|reflexivity|cbn[transfer_restore_cont gateway_cont_weight];lia|exact READY| |exact RUN].
  apply actual_captured_number_restore_path with(symbol:=symbol);assumption.
Qed.
