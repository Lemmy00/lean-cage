(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source initialization carries one actual native and aggregate reference context. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Memory Integers Floats Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayInterpreterRuntime GatewayInitializationRegions
  GatewayInitializationStores GatewayReferenceHistoryThreads GatewayReferenceThreads GatewayReferenceHeld GatewayReferenceLedger
  GatewayReferenceAccounting GatewayReferenceHistory GatewayReferenceAbandon GatewayObjectThreads
  GatewayBootstrapRuntime GatewayThreadRuntime GatewayStreamInterface.

Definition gateway_initialization_context {World} native stable base symbols snapshot active complete
    python objects decimal_float ledger retired held (current : World -> Values.val) (identifier : World -> int64)
    pointer number memory world : Prop :=
  @gateway_initialization_regions World native stable base symbols snapshot active complete memory world /\
  gateway_reference_history_scope python objects decimal_float ledger retired held world /\
  current world = pointer /\ identifier world = number.

Section Retention.
Context {World Event} (backend : gateway_backend World Event) io native stable base thread_errno heap_allocation
  python objects current identifier
  (threads : gateway_thread_runtime backend io native stable base thread_errno)
  (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (interpreter : gateway_interpreter_runtime backend io native stable base python objects current identifier)
  (symbols : gateway_initialization_symbols) (snapshot : mem) (active complete : int)
  (decimal_float : list Z -> Floats.float -> Prop) (ledger : gateway_reference_ledger)
  (retired : list gateway_abandoned_reference) (held : list gateway_held_value)
  (pointer : Values.val) (number : int64).
Let property := gateway_initialization_context native stable base symbols snapshot active complete
  python objects decimal_float ledger retired held current identifier pointer number.

Theorem gateway_initialization_context_ambient : GatewayFramedRuntime.gateway_ambient_closed backend property.
Proof.
  intros before world after next [REGIONS [HISTORY [CURRENT IDENTIFIER]]] INTERFERENCE.
  pose proof (proj1 (initialization_region_buffers _ _ _ _ _ _ _ _ _ REGIONS)) as SIDE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ threads None before world after next SIDE INTERFERENCE)
    as [NEXT [ACCESS FRAME]].
  destruct (gateway_interpreter_ambient_identity _ _ _ _ _ _ _ _ _ interpreter before world after next SIDE INTERFERENCE)
    as [NEXT_CURRENT NEXT_IDENTIFIER].
  split; [eapply gateway_initialization_regions_quiet; eassumption |]. split.
  - eapply gateway_reference_history_scope_effect; [exact HISTORY |].
    eapply gateway_reference_thread_ambient; [exact reference_threads |exact SIDE |exact INTERFERENCE].
  - split; congruence.
Qed.

Theorem gateway_initialization_context_query before world after next observed :
  property before world ->
  gateway_interpreter_query_post io native stable base python objects current identifier before world after next observed ->
  property after next.
Proof.
  intros [REGIONS [HISTORY [CURRENT IDENTIFIER]]] [POST PYTHON OBJECTS HEAP NEXT_CURRENT NEXT_IDENTIFIER].
  destruct POST as [SIDE [ACCESS [FRAME QUIET]]].
  split; [eapply gateway_initialization_regions_quiet; eassumption |]. split.
  - unfold gateway_reference_history_scope, gateway_reference_scope, gateway_reference_held in HISTORY |- *.
    rewrite PYTHON, OBJECTS; exact HISTORY.
  - split; congruence.
Qed.
End Retention.

Theorem gateway_initialization_context_store {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno (threads : gateway_thread_runtime backend io native stable base thread_errno)
    symbols snapshot active complete python objects decimal_float ledger retired held current identifier pointer number
    (completed : bool) word before world after :
  gateway_initialization_context native stable base symbols snapshot active complete
    python objects decimal_float ledger retired held current identifier pointer number before world ->
  Mem.store Mint32 before (initialization_flag_object symbols completed) 0 (Vint word) = Some after ->
  gateway_initialization_context native stable base symbols snapshot
    (if completed then active else word) (if completed then word else complete)
    python objects decimal_float ledger retired held current identifier pointer number after world.
Proof.
  intros [REGIONS REST] STORE; split; [|exact REST].
  eapply gateway_initialization_regions_store; [exact threads |exact REGIONS |exact STORE].
Qed.
