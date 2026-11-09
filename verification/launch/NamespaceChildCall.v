(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Construct the helper's actual function entry before its complete source certificate. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber StoreSteps LibraryMachine FreshMemory ReceiverAllocation WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput.
From EntryNamespace Require Import NamespaceStructure NamespaceAllocation NamespaceBorrow NamespaceMemory
  NamespaceTraceRegion NamespaceChildResult NamespaceChildBody.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge handoff_ge handoff_symbol.

Record ChildRequest := {
  request_cell : tls;
  request_borrowed : HandoffBorrowed;
  request_input : int;
  request_output : int;
  request_errors : int;
  request_peer : block;
  request_pid : block;
  request_continuation : cont;
  request_history : list NamespaceMachine.namespace_event
}.

Definition request_arguments request : ChildArguments :=
  {|child_input:=request_input request;child_output:=request_output request;child_errors:=request_errors request;
    child_peer_pointer:=Vptr (request_peer request) Ptrofs.zero;
    child_pid_pointer:=Vptr (request_pid request) Ptrofs.zero|}.

Definition request_scope request pair : ChildScope :=
  {|scope_cell:=request_cell request;
    scope_storage:={|storage_pair:=pair;storage_peer:=request_peer request;storage_pid:=request_pid request|};
    scope_borrowed:=request_borrowed request;scope_input:=request_input request;
    scope_output:=request_output request;scope_errors:=request_errors request;
    scope_continuation:=request_continuation request;scope_history:=request_history request|}.

Theorem child_call_allocates_and_certifies_to request
    (result : block -> list NamespaceMachine.namespace_event -> Clight.state -> Prop)
    (body_certificate : forall pair after,
      child_scope_registers(request_scope request pair)(child_parameters(request_arguments request)) ->
      child_storage_separate(request_cell request)(scope_storage(request_scope request pair)) ->
      child_scope_private(request_scope request pair) ->
      child_storage(request_cell request)(scope_storage(request_scope request pair))after ->
      handoff_borrowed_input(request_cell request)after(request_borrowed request) ->
      namespace_trace_region namespace_ge(request_cell request)(result pair)109(request_history request)
        (State f_create_entry_child(fn_body f_create_entry_child)(request_continuation request)
          (child_env pair)(child_parameters(request_arguments request))after)) before :
  handoff_borrowed_input (request_cell request) before (request_borrowed request) ->
  Mem.range_perm before (request_peer request) 0 4 Cur Freeable ->
  Mem.range_perm before (request_pid request) 0 4 Cur Freeable ->
  request_peer request <> request_pid request ->
  request_peer request <> tls_block (request_cell request) ->
  request_pid request <> tls_block (request_cell request) ->
  ~In (request_peer request) (handoff_borrowed_blocks (request_borrowed request)) ->
  ~In (request_pid request) (handoff_borrowed_blocks (request_borrowed request)) ->
  exists pair,
    ~Mem.valid_block before pair /\
    namespace_trace_region namespace_ge (request_cell request) (result pair)
      110 (request_history request)
      (Callstate (Internal f_create_entry_child) (child_values (request_arguments request))
        (request_continuation request) before).
Proof.
  intros INPUT PEER PID DISTINCT PEER_TLS PID_TLS PEER_PRIVATE PID_PRIVATE.
  destruct (child_entry_allocates before (request_arguments request) (request_continuation request))
    as [pair [after [ENTRY [ALLOC [OLD [FRESH PAIR]]]]]].
  assert (INPUT_AFTER : handoff_borrowed_input (request_cell request) after (request_borrowed request)).
  { eapply namespace_allocation_preserves_borrows; [exact INPUT|exact ALLOC]. }
  assert (PEER_VALID : Mem.valid_block before (request_peer request)).
  { eapply Mem.perm_valid_block with (ofs:=0); apply PEER; lia. }
  assert (PID_VALID : Mem.valid_block before (request_pid request)).
  { eapply Mem.perm_valid_block with (ofs:=0); apply PID; lia. }
  assert (TLS_VALID : Mem.valid_block before (tls_block (request_cell request))).
  { destruct (handoff_borrowed_errno _ _ _ INPUT) as [error [LOW [HIGH [ACCESS LOAD]]]].
    eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies; [exact ACCESS|constructor]. }
  assert (PAIR_TLS : pair<>tls_block (request_cell request)) by (intro SAME; subst pair; contradiction).
  assert (PEER_PAIR : request_peer request<>pair) by (intro SAME; subst pair; contradiction).
  assert (PID_PAIR : request_pid request<>pair) by (intro SAME; subst pair; contradiction).
  assert (PAIR_PRIVATE : ~In pair (handoff_borrowed_blocks (request_borrowed request))).
  { eapply namespace_fresh_local_separate_borrows; [exact INPUT|exact FRESH]. }
  exists pair; split; [exact FRESH|].
  eapply namespace_trace_source_prepend; [exact ENTRY|].
  apply body_certificate.
  - unfold child_scope_registers,request_scope,child_parameters,request_arguments; cbn.
    repeat split; WriteAll.lookup.
  - unfold child_storage_separate,request_scope; cbn; repeat split; assumption.
  - unfold child_scope_private,request_scope; cbn; repeat split; assumption.
  - unfold child_storage,request_scope; cbn.
    split; [exact (handoff_borrowed_errno _ _ _ INPUT_AFTER)|].
    split; [exact PAIR|]. split.
    + intros position RANGE; eapply local_allocations_perms; [exact ALLOC|apply PEER; exact RANGE].
    + intros position RANGE; eapply local_allocations_perms; [exact ALLOC|apply PID; exact RANGE].
  - exact INPUT_AFTER.
Qed.

Theorem child_call_allocates_and_certifies request before :
  handoff_borrowed_input (request_cell request) before (request_borrowed request) ->
  Mem.range_perm before (request_peer request) 0 4 Cur Freeable ->
  Mem.range_perm before (request_pid request) 0 4 Cur Freeable ->
  request_peer request <> request_pid request ->
  request_peer request <> tls_block (request_cell request) ->
  request_pid request <> tls_block (request_cell request) ->
  ~In (request_peer request) (handoff_borrowed_blocks (request_borrowed request)) ->
  ~In (request_pid request) (handoff_borrowed_blocks (request_borrowed request)) ->
  exists pair,
    ~Mem.valid_block before pair /\
    namespace_trace_region namespace_ge (request_cell request) (ChildResult (request_scope request pair))
      110 (request_history request)
      (Callstate (Internal f_create_entry_child) (child_values (request_arguments request))
        (request_continuation request) before).
Proof.
  eapply child_call_allocates_and_certifies_to.
  intros pair after;apply complete_child_body_trace.
Qed.
