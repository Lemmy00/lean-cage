(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: All actual post-send branches retain the caller's stream and buffers. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationMemory GatewayThreadRuntime GatewayStreamInterface GatewayStreamAccess GatewayStreamMemory
  GatewayStreamLayout GatewayRuntimeABI GatewayReadContext GatewayReadMemory GatewayOperations GatewayContexts
  GatewayRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition control_cancel_assignment := Sassign (stream_member _cancellation_sent tint)
  (Econst_int Int.one tint).
Definition control_errno_expression := Evar ___errno_location (Tfunction [] (tptr tint) cc_default).

Fixpoint control_tail_statement (body : statement) : Prop :=
  match body with
  | Sskip | Sreturn _ => True
  | Sset identifier _ => identifier <> _stream
  | Ssequence first second | Sifthenelse _ first second =>
    control_tail_statement first /\ control_tail_statement second
  | Sassign target value => Sassign target value = control_cancel_assignment
  | Scall destination function arguments =>
    destination <> Some _stream /\ function = control_errno_expression /\ arguments = []
  | _ => False
  end.

Fixpoint control_tail_cont (continuation : cont) : Prop :=
  match continuation with
  | Kstop => True
  | Kseq body rest => control_tail_statement body /\ control_tail_cont rest
  | _ => False
  end.

Lemma control_tail_call_cont continuation : control_tail_cont continuation -> call_cont continuation = Kstop.
Proof. induction continuation; cbn; tauto. Qed.

Lemma control_tail_is_call_cont continuation :
  control_tail_cont continuation -> is_call_cont continuation -> continuation = Kstop.
Proof. destruct continuation; cbn; tauto. Qed.

Definition control_tail_callback command stream (continuation : cont) : Prop :=
  exists destination temporaries rest,
    continuation = Kcall destination f_host_control (control_environment command) temporaries rest /\
    destination <> Some _stream /\ temporaries ! _stream = Some stream /\ control_tail_cont rest.

Definition control_tail_source command stream (source : Clight.state) : Prop :=
  match source with
  | State function body continuation environment temporaries _ =>
    function = f_host_control /\ environment = control_environment command /\
    temporaries ! _stream = Some stream /\ control_tail_statement body /\ control_tail_cont continuation
  | Callstate definition arguments continuation _ =>
    definition = gateway_errno_location_definition /\ arguments = [] /\
    control_tail_callback command stream continuation
  | Returnstate _ continuation _ => continuation = Kstop \/ control_tail_callback command stream continuation
  end.

Lemma actual_control_suffix_classification : control_tail_statement control_after_send.
Proof. cbn; intuition discriminate. Qed.

Lemma actual_control_cancel_edge ge command temporaries before stream_block stream_offset after continuation :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  stream_member_layout ge _cancellation_sent 8 ->
  Ptrofs.unsigned stream_offset + 48 <= Ptrofs.modulus ->
  Mem.store Mint32 before stream_block (Ptrofs.unsigned stream_offset + 8) (Vint Int.one) = Some after ->
  store_edge ge
    (State f_host_control control_cancel_assignment continuation (control_environment command) temporaries before)
    (State f_host_control Sskip continuation (control_environment command) temporaries after).
Proof.
  intros STREAM LAYOUT BOUND STORE.
  eapply actual_stream_member_store with (delta := 8) (chunk := Mint32) (value := Vint Int.one).
  - exact STREAM.
  - exact LAYOUT.
  - reflexivity.
  - apply old_expression_value; constructor.
  - reflexivity.
  - unfold Mem.storev, gateway_stream_slot.
    rewrite (gateway_stream_slot_unsigned stream_offset 8) by (try exact BOUND; lia).
    destruct (zle (Ptrofs.unsigned stream_offset + 8 + size_chunk Mint32) Ptrofs.modulus);
      [exact STORE | cbn [size_chunk] in *; lia].
Qed.

Lemma actual_control_tail_errno_edge (ge : Clight.genv) command temporaries memory continuation destination symbol :
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  store_edge ge
    (State f_host_control (Scall destination control_errno_expression []) continuation
      (control_environment command) temporaries memory)
    (Callstate gateway_errno_location_definition []
      (Kcall destination f_host_control (control_environment command) temporaries continuation) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity | exact SYMBOL | reflexivity].
  - apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac control_tail_impossible :=
  try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end;
  try match goal with BAD : control_tail_cont (Kloop1 _ _ _) |- _ => contradiction end;
  try match goal with BAD : control_tail_cont (Kloop2 _ _ _) |- _ => contradiction end;
  try match goal with BAD : control_tail_cont (Kswitch _) |- _ => contradiction end.

Section CancellationSuffix.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).

Definition control_tail_active command memory world : Prop :=
  exists current,
    control_context native_private stable_readonly discipline stream_block stream_offset current
      data_block data_offset amount readonly command memory world /\
    gateway_stream_transport_after initial current.
Definition control_tail_result memory world : Prop :=
  exists current,
    gateway_read_context native_private stable_readonly discipline None stream_block stream_offset current
      data_block data_offset amount readonly memory world /\
    gateway_stream_transport_after initial current.

Lemma control_tail_mark_context command before world after current :
  control_context native_private stable_readonly discipline stream_block stream_offset current
    data_block data_offset amount readonly command before world ->
  gateway_stream_transport_after initial current ->
  Mem.store Mint32 before stream_block (Ptrofs.unsigned stream_offset + 8) (Vint Int.one) = Some after ->
  control_tail_active command after world.
Proof.
  intros [INPUT [PRIVATE [BUFFER SEPARATE]]] TRANSPORT STORE.
  destruct INPUT as [SIDE [STREAM [DATA [STABLE RAW]]]].
  destruct (gateway_mark_cancel_read_inputs _ _ _ _ _ _ _ _ _ RAW STORE) as [MARKED [FRAME PERMISSIONS]].
  exists (gateway_stream_mark_cancelled current); split.
  - split.
    + split.
      * eapply gateway_thread_native_store; [exact runtime | exact SIDE | exact STREAM | exact STORE].
      * split; [exact STREAM |]. split; [exact DATA |]. split; assumption.
    + split; [exact PRIVATE |]. split; [|exact SEPARATE].
      intros position RANGE; apply (proj1 (PERMISSIONS _ _ _ _)); apply BUFFER; exact RANGE.
  - eapply gateway_stream_transport_transitive; [exact TRANSPORT | apply gateway_stream_mark_transport].
Qed.

Lemma control_tail_active_ambient command : gateway_runtime_discipline backend (control_tail_active command).
Proof.
  intros before world after next [current [CONTEXT TRANSPORT]] INTERFERENCE.
  exists current; split; [|exact TRANSPORT].
  eapply control_context_ambient; [exact runtime | exact CONTEXT | exact INTERFERENCE].
Qed.

Lemma control_tail_result_ambient : gateway_runtime_discipline backend control_tail_result.
Proof.
  intros before world after next [current [CONTEXT TRANSPORT]] INTERFERENCE.
  exists current; split; [|exact TRANSPORT].
  eapply gateway_read_context_ambient; [exact runtime | exact CONTEXT | exact INTERFERENCE].
Qed.

Definition control_tail_memory command source memory world : Prop :=
  match source with
  | Returnstate _ Kstop _ => control_tail_result memory world
  | _ => control_tail_active command memory world
  end.

Definition control_tail_runtime command (state : gateway_state World) : Prop :=
  match state with
  | gateway_live source world => control_tail_source command (Vptr stream_block stream_offset) source /\
    control_tail_memory command source (memory_of source) world
  | gateway_dead _ _ => True
  end.

Lemma control_tail_active_free command before world after :
  control_tail_active command before world ->
  Mem.free_list before (blocks_of_env ge (control_environment command)) = Some after ->
  control_tail_result after world.
Proof.
  intros [current [CONTEXT TRANSPORT]] FREE.
  exists current; split; [|exact TRANSPORT].
  exact (proj1 (control_scope_free backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset current data_block data_offset amount readonly command before world after CONTEXT FREE)).
Qed.

Lemma control_tail_returned_callback command value continuation before world after_source :
  control_tail_callback command (Vptr stream_block stream_offset) continuation ->
  control_tail_active command before world ->
  step2 ge (Returnstate value continuation before) E0 after_source ->
  control_tail_runtime command (gateway_live after_source world).
Proof.
  intros (destination & temporaries & rest & CONT & DESTINATION & STREAM & TAIL) ACTIVE STEP.
  subst continuation; inversion STEP; subst.
  split; [|exact ACTIVE]. cbn; split; [reflexivity |]. split; [reflexivity |]. split.
  - destruct destination as [identifier |]; cbn; [|exact STREAM].
    rewrite PTree.gso; [exact STREAM | congruence].
  - split; [exact I | exact TAIL].
Qed.

Lemma control_tail_internal_step command source world trace target symbol :
  stream_member_layout ge _cancellation_sent 8 ->
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  control_tail_runtime command (gateway_live source world) -> internal_state source ->
  step2 ge source trace target -> control_tail_runtime command (gateway_live target world).
Proof.
  intros LAYOUT SYMBOL FUNCTION [PROFILE READY] INTERNAL STEP.
  destruct source as [function body continuation environment temporaries before |
    definition arguments continuation before | returned continuation before].
  - destruct PROFILE as [FN [ENV [STREAM [BODY CONT]]]]; subst function environment.
    change (control_tail_active command before world) in READY.
    destruct body; cbn [control_tail_statement] in BODY; try contradiction.
    + inversion STEP; subst.
      all: cbn [control_tail_cont] in CONT; try contradiction.
      all: try match goal with CALL : is_call_cont ?kont |- _ =>
        pose proof (control_tail_is_call_cont kont CONT CALL) as STOP; subst kont end.
      all: try match goal with BAD : control_tail_cont (Kloop1 _ _ _) |- _ => contradiction end.
      all: try match goal with BAD : control_tail_cont (Kloop2 _ _ _) |- _ => contradiction end.
      all: try match goal with BAD : control_tail_cont (Kswitch _) |- _ => contradiction end.
      all: try solve [match type of CONT with _ /\ _ => destruct CONT as [NEXT REST] end;
        split; [cbn; repeat split; assumption | exact READY]].
      all: split; [cbn; left; reflexivity |]; eapply control_tail_active_free; eassumption.
    + change (Sassign e e0 = control_cancel_assignment) in BODY.
      inversion BODY; subst e e0.
      destruct READY as [current [CONTEXT TRANSPORT]].
      pose proof (proj2 (proj2 (proj2 (proj2 (proj1 CONTEXT))))) as RAW.
      destruct (gateway_cancel_store_exists _ _ _ _ _ _ _ _ RAW) as [changed STORE].
      destruct (actual_control_cancel_edge ge command temporaries before stream_block stream_offset
        changed continuation STREAM LAYOUT (gateway_read_stream_bounds _ _ _ _ _ _ _ _ RAW) STORE)
        as [IN [REAL UNIQUE]].
      destruct (UNIQUE _ _ STEP) as [TRACE SAME]; subst trace target.
      split.
      * cbn; repeat split; try reflexivity; assumption.
      * eapply control_tail_mark_context; eassumption.
    + inversion STEP; subst; control_tail_impossible.
      split; [|exact READY].
      cbn; split; [reflexivity |]. split; [reflexivity |]. split.
      * rewrite PTree.gso; [exact STREAM | congruence].
      * split; [exact I | exact CONT].
    + destruct BODY as [DESTINATION [EXPRESSION ARGUMENTS]]; subst e l.
      destruct (actual_control_tail_errno_edge ge command temporaries before continuation o symbol SYMBOL FUNCTION)
        as [IN [REAL UNIQUE]].
      destruct (UNIQUE _ _ STEP) as [TRACE SAME]; subst trace target.
      split; [|exact READY]. cbn; split; [reflexivity |]. split; [reflexivity |].
      exists o, temporaries, continuation; repeat split; assumption.
    + destruct BODY as [FIRST SECOND]; inversion STEP; subst; control_tail_impossible.
      split; [|exact READY]. cbn; repeat split; assumption.
    + destruct BODY as [FIRST SECOND]; inversion STEP; subst; control_tail_impossible.
      destruct b; split; try exact READY; cbn; repeat split; assumption.
    + inversion STEP; subst; control_tail_impossible.
      all: rewrite (control_tail_call_cont continuation CONT).
      all: split; [cbn; left; reflexivity |].
      all: eapply control_tail_active_free; eassumption.
  - cbn [internal_state] in INTERNAL; destruct PROFILE as [DEFINITION _]; subst definition; contradiction.
  - destruct PROFILE as [STOP | CALLBACK].
    + subst continuation; inversion STEP.
    + inversion STEP; subst; eapply control_tail_returned_callback; eassumption.
Qed.

Lemma control_tail_source_replace command stream source memory :
  control_tail_source command stream source ->
  control_tail_source command stream (gateway_replace_memory source memory).
Proof. destruct source; cbn; tauto. Qed.

Lemma control_tail_ambient command source world after next :
  control_tail_runtime command (gateway_live source world) ->
  gateway_interference backend (memory_of source) world after next ->
  control_tail_runtime command (gateway_live (gateway_replace_memory source after) next).
Proof.
  intros [PROFILE READY] INTERFERENCE; split; [apply control_tail_source_replace; exact PROFILE |].
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | value continuation memory]; cbn in *.
  - eapply control_tail_active_ambient; eassumption.
  - eapply control_tail_active_ambient; eassumption.
  - destruct continuation; cbn in *.
    all: first [eapply control_tail_result_ambient | eapply control_tail_active_ambient]; eassumption.
Qed.

Lemma control_tail_errno_primitive command before world returned after next observed :
  control_tail_active command before world ->
  gateway_runtime_operation backend gateway_errno_location_definition []
    before world returned after next observed ->
  control_tail_active command after next /\ io observed = None.
Proof.
  intros [current [CONTEXT TRANSPORT]] OPERATION.
  destruct (gateway_errno_location_operation _ _ _ _ _ _ runtime None before world returned after next observed
    (proj1 (proj1 CONTEXT)) OPERATION)
    as (object & offset & POINTER & GEOMETRY & VALUE & FOREIGN & MUTABLE & SIDE & ACCESS & FRAME & IO).
  split; [|exact IO]. exists current; split; [|exact TRANSPORT].
  eapply control_context_preserved; eassumption.
Qed.

Lemma control_tail_step command source world event target symbol :
  stream_member_layout ge _cancellation_sent 8 ->
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  control_tail_runtime command (gateway_live source world) ->
  gateway_step backend ge (gateway_live source world) event target ->
  control_tail_runtime command target /\
    gateway_received_event io (stream_descriptor initial) event = [].
Proof.
  intros LAYOUT SYMBOL FUNCTION READY STEP.
  inversion STEP; subst.
  - split; [eapply control_tail_internal_step; eassumption | reflexivity].
  - destruct READY as [[DEFINITION [ARGUMENTS CALLBACK]] CONTEXT]; subst.
    inversion DEFINITION; subst.
    destruct (control_tail_errno_primitive command _ _ _ _ _ _ CONTEXT
      ltac:(cbn [gateway_runtime_operation gateway_errno_location_definition]; eassumption)) as [ACTIVE IO].
    pose proof CALLBACK as CALLBACK_COPY.
    destruct CALLBACK as (destination & temporaries & rest & CONT & DESTINATION & STREAM & TAIL).
    subst continuation.
    split; [split; [cbn; right; exact CALLBACK_COPY | exact ACTIVE] |].
    unfold gateway_received_event; rewrite IO; reflexivity.
  - destruct READY as [[FN [ENV [STREAM [BODY CONT]]]] CONTEXT]; contradiction.
  - split; [eapply control_tail_ambient; eassumption | reflexivity].
  - split; [exact READY | reflexivity].
  - split; [exact I | reflexivity].
  - destruct READY as [[DEFINITION [ARGUMENTS CALLBACK]] CONTEXT]; subst.
    inversion DEFINITION; subst.
    destruct (control_tail_errno_primitive command _ _ _ _ _ _ CONTEXT
      ltac:(cbn [gateway_runtime_operation gateway_errno_location_definition]; eassumption)) as [ACTIVE IO].
    split; [exact I |]. unfold gateway_received_event; rewrite IO; reflexivity.
  - destruct READY as [[FN [ENV [STREAM [BODY CONT]]]] CONTEXT]; contradiction.
Qed.

Theorem actual_control_tail_prefix command source world events target symbol :
  stream_member_layout ge _cancellation_sent 8 ->
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  control_tail_runtime command (gateway_live source world) ->
  gateway_steps backend ge (gateway_live source world) events target ->
  control_tail_runtime command target /\ gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros LAYOUT SYMBOL FUNCTION READY RUN.
  remember (gateway_live source world) as first eqn:INITIAL.
  revert source world INITIAL READY.
  induction RUN; intros source world INITIAL READY; subst.
  - split; [exact READY | reflexivity].
  - destruct (control_tail_step command source world observed middle symbol LAYOUT SYMBOL FUNCTION READY H)
      as [NEXT EMPTY].
    destruct middle as [following current | memory current].
    + destruct (IHRUN following current eq_refl NEXT) as [FINAL REST].
      split; [exact FINAL |]. change (gateway_received_event io (stream_descriptor initial) observed ++
        gateway_received_bytes io (stream_descriptor initial) rest = []); rewrite EMPTY, REST; reflexivity.
    + destruct (gateway_dead_steps _ _ _ _ _ _ RUN) as [EMPTY_REST DEAD]; subst.
      split; [exact I |]. change (gateway_received_event io (stream_descriptor initial) observed ++ [] = []);
        rewrite EMPTY; reflexivity.
Qed.

End CancellationSuffix.
