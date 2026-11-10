(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Every actual poll initialization store targets its owned local. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadySource GatewayPollLayout
  GatewayReadyContext GatewayReadyMemory GatewayInstructions GatewayOperations GatewayCalls
  GatewayReadContext GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Lemma actual_poll_store_effect (ge : Clight.genv) item temporaries before member ty delta chunk expression
    continuation trace target :
  poll_member_layout ge member delta -> access_mode ty = By_value chunk ->
  step2 ge
    (State f_host_ready (Sassign (poll_member member ty) expression) continuation
      (ready_environment item) temporaries before) trace target ->
  exists value after,
    trace = E0 /\ target = State f_host_ready Sskip continuation (ready_environment item) temporaries after /\
    Mem.store chunk before item (Ptrofs.unsigned (Ptrofs.repr delta)) value = Some after.
Proof.
  intros LAYOUT ACCESS STEP; inversion STEP; subst;
    try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  match goal with LOCATION : eval_lvalue _ _ _ _ (poll_member member ty) _ _ _ |- _ =>
    destruct (proj2 (actual_poll_member_location ge item temporaries before member ty delta LAYOUT)
      _ _ _ LOCATION) as [OBJECT [OFFSET BITS]]; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst end;
    cbn [poll_member typeof Mem.storev] in *.
  - assert (chunk0 = chunk) by congruence; subst chunk0.
    match goal with STORE : (if ?condition then _ else None) = Some _ |- _ =>
      destruct condition in STORE; [|discriminate] end.
    eexists; eexists; split; [reflexivity |]. split; [reflexivity |].
    eassumption.
  - congruence.
Qed.

Section PollStore.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition slice := gateway_ready_slice native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Theorem actual_poll_store_retained item mode current member ty delta chunk expression continuation temporaries
    before world events returned after next :
  poll_member_layout ge member delta -> access_mode ty = By_value chunk ->
  slice item mode current before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready (Sassign (poll_member member ty) expression) continuation
      (ready_environment item) temporaries before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix memory changed called_world value,
    events = prefix ++ gateway_source E0 :: suffix /\
    Forall (fun event => event = gateway_ambient) prefix /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready (Sassign (poll_member member ty) expression) continuation
        (ready_environment item) temporaries before) world) prefix
      (gateway_live (State f_host_ready (Sassign (poll_member member ty) expression) continuation
        (ready_environment item) temporaries memory) called_world) /\
    step2 ge (State f_host_ready (Sassign (poll_member member ty) expression) continuation
      (ready_environment item) temporaries memory) E0
      (State f_host_ready Sskip continuation (ready_environment item) temporaries changed) /\
    Mem.store chunk memory item (Ptrofs.unsigned (Ptrofs.repr delta)) value = Some changed /\
    slice item mode current changed called_world /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready Sskip continuation (ready_environment item) temporaries changed) called_world)
      suffix (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros LAYOUT ACCESS READY RUN.
  destruct (gateway_source_instruction_occurrence backend ge f_host_ready
    (Sassign (poll_member member ty) expression) continuation (ready_environment item) temporaries before world
    events returned after next ltac:(cbn; tauto) RUN)
    as (prefix & suffix & memory & called_world & trace & target & EVENTS & AMBIENT & PREFIX & REAL & SUFFIX).
  assert (CALLED : slice item mode current memory called_world).
  { eapply gateway_ambient_run_ready with
      (source := State f_host_ready (Sassign (poll_member member ty) expression) continuation
        (ready_environment item) temporaries before).
    - apply gateway_ready_slice_ambient with (io := io) (thread_errno := thread_errno); exact runtime.
    - exact READY.
    - exact AMBIENT.
    - exact PREFIX. }
  destruct (actual_poll_store_effect ge item temporaries memory member ty delta chunk expression continuation trace target
    LAYOUT ACCESS REAL) as (value & changed & TRACE & TARGET & STORE); subst trace target.
  exists prefix, suffix, memory, changed, called_world, value.
  split; [exact EVENTS |]. split; [exact AMBIENT |]. split; [exact PREFIX |].
  split; [exact REAL |]. split; [exact STORE |].
  split; [|exact SUFFIX].
  eapply gateway_ready_local_store; [exact runtime | exact CALLED | exact STORE].
Qed.

End PollStore.
