(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source returns and moves transfer one owner without duplicating it. *)
From Stdlib Require Import List.
From compcert Require Import Maps Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayReferenceLedger GatewayReferencePlaces
  GatewayReferenceAccounting GatewayReferenceExecution.
Import ListNotations.

Definition gateway_reference_frame_select {World Event}:gateway_reference_selector World Event:=
  fun first event last status=>
  match event,first with
  |gateway_source _,gateway_live(Returnstate _ (Kcall(Some identifier)_ _ _ rest)_)_=>
    gateway_reference_move(gateway_reference_result(S(gateway_reference_depth rest)))
      (gateway_reference_temporary(gateway_reference_depth rest)identifier)
  |gateway_source _,gateway_live(State _ (Sset destination(Etempvar source _))continuation _ _ _)_
  |gateway_source _,gateway_live(State _ (Sset destination(Ecast(Etempvar source _) _))continuation _ _ _)_=>
    gateway_reference_move(gateway_reference_temporary(gateway_reference_depth continuation)source)
      (gateway_reference_temporary(gateway_reference_depth continuation)destination)
  |gateway_source _,gateway_live(State _ (Sreturn(Some(Etempvar source _)))continuation _ _ _)_
  |gateway_source _,gateway_live(State _ (Sreturn(Some(Ecast(Etempvar source _) _)))continuation _ _ _)_=>
    gateway_reference_move(gateway_reference_temporary(gateway_reference_depth continuation)source)
      (gateway_reference_result(gateway_reference_depth continuation))
  |gateway_source _,gateway_live(State _ Sskip _ _ _ _)_=>gateway_reference_keep
  |gateway_ambient,_|gateway_blocked,_|gateway_lost,_=>gateway_reference_keep
  |_,_=>gateway_reference_unclassified
  end.

Definition gateway_reference_temporary_expression(expression:Clight.expr):option AST.ident:=
  match expression with Etempvar identifier _|Ecast(Etempvar identifier _) _=>Some identifier|_=>None end.

Lemma gateway_reference_call_cont_depth continuation:
  gateway_reference_depth(call_cont continuation)=gateway_reference_depth continuation.
Proof. induction continuation;cbn;auto. Qed.

Theorem gateway_reference_returned_owner {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function destination environment temporaries continuation pointer memory world ledger ticket:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth continuation)))ticket pointer->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth continuation)destination)
    (gateway_reference_entries ledger)=None->
  exists next,
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(Returnstate pointer(Kcall(Some destination)function environment temporaries continuation)memory)world)
      (gateway_reference_valid ledger)[gateway_source E0]
      (gateway_live(State function Sskip continuation environment(PTree.set destination pointer temporaries)memory)world)
      (gateway_reference_valid next) /\gateway_reference_ledger_well_formed next /\
    gateway_reference_owns next(gateway_reference_temporary(gateway_reference_depth continuation)destination)ticket pointer /\
    gateway_reference_place_value ge
      (State function Sskip continuation environment(PTree.set destination pointer temporaries)memory)
      (gateway_reference_temporary(gateway_reference_depth continuation)destination)pointer /\
    (forall value,gateway_reference_count next value=gateway_reference_count ledger value).
Proof.
  intros FORMED OWNED VACANT.
  destruct(gateway_reference_move_selected ledger(gateway_reference_result(S(gateway_reference_depth continuation)))
    (gateway_reference_temporary(gateway_reference_depth continuation)destination)ticket pointer FORMED OWNED)
    as[next[MOVE[WELL[CAPTURED[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    apply(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER);exact OWNER.
  - exists next;split.
    + econstructor.
      * apply gateway_internal;[exact I|apply step_returnstate].
      * change(gateway_reference_execution backend ge gateway_reference_frame_select
          (gateway_live(State function Sskip continuation environment(PTree.set destination pointer temporaries)memory)world)
          (gateway_reference_apply(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth continuation)))
            (gateway_reference_temporary(gateway_reference_depth continuation)destination))(gateway_reference_valid ledger))[]
          (gateway_live(State function Sskip continuation environment(PTree.set destination pointer temporaries)memory)world)
          (gateway_reference_valid next)).
        rewrite MOVE;constructor.
    + split;[exact WELL|]. split;[exact CAPTURED|].
      split;[apply gateway_reference_temporary_binding,PTree.gss|exact COUNTS].
Qed.

Theorem gateway_reference_assigned_owner {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function destination source expression continuation environment temporaries pointer before world after ledger ticket:
  gateway_reference_temporary_expression expression=Some source->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth continuation)source)ticket pointer->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth continuation)destination)
    (gateway_reference_entries ledger)=None->
  gateway_step backend ge
    (gateway_live(State function(Sset destination expression)continuation environment temporaries before)world)
    (gateway_source E0)
    (gateway_live(State function Sskip continuation environment(PTree.set destination pointer temporaries)after)world)->
  exists next,
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(State function(Sset destination expression)continuation environment temporaries before)world)
      (gateway_reference_valid ledger)[gateway_source E0]
      (gateway_live(State function Sskip continuation environment(PTree.set destination pointer temporaries)after)world)
      (gateway_reference_valid next) /\gateway_reference_ledger_well_formed next /\
    gateway_reference_owns next(gateway_reference_temporary(gateway_reference_depth continuation)destination)ticket pointer /\
    gateway_reference_place_value ge
      (State function Sskip continuation environment(PTree.set destination pointer temporaries)after)
      (gateway_reference_temporary(gateway_reference_depth continuation)destination)pointer /\
    (forall value,gateway_reference_count next value=gateway_reference_count ledger value).
Proof.
  intros FORM FORMED OWNED VACANT SOURCE.
  destruct(gateway_reference_move_selected ledger(gateway_reference_temporary(gateway_reference_depth continuation)source)
    (gateway_reference_temporary(gateway_reference_depth continuation)destination)ticket pointer FORMED OWNED)
    as[next[MOVE[WELL[CAPTURED[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    apply(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER);exact OWNER.
  - assert(SELECT:@gateway_reference_frame_select World Event
      (gateway_live(State function(Sset destination expression)continuation environment temporaries before)world)
      (gateway_source E0)
      (gateway_live(State function Sskip continuation environment(PTree.set destination pointer temporaries)after)world)
      (gateway_reference_valid ledger)=gateway_reference_move
        (gateway_reference_temporary(gateway_reference_depth continuation)source)
        (gateway_reference_temporary(gateway_reference_depth continuation)destination)).
    { destruct expression;cbn[gateway_reference_temporary_expression]in FORM;try discriminate.
      - inversion FORM;subst;reflexivity.
      - match goal with nested:Clight.expr|-_=>destruct nested;
          cbn[gateway_reference_temporary_expression]in FORM;try discriminate end.
        inversion FORM;subst;reflexivity. }
    exists next;split.
    + econstructor;[exact SOURCE|]. rewrite SELECT,MOVE;constructor.
    + split;[exact WELL|]. split;[exact CAPTURED|].
      split;[apply gateway_reference_temporary_binding,PTree.gss|exact COUNTS].
Qed.
