(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual return edges transfer the selected source reference. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Events Ctypes Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayCallPath GatewayOperations GatewayReturns GatewayReturnIdentity GatewayRuntimeCuts
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceExecution
  GatewayReferenceFrames GatewayReferenceMoves.
Import ListNotations.

Lemma gateway_reference_ambient_execution {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    first events last ledger:
  gateway_steps backend ge first events last->Forall(fun event=>event=gateway_ambient)events->
  gateway_reference_execution backend ge gateway_reference_frame_select first ledger events last ledger.
Proof.
  intro RUN;induction RUN;intro AMBIENT;[constructor|].
  inversion AMBIENT;subst observed.
  econstructor;[exact H|].
  change(gateway_reference_execution backend ge gateway_reference_frame_select middle
    (gateway_reference_apply gateway_reference_keep ledger)rest last ledger).
  destruct ledger;cbn;apply IHRUN;assumption.
Qed.

Lemma gateway_reference_after_final_return {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    value before world events actual after next:
  gateway_steps backend ge(gateway_live(Returnstate value Kstop before)world)events
    (gateway_live(Returnstate actual Kstop after)next)->
  actual=value /\Forall(fun event=>event=gateway_ambient)events.
Proof.
  revert before world;induction events as[|event rest IH];intros before world RUN.
  - inversion RUN;split;[reflexivity|constructor].
  - inversion RUN;subst.
    match goal with STEP:gateway_step _ _ _ _ _|-_=>inversion STEP;subst end;cbn in *;try contradiction.
    + match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
    + destruct(IH _ _ ltac:(eassumption))as[SAME QUIET];split;[exact SAME|constructor;[reflexivity|exact QUIET]].
    + match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
        destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

Theorem gateway_reference_actual_source_return {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function expression identifier continuation environment temporaries pointer before world events actual after next ledger ticket:
  call_cont continuation=Kstop->gateway_reference_temporary_expression expression=Some identifier->
  (forall memory,expression_value ge environment temporaries memory expression pointer)->
  (forall memory converted,sem_cast pointer(typeof expression)(fn_return function)memory=Some converted->converted=pointer)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth continuation)identifier)ticket pointer->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth continuation))
    (gateway_reference_entries ledger)=None->
  gateway_steps backend ge(gateway_live(State function(Sreturn(Some expression))continuation environment temporaries before)world)
    events(gateway_live(Returnstate actual Kstop after)next)->
  exists final,
    actual=pointer /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(State function(Sreturn(Some expression))continuation environment temporaries before)world)
      (gateway_reference_valid ledger)events(gateway_live(Returnstate actual Kstop after)next)
      (gateway_reference_valid final) /\
    gateway_reference_apply(gateway_reference_move
      (gateway_reference_temporary(gateway_reference_depth continuation)identifier)
      (gateway_reference_result(gateway_reference_depth continuation)))(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth continuation))ticket pointer /\
    (forall value,gateway_reference_count final value=gateway_reference_count ledger value).
Proof.
  intros STOP FORM EXPRESSION CAST FORMED OWNED VACANT.
  destruct(gateway_reference_move_selected ledger(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    (gateway_reference_result(gateway_reference_depth continuation))ticket pointer FORMED OWNED)
    as[final[MOVE[WELL[CAPTURED[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    exact(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER OWNER).
  - revert before world;induction events as[|observed rest IH];intros before world RUN.
    + inversion RUN.
    + inversion RUN as[|first event middle remaining last HEAD TAIL];subst.
      assert(INTERNAL:~gateway_at_primitive(State function(Sreturn(Some expression))continuation environment temporaries before))
        by(cbn;tauto).
      destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
        as[[trace[target[EVENT[REAL TARGET]]]]|[[changed[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
      * inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
        match goal with VALUE:eval_expr _ _ _ _ expression ?value|-_=>
          pose proof(proj2(EXPRESSION before)_ VALUE)as SAME;subst value end.
        match goal with CONVERSION:sem_cast pointer _ _ _=Some ?converted|-_=>
          pose proof(CAST _ _ CONVERSION)as SAME;subst converted end.
        rewrite STOP in *.
        destruct(gateway_reference_after_final_return backend ge _ _ _ _ _ _ _ TAIL)as[ACTUAL QUIET].
        subst actual;exists final;split;[reflexivity|]. split.
        -- econstructor;[exact HEAD|].
           assert(SELECT:@gateway_reference_frame_select World Event
             (gateway_live(State function(Sreturn(Some expression))continuation environment temporaries before)world)
             (gateway_source E0)(gateway_live(Returnstate pointer Kstop m')world)(gateway_reference_valid ledger)=
             gateway_reference_move(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
               (gateway_reference_result(gateway_reference_depth continuation))).
           { destruct expression;cbn[gateway_reference_temporary_expression]in FORM;try discriminate.
             - inversion FORM;subst;reflexivity.
             - match goal with nested:Clight.expr|-_=>destruct nested;
                 cbn[gateway_reference_temporary_expression]in FORM;try discriminate end.
               inversion FORM;subst;reflexivity. }
           rewrite SELECT,MOVE;eapply gateway_reference_ambient_execution;[exact TAIL|exact QUIET].
        -- split;[exact MOVE|]. split;[exact WELL|]. split;assumption.
      * destruct(IH changed current TAIL)as[following[SAME[EXECUTION[APPLY[VALID[RESULT COUNT]]]]]].
        exists following;split;[exact SAME|]. split;[|exact(conj APPLY(conj VALID(conj RESULT COUNT)))].
        econstructor;[exact HEAD|exact EXECUTION].
      * destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

Theorem gateway_reference_actual_caller_result {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function destination environment temporaries expression following pointer before world events actual after next ledger ticket:
  call_cont following=Kstop->gateway_reference_temporary_expression expression=Some destination->
  (forall memory,expression_value ge environment(PTree.set destination pointer temporaries)memory expression pointer)->
  (forall memory converted,sem_cast pointer(typeof expression)(fn_return function)memory=Some converted->converted=pointer)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth following)))ticket pointer->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth following)destination)
    (gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth following))
    (gateway_reference_entries ledger)=None->
  gateway_steps backend ge
    (gateway_live(Returnstate pointer(Kcall(Some destination)function environment temporaries
      (Kseq(Sreturn(Some expression))following))before)world)events
    (gateway_live(Returnstate actual Kstop after)next)->
  exists intermediate final,
    actual=pointer /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_live(Returnstate pointer(Kcall(Some destination)function environment temporaries
        (Kseq(Sreturn(Some expression))following))before)world)(gateway_reference_valid ledger)events
      (gateway_live(Returnstate actual Kstop after)next)(gateway_reference_valid final) /\
    gateway_reference_apply(gateway_reference_move
      (gateway_reference_result(S(gateway_reference_depth following)))
      (gateway_reference_temporary(gateway_reference_depth following)destination))(gateway_reference_valid ledger)=
      gateway_reference_valid intermediate /\
    gateway_reference_apply(gateway_reference_move
      (gateway_reference_temporary(gateway_reference_depth following)destination)
      (gateway_reference_result(gateway_reference_depth following)))(gateway_reference_valid intermediate)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth following))ticket pointer /\
    (forall value,gateway_reference_count final value=gateway_reference_count ledger value).
Proof.
  intros STOP FORM EXPRESSION CAST FORMED OWNED TEMP_FREE RESULT_FREE RUN.
  assert(CLOSED:gateway_runtime_discipline backend(fun _ _=>True))
    by(unfold gateway_runtime_discipline;intros;exact I).
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (Returnstate pointer(Kcall(Some destination)function environment temporaries(Kseq(Sreturn(Some expression))following))before)
    (State function Sskip(Kseq(Sreturn(Some expression))following)environment(PTree.set destination pointer temporaries)before)
    before world events actual after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)I RUN)
    as(prefix &rest &called &current &EVENTS &AMBIENT &PREFIX &GOOD &REST).
  destruct(gateway_reference_move_selected ledger(gateway_reference_result(S(gateway_reference_depth following)))
    (gateway_reference_temporary(gateway_reference_depth following)destination)ticket pointer FORMED OWNED)
    as[intermediate[MOVE[WELL[CAPTURED[RETAINED COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    exact(proj1(gateway_reference_take_none _ _)TEMP_FREE entry MEMBER OWNER).
  - assert(RESULT_VACANT:gateway_reference_take(gateway_reference_result(gateway_reference_depth following))
      (gateway_reference_entries intermediate)=None).
    { eapply(gateway_reference_move_keeps_vacant ledger
        (gateway_reference_result(S(gateway_reference_depth following)))
        (gateway_reference_temporary(gateway_reference_depth following)destination)
        (gateway_reference_result(gateway_reference_depth following))intermediate);
        [exact RESULT_FREE|discriminate|exact MOVE]. }
    destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
      (State function Sskip(Kseq(Sreturn(Some expression))following)environment(PTree.set destination pointer temporaries)called)
      (State function(Sreturn(Some expression))following environment(PTree.set destination pointer temporaries)called)
      called current rest actual after next ltac:(cbn;tauto)
      ltac:(intros;apply unchanged_store_edge,edge_skip_seq)I REST)
      as(pending &suffix &return_memory &return_world &REST_EVENTS &WAITING &TO_RETURN &RETURN_READY &FROM_RETURN).
    destruct(gateway_reference_actual_source_return backend ge function expression destination following environment
      (PTree.set destination pointer temporaries)pointer return_memory return_world suffix actual after next
      intermediate ticket STOP FORM EXPRESSION CAST WELL CAPTURED RESULT_VACANT FROM_RETURN)
      as[final[SAME[RETURN[FINAL_MOVE[VALID[RESULT FINAL_COUNTS]]]]]].
    exists intermediate,final;split;[exact SAME|]. split.
    + rewrite EVENTS.
      eapply gateway_reference_execution_append with(prefix:=prefix)
        (middle:=gateway_live(Returnstate pointer(Kcall(Some destination)function environment temporaries
          (Kseq(Sreturn(Some expression))following))called)current)(intermediate:=gateway_reference_valid ledger).
      * eapply gateway_reference_ambient_execution;[exact PREFIX|exact AMBIENT].
      * econstructor.
        -- apply gateway_internal;[exact I|apply step_returnstate].
        -- change(gateway_reference_execution backend ge gateway_reference_frame_select
             (gateway_live(State function Sskip(Kseq(Sreturn(Some expression))following)environment
               (PTree.set destination pointer temporaries)called)current)
             (gateway_reference_apply(gateway_reference_move
               (gateway_reference_result(S(gateway_reference_depth following)))
               (gateway_reference_temporary(gateway_reference_depth following)destination))
               (gateway_reference_valid ledger))rest
             (gateway_live(Returnstate actual Kstop after)next)(gateway_reference_valid final)).
           rewrite MOVE,REST_EVENTS.
           eapply gateway_reference_execution_append with(prefix:=pending)
             (middle:=gateway_live(State function Sskip(Kseq(Sreturn(Some expression))following)environment
               (PTree.set destination pointer temporaries)return_memory)return_world)
             (intermediate:=gateway_reference_valid intermediate).
           ++ eapply gateway_reference_ambient_execution;[exact TO_RETURN|exact WAITING].
           ++ econstructor;[apply gateway_internal;[exact I|apply step_skip_seq]|exact RETURN].
    + split;[exact MOVE|]. split;[exact FINAL_MOVE|]. split;[exact VALID|]. split;[exact RESULT|].
      intro value;rewrite FINAL_COUNTS,COUNTS;reflexivity.
Qed.
