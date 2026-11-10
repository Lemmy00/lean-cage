(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual errno expressions retain critical temporaries. *)
From Stdlib Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayBindings GatewayContexts GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayFramedRuntime GatewayReadonly GatewayRuntimeCuts GatewayMemoryPrefixes GatewayBoundaryValues GatewayPrimitiveCalls GatewayTransferMath GatewaySendRuntime.
Import ListNotations.

Definition gateway_errno_destination(protected:ident->bool)(destination:option ident):bool:=
  match destination with None=>true|Some identifier=>negb(protected identifier)end.
Definition gateway_errno_callee(expression:expr):bool:=
  match expression with Evar identifier ty=>
    Pos.eqb identifier ___errno_location&&
      if type_eq ty(Tfunction[](tptr tint)cc_default)then true else false
  |_=>false end.
Fixpoint gateway_errno_statement(protected:ident->bool)(body:statement):bool:=
  match body with
  |Sskip=>true
  |Sset identifier _=>negb(protected identifier)
  |Scall destination expression []=>gateway_errno_destination protected destination&&gateway_errno_callee expression
  |Ssequence first second|Sifthenelse _ first second=>gateway_errno_statement protected first&&gateway_errno_statement protected second
  |_=>false end.
Definition gateway_errno_temps(protected:ident->bool)(before after:temp_env):Prop:=
  forall identifier,protected identifier=true->after!identifier=before!identifier.
Definition gateway_errno_silent {Event}io(events:list(gateway_event Event)):Prop:=
  forall descriptor,gateway_received_bytes io descriptor events=[] /\gateway_sent_bytes io descriptor events=[].

Lemma gateway_errno_silent_append {Event}io(first second:list(gateway_event Event)):
  gateway_errno_silent io first->gateway_errno_silent io second->gateway_errno_silent io(first++second).
Proof.
  intros FIRST SECOND descriptor;destruct(FIRST descriptor)as[A B];destruct(SECOND descriptor)as[C D].
  split;[rewrite gateway_received_bytes_append,A,C|rewrite gateway_sent_bytes_append,B,D];reflexivity.
Qed.
Lemma gateway_errno_silent_quiet {Event}io(events:list(gateway_event Event)):
  Forall gateway_quiet_event events->gateway_errno_silent io events.
Proof. intros QUIET descriptor;split;[apply gateway_quiet_received_empty|apply gateway_quiet_sent_empty];exact QUIET. Qed.
Lemma gateway_errno_silent_pending {Event}io(events:list(gateway_event Event)):
  Forall gateway_pending_event events->gateway_errno_silent io events.
Proof. intros PENDING descriptor;split;[apply gateway_pending_received_empty|apply gateway_pending_sent_empty];exact PENDING. Qed.
Lemma gateway_errno_silent_ambient {Event}io(events:list(gateway_event Event)):
  Forall(fun event=>event=gateway_ambient)events->gateway_errno_silent io events.
Proof.
  intro AMBIENT;apply gateway_errno_silent_pending;eapply Forall_impl;[|exact AMBIENT];intros event SAME;left;exact SAME.
Qed.
Lemma gateway_errno_silent_source {Event}io:gateway_errno_silent(Event:=Event)io[gateway_source E0].
Proof. intros;split;reflexivity. Qed.
Lemma gateway_errno_callee_exact expression:
  gateway_errno_callee expression=true->expression=Evar ___errno_location(Tfunction[](tptr tint)cc_default).
Proof.
  destruct expression;cbn[gateway_errno_callee];try discriminate.
  rewrite andb_true_iff;intros[IDENTIFIER TYPE];apply Pos.eqb_eq in IDENTIFIER;subst.
  destruct(type_eq t(Tfunction[](tptr tint)cc_default));[subst;reflexivity|discriminate].
Qed.
Lemma gateway_errno_call_edge ge function destination environment temporaries memory continuation:
  environment!___errno_location=None->gateway_function_binding ge ___errno_location gateway_errno_location_definition->
  store_edge ge(State function(Scall destination(Evar ___errno_location(Tfunction[](tptr tint)cc_default))[])continuation environment temporaries memory)
    (Callstate gateway_errno_location_definition[](Kcall destination function environment temporaries continuation)memory).
Proof.
  intros LOCAL[symbol[SYMBOL FUNCTION]];eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Section Fragment.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(property:mem->World->Prop)
  (CLOSED:gateway_ambient_closed backend property).
Variable protected:ident->bool.
Variables(function:Clight.function)(environment:env).
Hypotheses(LOCAL:environment!___errno_location=None)
  (FUNCTION:gateway_function_binding ge ___errno_location gateway_errno_location_definition).
Hypothesis OPERATION:forall before world result after next observed,
  property before world->gateway_runtime_operation backend gateway_errno_location_definition[]
    before world result after next observed->property after next /\io observed=None.

Theorem gateway_actual_errno_fragment body:
  gateway_errno_statement protected body=true->
  forall continuation temporaries before world events value after next,
  property before world->
  gateway_steps backend ge(gateway_live(State function body continuation environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\gateway_errno_silent io prefix /\
    gateway_steps backend ge(gateway_live(State function body continuation environment temporaries before)world)prefix
      (gateway_live(State function Sskip continuation environment final_temps memory)current) /\
    property memory current /\gateway_errno_temps protected temporaries final_temps /\
    gateway_steps backend ge(gateway_live(State function Sskip continuation environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  induction body;cbn[gateway_errno_statement];try discriminate.
  - intros PROFILE continuation temporaries before world events value after next READY RUN.
    exists[],events,before,world,temporaries;split;[reflexivity|]. split;[intros;split;reflexivity|].
    split;[constructor|]. split;[exact READY|]. split;[intros identifier SELECTED;reflexivity|exact RUN].
  - intros PROFILE continuation temporaries before world events value after next READY RUN.
    destruct(gateway_boundary_set_cut backend ge property CLOSED function i e continuation environment temporaries before world events
      (Returnstate value Kstop after)next I READY RUN)
      as(pending&suffix&memory&current&assigned&EVENTS&AMBIENT&PENDING&EXPRESSION&CURRENT&SUFFIX).
    exists(pending++[gateway_source E0]),suffix,memory,current,(PTree.set i assigned temporaries).
    split;[rewrite EVENTS;rewrite<-app_assoc;reflexivity|]. split.
    + apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact AMBIENT|apply gateway_errno_silent_source].
    + split.
      * eapply gateway_steps_append;[exact PENDING|]. econstructor;[apply gateway_internal;[cbn;tauto|apply step_set;exact EXPRESSION]|constructor].
      * split;[exact CURRENT|]. split;[|exact SUFFIX].
        intros identifier SELECTED;apply PTree.gso;intro SAME;subst identifier.
        rewrite SELECTED in PROFILE;discriminate.
  - destruct l;try discriminate.
    rewrite andb_true_iff;intros[DESTINATION CALLEE]continuation temporaries before world events value after next READY RUN.
    apply gateway_errno_callee_exact in CALLEE;subst e.
    destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
      (State function(Scall o(Evar ___errno_location(Tfunction[](tptr tint)cc_default))[])continuation environment temporaries before)
      (Callstate gateway_errno_location_definition[](Kcall o function environment temporaries continuation)before)
      before world events value after next ltac:(cbn;tauto)
      ltac:(intros;apply gateway_errno_call_edge;assumption)READY RUN)
      as(p0&r0&c0&cw0&E0S&Q0&P0&C0&S0).
    cbn[gateway_replace_memory]in P0,S0.
    destruct(gateway_return_cut backend ge gateway_errno_location_definition[](Kcall o function environment temporaries continuation)
      c0 cw0 r0(Returnstate value Kstop after)next I ltac:(cbn;lia)S0)
      as(call&rest&returned&m1&w1&E1&CALL&REST).
    destruct(gateway_actual_primitive_context backend ge _ _ _ _ [] property(fun _=>property)CLOSED ltac:(intros;exact CLOSED)
      ltac:(intros api_before api_world api_result api_after api_next api_event INPUT API;
        exact(proj1(OPERATION api_before api_world api_result api_after api_next api_event INPUT API)))
      c0 cw0 call returned m1 w1 C0 CALL)
      as(wait&tail&api_memory&api_world&changed&changed_world&observed&EC&WAIT&WAIT_RUN&INPUT&API&POST&TAIL&FINAL).
    assert(SILENT_CALL:gateway_errno_silent io call).
    { destruct(OPERATION _ _ _ _ _ _ INPUT API)as[OUTPUT EMPTY].
      rewrite EC;apply gateway_errno_silent_append;[apply gateway_errno_silent_pending;exact WAIT|].
      apply gateway_errno_silent_append with(first:=[gateway_primitive observed]).
      - intros descriptor;split;unfold gateway_received_bytes,gateway_sent_bytes;
          cbn[flat_map gateway_received_event gateway_sent_event];rewrite EMPTY;reflexivity.
      - apply gateway_errno_silent_ambient;eapply gateway_terminal_return_ambient;exact TAIL. }
    destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
      (Returnstate returned(Kcall o function environment temporaries continuation)m1)
      (State function Sskip continuation environment(set_opttemp o returned temporaries)m1)
      m1 w1 rest value after next ltac:(cbn;tauto)
      ltac:(intros;apply unchanged_store_edge,edge_returnstate)FINAL REST)
      as(p2&suffix&memory&current&E2&Q2&P2&C2&SUFFIX).
    cbn[gateway_replace_memory]in P2,SUFFIX.
    exists(p0++gateway_source E0::call++p2++[gateway_source E0]),suffix,memory,current,(set_opttemp o returned temporaries).
    split;[rewrite E0S,E1,E2;repeat rewrite<-app_assoc;cbn[app];repeat rewrite<-app_assoc;reflexivity|]. split.
    + apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact Q0|].
      apply gateway_errno_silent_append with(first:=[gateway_source E0]);[apply gateway_errno_silent_source|].
      apply gateway_errno_silent_append;[exact SILENT_CALL|].
      apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact Q2|apply gateway_errno_silent_source].
    + split.
      * eapply gateway_steps_append;[exact P0|].
        econstructor;[apply gateway_internal;[cbn;tauto|eapply(proj1(proj2(gateway_errno_call_edge ge function o environment temporaries c0 continuation LOCAL FUNCTION)))]|].
        eapply gateway_steps_append;[exact(gateway_plug_steps backend ge _ _ _(Kcall o function environment temporaries continuation)I CALL)|].
        eapply gateway_steps_append;[exact P2|].
        econstructor;[apply gateway_internal;[cbn;tauto|constructor;reflexivity]|constructor].
      * split;[exact C2|]. split;[|exact SUFFIX].
        intros identifier SELECTED;destruct o as[assigned|];[|reflexivity]. cbn[set_opttemp].
        apply PTree.gso;intro SAME;subst identifier;cbn[gateway_errno_destination]in DESTINATION;rewrite SELECTED in DESTINATION;discriminate.
  - rewrite andb_true_iff;intros[FIRST SECOND]continuation temporaries before world events value after next READY RUN.
    destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
      (State function(Ssequence body1 body2)continuation environment temporaries before)
      (State function body1(Kseq body2 continuation)environment temporaries before)
      before world events value after next ltac:(cbn;tauto)
      ltac:(intros;apply unchanged_store_edge,edge_seq)READY RUN)
      as(p0&r0&c0&cw0&E0S&Q0&P0&C0&S0).
    cbn[gateway_replace_memory]in P0,S0.
    destruct(IHbody1 FIRST(Kseq body2 continuation)temporaries c0 cw0 r0 value after next C0 S0)
      as(p1&r1&m1&w1&temps1&E1&Q1&P1&C1&F1&S1).
    destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
      (State function Sskip(Kseq body2 continuation)environment temps1 m1)
      (State function body2 continuation environment temps1 m1)m1 w1 r1 value after next ltac:(cbn;tauto)
      ltac:(intros;apply unchanged_store_edge,edge_skip_seq)C1 S1)
      as(p2&r2&m2&w2&E2&Q2&P2&C2&S2).
    cbn[gateway_replace_memory]in P2,S2.
    destruct(IHbody2 SECOND continuation temps1 m2 w2 r2 value after next C2 S2)
      as(p3&suffix&memory&current&final_temps&E3&Q3&P3&FINAL&F3&SUFFIX).
    exists(p0++gateway_source E0::p1++p2++gateway_source E0::p3),suffix,memory,current,final_temps.
    split;[rewrite E0S,E1,E2,E3;repeat rewrite<-app_assoc;cbn[app];repeat rewrite<-app_assoc;reflexivity|]. split.
    + apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact Q0|].
      apply gateway_errno_silent_append with(first:=[gateway_source E0]);[apply gateway_errno_silent_source|].
      apply gateway_errno_silent_append;[exact Q1|].
      apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact Q2|].
      apply gateway_errno_silent_append with(first:=[gateway_source E0]);[apply gateway_errno_silent_source|exact Q3].
    + split.
      * eapply gateway_steps_append;[exact P0|].
        econstructor;[apply gateway_internal;[cbn;tauto|constructor]|].
        eapply gateway_steps_append;[exact P1|]. eapply gateway_steps_append;[exact P2|].
        econstructor;[apply gateway_internal;[cbn;tauto|constructor]|exact P3].
      * split;[exact FINAL|]. split;[|exact SUFFIX].
        intros identifier SELECTED;rewrite(F3 identifier SELECTED);apply F1;exact SELECTED.
  - rewrite andb_true_iff;intros[YES NO]continuation temporaries before world events value after next READY RUN.
    destruct(gateway_boundary_if_cut backend ge property CLOSED function e body1 body2 continuation environment temporaries
      before world events(Returnstate value Kstop after)next I READY RUN)
      as(pending&rest&called&called_world&observed&branch&EVENTS&AMBIENT&PENDING&EXPRESSION&BOOLEAN&CALLED&REST).
    assert(CHOSEN:gateway_errno_statement protected(if branch then body1 else body2)=true)by(destruct branch;assumption).
    assert(CHILD:forall continuation temporaries before world events value after next,
      property before world->
      gateway_steps backend ge(gateway_live(State function(if branch then body1 else body2)continuation environment temporaries before)world)events
        (gateway_live(Returnstate value Kstop after)next)->
      exists prefix suffix memory current final_temps,
        events=prefix++suffix /\gateway_errno_silent io prefix /\
        gateway_steps backend ge(gateway_live(State function(if branch then body1 else body2)continuation environment temporaries before)world)prefix
          (gateway_live(State function Sskip continuation environment final_temps memory)current) /\
        property memory current /\gateway_errno_temps protected temporaries final_temps /\
        gateway_steps backend ge(gateway_live(State function Sskip continuation environment final_temps memory)current)suffix
          (gateway_live(Returnstate value Kstop after)next)).
    { destruct branch;[apply IHbody1;exact YES|apply IHbody2;exact NO]. }
    destruct(CHILD continuation temporaries called called_world rest value after next CALLED REST)
      as(prefix&suffix&memory&current&final_temps&TAIL&SILENT&PREFIX&FINAL&FRAME&SUFFIX).
    exists(pending++gateway_source E0::prefix),suffix,memory,current,final_temps.
    split;[rewrite EVENTS,TAIL;repeat rewrite<-app_assoc;reflexivity|]. split.
    + apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact AMBIENT|].
      apply gateway_errno_silent_append with(first:=[gateway_source E0]);[apply gateway_errno_silent_source|exact SILENT].
    + split.
      * eapply gateway_steps_append;[exact PENDING|].
        econstructor;[apply gateway_internal;[cbn;tauto|eapply step_ifthenelse;[exact EXPRESSION|exact BOOLEAN]]|exact PREFIX].
      * split;[exact FINAL|]. split;assumption.
Qed.
End Fragment.
