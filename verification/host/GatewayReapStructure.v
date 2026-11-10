(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Every reaper call and source store has an exact native role. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayReapAllocation GatewayReapABI
  GatewayExchangeABI GatewayRuntimeABI GatewayPrefix.
Import ListNotations.

Inductive gateway_reap_site:=reap_site_clock|reap_site_signal|reap_site_wait_nonblock|reap_site_wait_block|
  reap_site_pause|reap_site_errno.

Definition reap_site_identifier site:ident:=match site with
  |reap_site_clock=>_host_now|reap_site_signal=>_kill|reap_site_wait_nonblock|reap_site_wait_block=>_waitpid
  |reap_site_pause=>_nanosleep|reap_site_errno=>___errno_location end.
Definition reap_site_definition site:Ctypes.fundef Clight.function:=match site with
  |reap_site_clock=>Internal f_host_now|reap_site_signal=>gateway_kill_definition
  |reap_site_wait_nonblock|reap_site_wait_block=>gateway_waitpid_definition
  |reap_site_pause=>gateway_nanosleep_definition|reap_site_errno=>gateway_errno_location_definition end.
Definition reap_site_expression site:expr:=match site with
  |reap_site_clock=>Evar _host_now(Tfunction[]tdouble cc_default)
  |reap_site_signal=>Evar _kill(Tfunction[tint;tint]tint cc_default)
  |reap_site_wait_nonblock|reap_site_wait_block=>Evar _waitpid(Tfunction[tint;tptr tint;tint]tint cc_default)
  |reap_site_pause=>Evar _nanosleep(Tfunction[tptr(Tstruct _timespec noattr);tptr(Tstruct _timespec noattr)]tint cc_default)
  |reap_site_errno=>Evar ___errno_location(Tfunction[](tptr tint)cc_default)end.
Definition reap_site_arguments site:list expr:=match site with
  |reap_site_clock|reap_site_errno=>[]
  |reap_site_signal=>[Eunop Oneg(Etempvar _child tint)tint;Econst_int(Int.repr 9)tint]
  |reap_site_wait_nonblock=>[Etempvar _child tint;Eaddrof(Evar _status tint)(tptr tint);Econst_int Int.one tint]
  |reap_site_wait_block=>[Etempvar _child tint;Eaddrof(Evar _status tint)(tptr tint);Econst_int Int.zero tint]
  |reap_site_pause=>[Eaddrof(Evar _pause(Tstruct _timespec noattr))(tptr(Tstruct _timespec noattr));
      Ecast(Econst_int Int.zero tint)(tptr tvoid)]end.
Definition reap_site_values slots child site:list val:=match site with
  |reap_site_clock|reap_site_errno=>[]
  |reap_site_signal=>[Vint(Int.neg child);Vint(Int.repr 9)]
  |reap_site_wait_nonblock=>[Vint child;Vptr(reap_status_slot slots)Ptrofs.zero;Vint Int.one]
  |reap_site_wait_block=>[Vint child;Vptr(reap_status_slot slots)Ptrofs.zero;Vint Int.zero]
  |reap_site_pause=>[Vptr(reap_pause_slot slots)Ptrofs.zero;Vnullptr]end.

Definition reap_pause_location(location:expr):Prop:=
  location=Efield(Evar _pause(Tstruct _timespec noattr))_tv_sec tlong \/
  location=Efield(Evar _pause(Tstruct _timespec noattr))_tv_nsec tlong.

Fixpoint gateway_reap_statement(body:statement):Prop:=match body with
  |Sskip|Sbreak|Scontinue|Sreturn None=>True
  |Sset identifier _=>identifier<>_child
  |Sassign location _=>reap_pause_location location
  |Scall destination function arguments=>destination<>Some _child /\exists site,
      function=reap_site_expression site /\arguments=reap_site_arguments site
  |Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
      gateway_reap_statement first /\gateway_reap_statement rest
  |_=>False end.

Fixpoint gateway_reap_cont(continuation:cont):Prop:=match continuation with
  |Kstop=>True
  |Kseq body rest=>gateway_reap_statement body /\gateway_reap_cont rest
  |Kloop1 first second rest|Kloop2 first second rest=>
      gateway_reap_statement first /\gateway_reap_statement second /\gateway_reap_cont rest
  |_=>False end.

Definition gateway_reap_call_frame slots child(continuation:cont):Prop:=exists destination temporaries rest,
  continuation=Kcall destination f_host_engine_reap(reap_environment slots)temporaries rest /\
    destination<>Some _child /\temporaries!_child=Some(Vint child) /\gateway_reap_cont rest.

Definition gateway_reap_source slots child(source:Clight.state):Prop:=match source with
  |State function body continuation environment temporaries _=>
      function=f_host_engine_reap /\environment=reap_environment slots /\temporaries!_child=Some(Vint child) /\
      gateway_reap_statement body /\gateway_reap_cont continuation
  |Callstate definition arguments continuation _=>
      (exists site,definition=reap_site_definition site /\arguments=reap_site_values slots child site) /\
      gateway_reap_call_frame slots child continuation
  |Returnstate _ continuation _=>continuation=Kstop\/gateway_reap_call_frame slots child continuation end.

Definition gateway_reap_source_instruction(source:Clight.state):Prop:=
  match source with Callstate _ _ _ _=>False|_=>True end.

Lemma actual_reap_statement_profile:gateway_reap_statement(fn_body f_host_engine_reap).
Proof.
  cbn[gateway_reap_statement fn_body].
  repeat split;try discriminate;try exact I.
  all:try solve[left;reflexivity|right;reflexivity].
  all:first[solve[exists reap_site_clock;split;reflexivity]|solve[exists reap_site_signal;split;reflexivity]|
    solve[exists reap_site_wait_nonblock;split;reflexivity]|solve[exists reap_site_wait_block;split;reflexivity]|
    solve[exists reap_site_pause;split;reflexivity]|solve[exists reap_site_errno;split;reflexivity]].
Qed.

Lemma gateway_reap_cont_call_cont continuation:
  gateway_reap_cont continuation->call_cont continuation=Kstop.
Proof. induction continuation;cbn;intuition. Qed.

Lemma gateway_reap_source_replace slots child source memory:
  gateway_reap_source slots child source->gateway_reap_source slots child(gateway_replace_memory source memory).
Proof. destruct source;cbn;tauto. Qed.

Lemma gateway_reap_site_binding site:
  gateway_function_binding(Clight.globalenv prog)(reap_site_identifier site)(reap_site_definition site).
Proof. destruct site;apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Lemma gateway_reap_site_arguments ge slots child site temporaries memory:
  temporaries!_child=Some(Vint child)->
  argument_values ge(reap_environment slots)temporaries memory(reap_site_arguments site)
    (match site with reap_site_clock|reap_site_errno=>[]|reap_site_signal=>[tint;tint]|
      reap_site_wait_nonblock|reap_site_wait_block=>[tint;tptr tint;tint]|
      reap_site_pause=>[tptr(Tstruct _timespec noattr);tptr(Tstruct _timespec noattr)]end)
    (reap_site_values slots child site).
Proof.
  intro CHILD;destruct site;cbn[reap_site_arguments reap_site_values].
  - apply no_argument_values.
  - eapply cons_argument_values with(v:=Vint(Int.neg child)).
    + apply old_expression_value;eapply value_unary;[apply value_temp;exact CHILD|reflexivity].
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint(Int.repr 9));
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - eapply cons_argument_values with(v:=Vint child);[apply old_expression_value,value_temp;exact CHILD|reflexivity|].
    eapply cons_argument_values with(v:=Vptr(reap_status_slot slots)Ptrofs.zero).
    + apply local_address_expression;unfold reap_environment;rewrite PTree.gso by discriminate;apply PTree.gss.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint Int.one);
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - eapply cons_argument_values with(v:=Vint child);[apply old_expression_value,value_temp;exact CHILD|reflexivity|].
    eapply cons_argument_values with(v:=Vptr(reap_status_slot slots)Ptrofs.zero).
    + apply local_address_expression;unfold reap_environment;rewrite PTree.gso by discriminate;apply PTree.gss.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint Int.zero);
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - eapply cons_argument_values with(v:=Vptr(reap_pause_slot slots)Ptrofs.zero).
    + apply local_address_expression;apply PTree.gss.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vnullptr);
        [apply old_expression_value;eapply value_cast;[constructor|reflexivity]|reflexivity|apply no_argument_values].
  - apply no_argument_values.
Qed.

Lemma gateway_reap_site_call ge slots child site destination continuation temporaries memory:
  gateway_function_binding ge(reap_site_identifier site)(reap_site_definition site)->
  temporaries!_child=Some(Vint child)->
  store_edge ge
    (State f_host_engine_reap(Scall destination(reap_site_expression site)(reap_site_arguments site))continuation
      (reap_environment slots)temporaries memory)
    (Callstate(reap_site_definition site)(reap_site_values slots child site)
      (Kcall destination f_host_engine_reap(reap_environment slots)temporaries continuation)memory).
Proof.
  intros[symbol[SYMBOL FUNCTION]]CHILD.
  pose proof(gateway_reap_site_arguments ge slots child site temporaries memory CHILD)as ARGUMENTS.
  assert(LOCAL:(reap_environment slots)!(reap_site_identifier site)=None)by(destruct site;reflexivity).
  destruct site;cbn[reap_site_expression reap_site_definition reap_site_identifier reap_site_values].
  all:eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero);
    [reflexivity|apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity]|
      exact ARGUMENTS|cbn;exact FUNCTION|reflexivity].
Qed.

Theorem gateway_reap_source_internal slots child source trace after:
  gateway_reap_source slots child source->gateway_reap_source_instruction source->~gateway_at_primitive source->
  step2(Clight.globalenv prog)source trace after->gateway_reap_source slots child after.
Proof.
  destruct source as[function body continuation environment temporaries memory|
    definition arguments continuation memory|returned continuation memory];intros PROFILE SOURCE INTERNAL STEP.
  - destruct PROFILE as[FUNCTION[ENV[CHILD[BODY CONT]]]];subst function environment.
    inversion STEP;subst;cbn[gateway_reap_statement]in BODY;try contradiction.
    all:cbn[gateway_reap_cont]in CONT.
    all:cbn[gateway_reap_source gateway_reap_statement gateway_reap_cont].
    all:try solve[intuition discriminate].
    all:try solve[rewrite(gateway_reap_cont_call_cont continuation CONT);left;reflexivity].
    all:try solve[destruct b;intuition discriminate].
    all:try solve[match goal with SAME:_=Sskip\/_=Scontinue|-_=>destruct SAME;subst;cbn in BODY;intuition end].
    all:try solve[match goal with SAME:_=Sskip\/_=Sbreak|-_=>destruct SAME;subst;cbn in BODY;intuition end].
    all:try solve[match goal with CALL:is_call_cont ?kont|-_=>destruct kont;cbn in CONT,CALL;intuition discriminate end].
    + repeat split;try reflexivity;try assumption.
      rewrite PTree.gso;[exact CHILD|congruence].
    + destruct BODY as[DESTINATION[site[FUNCTION ARGUMENTS]]];subst.
      destruct(gateway_reap_site_call(Clight.globalenv prog)slots child site optid continuation temporaries memory
        (gateway_reap_site_binding site)CHILD)as[_[_ UNIQUE]].
      match goal with REAL:step2 _ (State _ (Scall _ _ _) _ _ _ _)_ _|-_=>
        destruct(UNIQUE _ _ REAL)as[TRACE SAME];inversion SAME;subst end.
      split;[exists site;split;reflexivity|]. exists optid,temporaries,continuation;repeat split;try reflexivity;assumption.
  - contradiction.
  - destruct PROFILE as[STOP|[destination[temporaries[rest[FRAME[DESTINATION[CHILD CONT]]]]]]];subst continuation.
    + inversion STEP.
    + inversion STEP;subst;cbn[gateway_reap_source gateway_reap_statement].
      repeat split;try reflexivity;try exact I;try assumption.
      destruct destination as[identifier|];cbn;[rewrite PTree.gso;[exact CHILD|congruence]|exact CHILD].
Qed.
