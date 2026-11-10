(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful original Outcome call reaches its same private-copy operation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMandatoryCut GatewayOutcomeConstruction GatewayOutcomeCopySource
  GatewayOutcomeEntry GatewayFunctionEntry GatewaySourcePaths GatewaySourceCuts GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_copy_statement:=Scall(Some _t'20)
  (Evar _PyDict_Copy(Tfunction[tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default))
  [Etempvar _data(tptr(Tstruct __object noattr))].
Definition gateway_outcome_copy_tail:=Kseq(Sset _copy(Etempvar _t'20(tptr(Tstruct __object noattr))))
  (Kseq gateway_outcome_after_copy Kstop).

Ltac gateway_outcome_validation_marker:=
  first[solve[left;split;reflexivity]|
    lazymatch goal with
    | |-gateway_mandatory_body ?protected ?marker ?tail ?body ?continuation=>
      let actual:=eval hnf in body in lazymatch actual with
      |Ssequence ?first ?second=>
        change(gateway_mandatory_body protected marker tail actual continuation);
        first[right;right;split;[reflexivity|gateway_outcome_validation_marker]|
              right;left;gateway_outcome_validation_marker]
      end
    end].

Theorem gateway_outcome_validation_profile:
  gateway_mandatory_body _data gateway_outcome_copy_statement gateway_outcome_copy_tail(fn_body f_host_outcome_from)Kstop.
Proof. gateway_outcome_validation_marker. Qed.

Theorem gateway_outcome_body_reaches_copy {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters data_block data_offset before world events value after next symbol definition:
  parameters!_data=Some(Vptr data_block data_offset)->environment!_PyDict_Copy=None->
  Genv.find_symbol ge _PyDict_Copy=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default->
  gateway_steps backend ge
    (gateway_live(State f_host_outcome_from(fn_body f_host_outcome_from)Kstop environment parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists prefix suffix selected memory current,
    events=prefix++suffix /\selected!_data=Some(Vptr data_block data_offset) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from(fn_body f_host_outcome_from)Kstop environment parameters before)world)prefix
      (gateway_live(Callstate definition[Vptr data_block data_offset](gateway_outcome_copy_cont environment selected)memory)current) /\
    gateway_steps backend ge
      (gateway_live(Callstate definition[Vptr data_block data_offset](gateway_outcome_copy_cont environment selected)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros DATA LOCAL SYMBOL FUNCTION TYPE RUN NONNULL.
  assert(GOOD:gateway_mandatory_source f_host_outcome_from environment _data(Vptr data_block data_offset)
    gateway_outcome_copy_statement gateway_outcome_copy_tail
    (State f_host_outcome_from(fn_body f_host_outcome_from)Kstop environment parameters before)).
  { left;split;[reflexivity|]. split;[reflexivity|]. split;[exact DATA|]. split;[reflexivity|].
    left;exact gateway_outcome_validation_profile. }
  destruct(gateway_mandatory_actual_cut backend ge f_host_outcome_from environment _data(Vptr data_block data_offset)
    gateway_outcome_copy_statement gateway_outcome_copy_tail
    (State f_host_outcome_from(fn_body f_host_outcome_from)Kstop environment parameters before)world events value after next
    ltac:(repeat eexists)eq_refl GOOD RUN NONNULL)
    as(prelude &rest &selected &memory &current &EVENTS &SELECTED &PREFIX &REST).
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(PATH:gateway_source_path backend ge definition[Vptr data_block data_offset]
    (gateway_outcome_copy_cont environment selected)(fun _ _=>True)
    (State f_host_outcome_from gateway_outcome_copy_statement gateway_outcome_copy_tail environment selected memory)(fun _ _=>True)).
  { eapply gateway_source_same with(target:=Callstate definition[Vptr data_block data_offset]
      (gateway_outcome_copy_cont environment selected)memory).
    - exact CLOSED.
    - cbn;tauto.
    - intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      + reflexivity.
      + apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
      + apply cons_argument_values with(v:=Vptr data_block data_offset);
          [apply old_expression_value,value_temp;exact SELECTED|reflexivity|apply no_argument_values].
      + change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      + exact TYPE.
    - apply gateway_source_reached;auto. }
  destruct(gateway_source_path_cut backend ge definition[Vptr data_block data_offset](gateway_outcome_copy_cont environment selected)
    _ _ _ PATH memory current rest value after next I REST)
    as(pending &suffix &called &owner &TAIL &QUIET &TO_CALL &READY &SUFFIX).
  exists(prelude++pending),suffix,selected,called,owner;split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|].
  split;[exact SELECTED|]. split;[eapply gateway_steps_append;eassumption|exact SUFFIX].
Qed.

Theorem gateway_actual_outcome_reaches_copy {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    data_block data_offset before world events value after next symbol definition:
  Genv.find_symbol ge _PyDict_Copy=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_outcome_from)[Vptr data_block data_offset]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists prefix suffix environment selected memory current,
    events=prefix++suffix /\selected!_data=Some(Vptr data_block data_offset) /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_outcome_from)[Vptr data_block data_offset]Kstop before)world)prefix
      (gateway_live(Callstate definition[Vptr data_block data_offset](gateway_outcome_copy_cont environment selected)memory)current) /\
    gateway_steps backend ge
      (gateway_live(Callstate definition[Vptr data_block data_offset](gateway_outcome_copy_cont environment selected)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros SYMBOL FUNCTION TYPE RUN NONNULL.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_outcome_from[Vptr data_block data_offset]Kstop
    before world events value Kstop after next RUN)
    as(pending &rest &called &owner &environment &parameters &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &REST).
  destruct(gateway_outcome_entry_canonical ge(Vptr data_block data_offset)called environment parameters allocated ENTRY)
    as[PARAMETERS ALLOC];subst parameters.
  pose proof(gateway_actual_outcome_allocations ge called environment allocated ALLOC)as BUFFERS.
  assert(LOCAL:environment!_PyDict_Copy=None).
  { apply(proj2(proj2(proj2 BUFFERS)));cbn;intuition discriminate. }
  destruct(gateway_outcome_body_reaches_copy backend ge environment(gateway_outcome_parameters(Vptr data_block data_offset))
    data_block data_offset allocated owner rest value after next symbol definition
    ltac:(apply PTree.gss)LOCAL SYMBOL FUNCTION TYPE REST NONNULL)
    as(prelude &suffix &selected &memory &current &TAIL &SELECTED &TO_COPY &SUFFIX).
  exists(pending++gateway_source E0::prelude),suffix,environment,selected,memory,current.
  split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|]. split;[exact SELECTED|]. split.
  - eapply gateway_steps_append;[exact PREFIX|].
    econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact TO_COPY].
  - exact SUFFIX.
Qed.
