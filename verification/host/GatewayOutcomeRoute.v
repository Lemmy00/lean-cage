(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Presentation cannot replace the captured private-copy pointer before allocation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMandatoryCut GatewayOutcomeConstruction GatewayOutcomeCopySource
  GatewayOutcomeValidationCut GatewaySourceObjectReceipt GatewayObjects GatewayContexts GatewayOperations GatewayExternalFrontier GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Ltac gateway_outcome_allocation_marker:=
  first[solve[left;split;reflexivity]|
    lazymatch goal with
    | |-gateway_mandatory_body ?protected ?marker ?tail ?body ?continuation=>
      let actual:=eval hnf in body in lazymatch actual with
      |Ssequence ?first ?second=>
        change(gateway_mandatory_body protected marker tail actual continuation);
        first[right;right;split;[reflexivity|gateway_outcome_allocation_marker]|
              right;left;gateway_outcome_allocation_marker]
      end
    end].

Theorem gateway_outcome_presentation_allocation_profile:
  gateway_mandatory_body _copy gateway_outcome_allocation_tail Kstop gateway_outcome_after_copy Kstop.
Proof. gateway_outcome_allocation_marker. Qed.

Theorem gateway_outcome_same_copy_reaches_allocation {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters copy_block copy_offset before world events value after next:
  parameters!_copy=Some(Vptr copy_block copy_offset)->
  gateway_steps backend ge
    (gateway_live(State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy Kstop)environment parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists prefix suffix selected memory current,
    events=prefix++suffix /\selected!_copy=Some(Vptr copy_block copy_offset) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy Kstop)environment parameters before)world)prefix
      (gateway_live(State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment selected memory)current) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment selected memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros COPY RUN NONNULL.
  eapply(gateway_mandatory_actual_cut backend ge f_host_outcome_from environment _copy(Vptr copy_block copy_offset)
    gateway_outcome_allocation_tail Kstop _ world events value after next);[repeat eexists|reflexivity| |exact RUN|exact NONNULL].
  left;split;[reflexivity|]. split;[reflexivity|]. split;[exact COPY|]. split;[reflexivity|].
  right;split;[reflexivity|]. left;exact gateway_outcome_presentation_allocation_profile.
Qed.

Theorem gateway_actual_outcome_copy_operation {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    data_block data_offset before world events value after next symbol external types result_type convention:
  Genv.find_symbol ge _PyDict_Copy=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(External external types result_type convention)->
  type_of_fundef(External external types result_type convention)=
    Tfunction[tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default->
  gateway_object_api_definition gateway_api_dict_copy=Some(External external types result_type convention)->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_outcome_from)[Vptr data_block data_offset]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists prefix suffix environment selected memory current returned changed following observed,
    events=prefix++gateway_primitive observed::suffix /\selected!_data=Some(Vptr data_block data_offset) /\returned<>Vnullptr /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_outcome_from)[Vptr data_block data_offset]Kstop before)world)prefix
      (gateway_live(Callstate(External external types result_type convention)[Vptr data_block data_offset]
        (gateway_outcome_copy_cont environment selected)memory)current) /\
    gateway_object_operation backend gateway_api_dict_copy[Vptr data_block data_offset]memory current returned changed following observed /\
    gateway_steps backend ge
      (gateway_live(Returnstate returned(gateway_outcome_copy_cont environment selected)changed)following)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros SYMBOL FUNCTION TYPE DEFINITION RUN NONNULL.
  destruct(gateway_actual_outcome_reaches_copy backend ge data_block data_offset before world events value after next symbol
    (External external types result_type convention)SYMBOL FUNCTION TYPE RUN NONNULL)
    as(prelude &rest &environment &selected &called &owner &EVENTS &DATA &PREFIX &REST).
  destruct(gateway_actual_external_frontier backend ge external types result_type convention[Vptr data_block data_offset]
    (gateway_outcome_copy_cont environment selected)called owner rest value after next ltac:(exact I)ltac:(cbn;lia)REST)
    as(pending &suffix &memory &current &returned &changed &following &observed &TAIL &PENDING &TO_OPERATION &OPERATION &SUFFIX).
  exists(prelude++pending),suffix,environment,selected,memory,current,returned,changed,following,observed.
  split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|]. split;[exact DATA|]. split.
  - intro NULL;subst returned;apply NONNULL;eapply gateway_actual_outcome_copy_failure;exact SUFFIX.
  - split;[eapply gateway_steps_append;eassumption|]. split;[eexists;split;eassumption|exact SUFFIX].
Qed.
