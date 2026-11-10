(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A failed initial numeric allocation cannot be turned into a
   returned number by the later base allocation, error callbacks or cleanup. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayNumberConstruction GatewayFailurePaths
  GatewaySourcePaths GatewaySourceCuts GatewaySourceBoundCalls GatewayUnaryExpressions GatewayNullContexts GatewayFramedRuntime
  GatewaySourceSegmentAutomation.
Import ListNotations.

Ltac gateway_bound_null_failure closed loads reduce pointer :=
  tryif solve[apply gateway_failure_when_selected;apply gateway_failure_null_context;
    left;split;[exact pointer|];split;[reflexivity|];
    first[solve[left;cbn[gateway_must_null gateway_no_return];tauto]|
      solve[right;split;[vm_compute;reflexivity|cbn[gateway_null_barrier gateway_must_null gateway_no_return gateway_null_expression call_cont];intuition congruence]]]]then idtac else(
  lazymatch goal with
  | |-gateway_failure_when _ _ _ (Returnstate ?value ?saved ?memory)=>
    let call:=eval hnf in saved in
    lazymatch call with
    |Kcall ?destination ?function ?environment ?temporaries ?continuation=>
      eapply gateway_failure_when_same with(target:=State function Sskip continuation environment(set_opttemp destination value temporaries)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|
          gateway_bound_null_failure closed loads reduce pointer]
    end
  | |-gateway_failure_when _ _ _ (State ?function ?body ?continuation ?environment ?temporaries ?memory)=>
    let statement:=eval hnf in body in
    lazymatch statement with
    |(if ?flag then ?yes else ?no)=>
      let selected:=eval vm_compute in flag in
      lazymatch selected with
      |true=>change body with yes;gateway_bound_null_failure closed loads reduce pointer
      |false=>change body with no;gateway_bound_null_failure closed loads reduce pointer
      |?unknown=>fail 1 "source guard remains symbolic" unknown
      end
    |Ssequence ?first ?rest=>
      eapply gateway_failure_when_same with(target:=State function first(Kseq rest continuation)environment temporaries memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|
          gateway_bound_null_failure closed loads reduce pointer]
    |Sskip=>
      lazymatch continuation with
      |Kseq ?following ?rest=>
        eapply gateway_failure_when_same with(target:=State function following rest environment temporaries memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|
            gateway_bound_null_failure closed loads reduce pointer]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_failure_when_same with(target:=State function Sskip continuation environment(PTree.set identifier result temporaries)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_segment_expression loads reduce|
          gateway_bound_null_failure closed loads reduce pointer]
    |Sifthenelse(Etempvar _base _) ?yes ?no=>
      apply gateway_failure_when_selected;apply gateway_failure_null_context;
      left;split;[repeat eexists;reflexivity|];split;[reflexivity|];
      right;split;[reflexivity|];left;split;reflexivity
    |Sifthenelse ?expression ?yes ?no=>
      let flag:=open_constr:(_ : bool)in
      eapply gateway_failure_when_same with(target:=State function(if flag then yes else no)continuation environment temporaries memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;
          [gateway_segment_expression loads reduce|reduce ()]|
            gateway_bound_null_failure closed loads reduce pointer]
    |?unknown=>fail 1 "unsupported failure source" unknown
    end
  | |- ?unknown=>fail 1 "unsupported failure goal" unknown
  end).

Theorem gateway_number_base_after_null_zero {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters returned memory:
  parameters!_value__1=Some Vnullptr->
  gateway_failure_result backend ge(Returnstate returned(gateway_number_base_cont parameters)memory).
Proof.
  intro NULL.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(intros first current last following GOOD CHANGE;exact I).
  assert(FAILURE:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate returned(gateway_number_base_cont parameters)memory)).
  { gateway_bound_null_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [apply old_expression_value,value_temp;unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact NULL|reflexivity])
      ltac:(fun _=>reflexivity)
      ltac:(repeat eexists;reflexivity). }
  intros before world events value after next RUN;exact(FAILURE before world events value after next I RUN).
Qed.

Theorem gateway_number_null_zero_denied {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters before world events value after next symbol definition:
  Genv.find_symbol ge _PyLong_FromUnsignedLong=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[Ctypesdefs.tulong](Ctypesdefs.tptr(Tstruct __object noattr))cc_default->
  gateway_steps backend ge
    (gateway_live(Returnstate Vnullptr(gateway_number_zero_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intros SYMBOL FUNCTION TYPE RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(intros first current last following GOOD CHANGE;exact I).
  destruct(gateway_number_base_source_path backend ge(fun _ _=>True)parameters Vnullptr before symbol definition CLOSED SYMBOL FUNCTION TYPE)
    as(called_parameters &PATH &NULL &PARAMETERS).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as(prefix &rest &called &called_world &EVENTS &QUIET &PREFIX &READY &FROM_BASE).
  destruct(gateway_return_cut backend ge definition[Vlong(Int64.repr 1000000000)](gateway_number_base_cont called_parameters)
    called called_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_BASE)
    as(constructing &suffix &returned &changed &following &REST_EVENTS &BASE &REST).
  exact(gateway_number_base_after_null_zero backend ge called_parameters returned changed NULL changed following suffix value after next REST).
Qed.
