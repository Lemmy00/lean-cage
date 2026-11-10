(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The source assigns the same owned copy to its allocated Outcome. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcome GatewayOutcomeAllocation GatewayOutcomeMemory
  GatewaySourceDynamic GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime GatewayReturnIdentity GatewayFrames
  GatewayUnaryExpressions GatewayRuntimeCuts.
Import ListNotations.
Open Scope Z_scope.

Fixpoint gateway_outcome_right_suffix(n:nat)(source:statement):statement:=
  match n,source with S remaining,Ssequence _ rest=>gateway_outcome_right_suffix remaining rest|_,_=>source end.
Definition gateway_outcome_allocation_tail:=gateway_outcome_right_suffix 11(fn_body f_host_outcome_from).
Definition gateway_outcome_after_allocation:=match gateway_outcome_allocation_tail with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_outcome_after_guard:=match gateway_outcome_after_allocation with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_outcome_return:=match gateway_outcome_after_guard with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_outcome_allocation_assign:=
  Sset _outcome(Ecast(Etempvar _t'24(tptr(Tstruct __object noattr)))(tptr(Tstruct __9090 noattr))).
Definition gateway_outcome_allocation_cont environment parameters:=
  Kcall(Some _t'24)f_host_outcome_from environment parameters
    (Kseq gateway_outcome_allocation_assign(Kseq gateway_outcome_after_allocation Kstop)).
Definition gateway_outcome_allocated_parameters object parameters:=
  PTree.set _outcome(Vptr object Ptrofs.zero)(set_opttemp(Some _t'24)(Vptr object Ptrofs.zero)parameters).
Definition gateway_outcome_assigned_state environment parameters object memory:=
  State f_host_outcome_from Sskip(Kseq gateway_outcome_return Kstop)environment
    (gateway_outcome_allocated_parameters object parameters)memory.

Theorem actual_outcome_construction_source:
  gateway_outcome_after_guard=Ssequence
    (Sassign(gateway_outcome_member _outcome)(Etempvar _copy(tptr(Tstruct __object noattr))))
    (Sreturn(Some(Ecast(Etempvar _outcome(tptr(Tstruct __9090 noattr)))(tptr(Tstruct __object noattr))))) /\
  gateway_outcome_return=Sreturn(Some(Ecast(Etempvar _outcome(tptr(Tstruct __9090 noattr)))
    (tptr(Tstruct __object noattr)))).
Proof. split;reflexivity. Qed.

Lemma gateway_outcome_pointer_notnull memory object ty:
  Mem.weak_valid_pointer memory object 0=true ->
  sem_unary_operation Onotbool(Vptr object Ptrofs.zero)(tptr ty)memory=Some(Vint Int.zero).
Proof.
  intro POINTER;change(option_map(fun flag=>Val.of_bool(negb flag))
    (if Mem.weak_valid_pointer memory object 0 then Some true else None)=Some(Vint Int.zero)).
  rewrite POINTER;reflexivity.
Qed.

Ltac gateway_outcome_to_assignment closed pointer:=
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (Returnstate ?value ?saved ?memory) _ _=>
    let call:=eval hnf in saved in lazymatch call with
    |Kcall ?destination ?function ?environment ?parameters ?continuation=>
      eapply gateway_segment_same with(next:=State function Sskip continuation environment(set_opttemp destination value parameters)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|gateway_outcome_to_assignment closed pointer]
    end
  | |-gateway_source_segment _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory) _ _=>
    let statement:=eval hnf in body in lazymatch statement with
    |Ssequence ?first ?rest=>eapply gateway_segment_same with(next:=State function first(Kseq rest continuation)environment parameters memory);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|gateway_outcome_to_assignment closed pointer]
    |Sskip=>lazymatch continuation with
      |Kseq ?following ?rest=>eapply gateway_segment_same with(next:=State function following rest environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|gateway_outcome_to_assignment closed pointer]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_segment_same with(next:=State function Sskip continuation environment(PTree.set identifier result parameters)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;
          gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|gateway_outcome_to_assignment closed pointer]
    |Sifthenelse ?expression ?yes ?no=>
      eapply gateway_segment_same with(next:=State function no continuation environment parameters memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge with(b:=false);
          [eapply gateway_unary_expression_value with(result:=Vint Int.zero);
            [gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
             apply gateway_outcome_pointer_notnull;pointer ()]|reflexivity]|
          gateway_outcome_to_assignment closed pointer]
    |Sassign _ _=>idtac
    end
  end.

Theorem gateway_outcome_assignment_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property result:Memory.mem->World->Prop)environment parameters object data_block data_offset memory :
  gateway_outcome_member_layout ge ->parameters!_copy=Some(Vptr data_block data_offset) ->
  gateway_ambient_closed backend property ->
  (forall before world,property before world->Mem.weak_valid_pointer before object 0=true) ->
  (forall before world,property before world->exists after,
    Mem.store Mptr before object 16(Vptr data_block data_offset)=Some after /\result after world) ->
  gateway_source_segment backend ge property
    (Returnstate(Vptr object Ptrofs.zero)(gateway_outcome_allocation_cont environment parameters)memory)
    (gateway_outcome_assigned_state environment parameters object memory)result.
Proof.
  intros LAYOUT COPY CLOSED POINTER STORE.
  gateway_outcome_to_assignment CLOSED ltac:(fun _=>
    match goal with GOOD:property ?current ?world|-_=>exact(POINTER current world GOOD)end).
  eapply gateway_segment_next with(next:=gateway_outcome_assigned_state environment parameters object memory)(middle:=result).
  - exact CLOSED.
  - cbn;tauto.
  - intros before world READY;destruct(STORE before world READY)as(after &WRITE &POST).
    exists after;split;[|exact POST].
    eapply gateway_actual_outcome_data_assignment with(data:=Vptr data_block data_offset).
    + exact LAYOUT.
    + apply PTree.gss.
    + unfold gateway_outcome_allocated_parameters,set_opttemp;
        repeat rewrite PTree.gso by discriminate;exact COPY.
    + reflexivity.
    + change(Mem.store Mptr before object 16(Vptr data_block data_offset)=Some after);exact WRITE.
  - apply gateway_segment_here.
Qed.

Theorem gateway_outcome_final_return_identity {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters object before world events returned after next:
  gateway_steps backend ge(gateway_live(gateway_outcome_assigned_state environment parameters object before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->returned=Vptr object Ptrofs.zero.
Proof.
  intro RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(GatewayRuntimeCuts.gateway_uniform_edge_side_cut backend ge _ CLOSED
    (gateway_outcome_assigned_state environment parameters object before)
    (State f_host_outcome_from gateway_outcome_return Kstop environment(gateway_outcome_allocated_parameters object parameters)before)
    before world events returned after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)I RUN)
    as(prefix &suffix &middle &current &EVENTS &AMBIENT &PREFIX &READY &REST).
  eapply(gateway_return_expression_identity backend ge f_host_outcome_from
    (Ecast(Etempvar _outcome(tptr(Tstruct __9090 noattr)))(tptr(Tstruct __object noattr)))Kstop
    environment(gateway_outcome_allocated_parameters object parameters)middle current(Vptr object Ptrofs.zero)
    suffix returned after next);[reflexivity| | |exact REST].
  - intros;eapply cast_expression_value;[apply old_expression_value,value_temp;apply PTree.gss|reflexivity].
  - intros memory value CAST;eapply(gateway_pointer_cast_identity memory(tptr(Tstruct __object noattr))
      (tptr(Tstruct __object noattr))(Vptr object Ptrofs.zero)value);
      [eexists;reflexivity|eexists;reflexivity|exact CAST].
Qed.
