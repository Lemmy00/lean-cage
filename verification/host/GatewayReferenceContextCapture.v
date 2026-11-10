(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: An isolated callee capture retains the actual older caller's ownership places. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayRuntimeCuts GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceFrames GatewayReferenceExecution GatewayReferencePlaces GatewayReferenceCapture GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_context_reference_capture {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)context function environment parameters identifier destination ty tail pointer
    before world events value after next ledger ticket:
  is_call_cont context->gateway_ambient_closed backend property->property before world->identifier<>destination->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))ticket pointer->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)(gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)(gateway_reference_entries ledger)=None->
  gateway_steps backend ge(gateway_live(Returnstate pointer
    (gateway_reference_capture_cont function environment parameters identifier destination ty tail)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists returned stored prefix suffix memory current,
    events=prefix++suffix /\property memory current /\
    gateway_steps backend ge(gateway_live(Returnstate pointer
      (gateway_reference_capture_cont function environment parameters identifier destination ty tail)before)world)prefix
      (gateway_live(State function Sskip tail environment(gateway_reference_capture_parameters parameters identifier destination pointer)memory)current) /\
    gateway_reference_execution backend ge gateway_reference_frame_select
      (gateway_plug(gateway_live(Returnstate pointer
        (gateway_reference_capture_cont function environment parameters identifier destination ty tail)before)world)context)
      (gateway_reference_valid ledger)prefix
      (gateway_plug(gateway_live(State function Sskip tail environment
        (gateway_reference_capture_parameters parameters identifier destination pointer)memory)current)context)(gateway_reference_valid stored) /\
    gateway_reference_apply(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))
      (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier))(gateway_reference_valid ledger)=gateway_reference_valid returned /\
    gateway_reference_apply(gateway_reference_move(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)
      (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination))(gateway_reference_valid returned)=gateway_reference_valid stored /\
    gateway_reference_ledger_well_formed stored /\
    gateway_reference_owns stored(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)ticket pointer /\
    gateway_reference_place_value ge(plug_state(State function Sskip tail environment
      (gateway_reference_capture_parameters parameters identifier destination pointer)memory)context)
      (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)pointer /\
    (forall other,gateway_reference_count stored other=gateway_reference_count ledger other) /\
    gateway_steps backend ge(gateway_live(State function Sskip tail environment
      (gateway_reference_capture_parameters parameters identifier destination pointer)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CALL CLOSED INPUT DIFFERENT WELL OWNED FIRST_VACANT LAST_VACANT RUN.
  set(return_tail:=Kseq(Sset destination(Etempvar identifier ty))tail).
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (Returnstate pointer(gateway_reference_capture_cont function environment parameters identifier destination ty tail)before)
    (State function Sskip return_tail environment(PTree.set identifier pointer parameters)before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)INPUT RUN)
    as(prefix &rest &first &first_world &EVENTS &AMBIENT &PREFIX &FIRST &REST).
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (State function Sskip return_tail environment(PTree.set identifier pointer parameters)first)
    (State function(Sset destination(Etempvar identifier ty))tail environment(PTree.set identifier pointer parameters)first)
    first first_world rest value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)FIRST REST)
    as(pending &later &second &second_world &REST_EVENTS &PENDING &PENDING_RUN &SECOND &LATER).
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (State function(Sset destination(Etempvar identifier ty))tail environment(PTree.set identifier pointer parameters)second)
    (State function Sskip tail environment(gateway_reference_capture_parameters parameters identifier destination pointer)second)
    second second_world later value after next ltac:(cbn;tauto)
    ltac:(intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss)SECOND LATER)
    as(waiting &suffix &third &third_world &LATER_EVENTS &WAITING &WAITING_RUN &THIRD &SUFFIX).
  destruct(gateway_reference_returned_owner backend ge function identifier environment parameters(plug_cont return_tail context)
    pointer first first_world ledger ticket WELL OWNED FIRST_VACANT)
    as(returned &RETURN_EXECUTION &RETURNED_WELL &RETURNED_OWNER &RETURNED_BINDING &RETURN_COUNTS).
  assert(RETURN_MOVE:gateway_reference_apply(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))
    (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier))(gateway_reference_valid ledger)=gateway_reference_valid returned).
  { inversion RETURN_EXECUTION as[|a b c d e f g HEAD TAIL];subst;inversion TAIL;reflexivity. }
  assert(STORE_VACANT:gateway_reference_take(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)
    (gateway_reference_entries returned)=None).
  { eapply(gateway_reference_move_keeps_vacant ledger(gateway_reference_result(S(gateway_reference_depth(plug_cont tail context))))
      (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)
      (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination)returned);
      [exact LAST_VACANT|congruence|exact RETURN_MOVE]. }
  assert(ASSIGN:gateway_step backend ge
    (gateway_live(State function(Sset destination(Etempvar identifier ty))(plug_cont tail context)environment(PTree.set identifier pointer parameters)third)third_world)
    (gateway_source E0)(gateway_live(State function Sskip(plug_cont tail context)environment
      (gateway_reference_capture_parameters parameters identifier destination pointer)third)third_world)).
  { apply gateway_internal;[exact I|apply step_set;constructor;apply PTree.gss]. }
  destruct(gateway_reference_assigned_owner backend ge function destination identifier(Etempvar identifier ty)(plug_cont tail context)environment
    (PTree.set identifier pointer parameters)pointer third third_world third returned ticket eq_refl
    RETURNED_WELL RETURNED_OWNER STORE_VACANT ASSIGN)
    as(stored &STORE_EXECUTION &STORED_WELL &STORED_OWNER &STORED_BINDING &STORE_COUNTS).
  assert(STORE_MOVE:gateway_reference_apply(gateway_reference_move(gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))identifier)
    (gateway_reference_temporary(gateway_reference_depth(plug_cont tail context))destination))(gateway_reference_valid returned)=gateway_reference_valid stored).
  { inversion STORE_EXECUTION as[|a b c d e f g HEAD TAIL];subst;inversion TAIL;reflexivity. }
  set(all_prefix:=prefix++gateway_source E0::pending++gateway_source E0::waiting++[gateway_source E0]).
  assert(PHYSICAL:gateway_steps backend ge
    (gateway_live(Returnstate pointer(gateway_reference_capture_cont function environment parameters identifier destination ty tail)before)world)all_prefix
    (gateway_live(State function Sskip tail environment(gateway_reference_capture_parameters parameters identifier destination pointer)third)third_world)).
  { unfold all_prefix;eapply gateway_steps_append;[exact PREFIX|]. econstructor.
    - apply gateway_internal;[exact I|apply step_returnstate].
    - eapply gateway_steps_append;[exact PENDING_RUN|]. econstructor.
      + apply gateway_internal;[exact I|apply step_skip_seq].
      + eapply gateway_steps_append;[exact WAITING_RUN|]. econstructor.
        * apply gateway_internal;[exact I|apply step_set;constructor;apply PTree.gss].
        * constructor. }
  exists returned,stored,all_prefix,suffix,third,third_world.
  split.
  - unfold all_prefix;rewrite EVENTS,REST_EVENTS,LATER_EVENTS;
      repeat first[rewrite<-app_assoc|progress cbn[app]];reflexivity.
  - split;[exact THIRD|]. split;[exact PHYSICAL|]. split.
    + unfold all_prefix;eapply gateway_reference_execution_append;
        [eapply gateway_reference_ambient_execution;[exact AMBIENT|exact(gateway_plug_steps backend ge _ _ _ context CALL PREFIX)]|].
      eapply gateway_reference_execution_append with(prefix:=[gateway_source E0]);[exact RETURN_EXECUTION|].
      eapply gateway_reference_execution_append;
        [eapply gateway_reference_ambient_execution;[exact PENDING|exact(gateway_plug_steps backend ge _ _ _ context CALL PENDING_RUN)]|].
      econstructor.
      * apply gateway_internal;[exact I|apply step_skip_seq].
      * change(gateway_reference_execution backend ge gateway_reference_frame_select
          (gateway_live(State function(Sset destination(Etempvar identifier ty))(plug_cont tail context)environment(PTree.set identifier pointer parameters)second)second_world)
          (gateway_reference_valid returned)(waiting++[gateway_source E0])
          (gateway_live(State function Sskip(plug_cont tail context)environment
            (gateway_reference_capture_parameters parameters identifier destination pointer)third)third_world)(gateway_reference_valid stored)).
        eapply gateway_reference_execution_append;
          [eapply gateway_reference_ambient_execution;[exact WAITING|exact(gateway_plug_steps backend ge _ _ _ context CALL WAITING_RUN)]|exact STORE_EXECUTION].
    + split;[exact RETURN_MOVE|]. split;[exact STORE_MOVE|]. split;[exact STORED_WELL|]. split;[exact STORED_OWNER|]. split;[exact STORED_BINDING|].
      split;[intro other;rewrite STORE_COUNTS,RETURN_COUNTS;reflexivity|exact SUFFIX].
Qed.
