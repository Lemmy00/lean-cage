(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The observed metadata is rooted before its selected dictionary is released. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayPublicReferences
  GatewayAttachedReferences GatewayObjectDiscipline GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceRuntime GatewayReferenceBorrowedGraph GatewayReferenceNormalForm
  GatewayReferenceMoves GatewayOwnedObservationKey GatewayReferenceNumericFrames GatewayReferenceBoolean GatewayReferenceFrames GatewayReferencePlaces GatewayReferenceSourceExecution
  GatewayHeldGILViews GatewayObservationContexts GatewayOutcomeGetterSource GatewaySourceObjectReceipt GatewayFramedRuntime
  GatewaySourcePaths GatewayContexts GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Section OwnedObservationPresent.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (decimal_float:list Z->Floats.float->Prop)(detached:Values.val->mem->World->Prop)
  (io:Event->option gateway_native_io)(stable:World->block->Z->Prop)(thread_errno:World->int)
  (heap_allocation:block->Z->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (references:gateway_reference_runtime backend python objects)
  (public_references:gateway_public_reference_runtime backend python objects)
  (views:gateway_held_gil_views backend python objects).
Let owned:=@gateway_observation_owned_context World python objects decimal_float.
Let borrowed:=@gateway_observation_borrowed_context World python objects decimal_float.

Theorem gateway_actual_owned_observation_present parameters data data_offset key key_offset metadata metadata_offset description
    before world events value after next ledger data_ticket key_ticket held incref decref:
  parameters!_selected_data=Some(Vptr data data_offset)->parameters!_key=Some(Vptr key key_offset)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary 0 _selected_data)data_ticket(Vptr data data_offset)->
  gateway_reference_owns ledger(gateway_reference_temporary 0 _key)key_ticket(Vptr key key_offset)->
  gateway_reference_take(gateway_reference_temporary 0 _value)(gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_result 0)(gateway_reference_entries ledger)=None->
  (forall captured,In captured held->gateway_held_ticket captured<>data_ticket)->
  (forall captured,In captured held->gateway_held_ticket captured<>key_ticket)->
  borrowed ledger held(Vptr metadata metadata_offset)description before world->
  Genv.find_symbol ge _Py_IncRef=Some incref->Genv.find_funct_ptr ge incref=Some python_incref_definition->
  Genv.find_symbol ge _Py_DecRef=Some decref->Genv.find_funct_ptr ge decref=Some gateway_reference_decref_definition->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr metadata metadata_offset)(gateway_observation_lookup_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists minted key_released released final,
    value=Vptr metadata metadata_offset /\gateway_reference_ledger_well_formed final /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_temporary 0 _value)(Vptr metadata metadata_offset))
      (gateway_reference_valid ledger)=gateway_reference_valid minted /\
    gateway_reference_apply(gateway_reference_release(gateway_reference_temporary 0 _key)(Vptr key key_offset))
      (gateway_reference_valid minted)=gateway_reference_valid key_released /\
    gateway_reference_apply(gateway_reference_release(gateway_reference_temporary 0 _selected_data)(Vptr data data_offset))
      (gateway_reference_valid key_released)=gateway_reference_valid released /\
    gateway_reference_apply(gateway_reference_move(gateway_reference_temporary 0 _value)(gateway_reference_result 0))
      (gateway_reference_valid released)=gateway_reference_valid final /\
    gateway_reference_owns final(gateway_reference_result 0)(gateway_reference_next ledger)(Vptr metadata metadata_offset) /\
    gateway_reference_place_value ge(Returnstate value Kstop after)(gateway_reference_result 0)(Vptr metadata metadata_offset) /\
    owned final(held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=Vptr metadata metadata_offset;
      gateway_held_view:=description|}])after next /\
    exists root_prefix key_prefix release_prefix return_events root_memory root_world root_result rooted root_next root_event
      key_memory key_world key_result keyed key_next key_event release_memory release_world release_result unrooted release_next release_event selected updated,
      events=root_prefix++gateway_primitive root_event::(key_prefix++gateway_primitive key_event::
        (release_prefix++gateway_primitive release_event::return_events)) /\
      gateway_object_operation backend gateway_api_incref[Vptr metadata metadata_offset]
        root_memory root_world root_result rooted root_next root_event /\
      gateway_object_operation backend gateway_api_decref[Vptr key key_offset]
        key_memory key_world key_result keyed key_next key_event /\
      gateway_object_operation backend gateway_api_decref[Vptr data data_offset]
        release_memory release_world release_result unrooted release_next release_event /\
      gateway_steps backend ge
        (gateway_live(Returnstate(Vptr metadata metadata_offset)(gateway_observation_lookup_cont parameters)before)world)root_prefix
        (gateway_live(Callstate python_incref_definition[Vptr metadata metadata_offset]
          (gateway_observation_value_root_cont selected)root_memory)root_world) /\
      gateway_steps backend ge
        (gateway_live(Returnstate root_result(gateway_observation_value_root_cont selected)rooted)root_next)key_prefix
        (gateway_live(Callstate gateway_reference_decref_definition[Vptr key key_offset]
          (gateway_observation_key_release_cont selected)key_memory)key_world) /\
      gateway_steps backend ge
        (gateway_live(Returnstate key_result(gateway_observation_key_release_cont selected)keyed)key_next)release_prefix
        (gateway_live(Callstate gateway_reference_decref_definition[Vptr data data_offset]
          (gateway_observation_release_cont updated)release_memory)release_world) /\
      gateway_steps backend ge
        (gateway_live(Returnstate release_result(gateway_observation_release_cont updated)unrooted)release_next)return_events
        (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros DATA KEY WELL DATA_OWNED KEY_OWNED TEMP_FREE RESULT_FREE HELD_OTHER KEY_OTHER INPUT INC_SYMBOL INC_FUNCTION DEC_SYMBOL DEC_FUNCTION RUN.
  set(input:=borrowed ledger held(Vptr metadata metadata_offset)description).
  assert(CLOSED:gateway_ambient_closed backend input).
  { eapply gateway_observation_borrowed_context_closed;[exact runtime|exact reference_threads|exact views]. }
  assert(POINTER:forall memory current,input memory current->
    Mem.weak_valid_pointer memory metadata(Ptrofs.unsigned metadata_offset)=true).
  { intros memory current[[NORMAL SCOPE][ROOT REST]].
    destruct(proj1 NORMAL)as[PYTHON[LIVE[BYTES[DICTIONARIES WEAK]]]].
    destruct(WEAK _ ROOT)as(object &offset &SAME &VALID);inversion SAME;subst;exact VALID. }
  destruct(gateway_observation_present_root_source_path backend ge input parameters metadata metadata_offset before incref
    python_incref_definition CLOSED POINTER INC_SYMBOL INC_FUNCTION eq_refl)as(selected &PATH &VALUE &SAVED_DATA &SAVED_KEY).
  destruct(gateway_source_object_receipt backend ge gateway_api_incref python_incref_definition[Vptr metadata metadata_offset]
    (gateway_observation_value_root_cont selected)input _ before world events value after next eq_refl
    ltac:(cbn;exact I)ltac:(cbn;lia)CLOSED PATH INPUT RUN)
    as(root_prefix &rest &root_memory &root_world &root_result &rooted &root_next &root_event
      &EVENTS &AT_ROOT &ROOT_PREFIX &INCREMENT &REST).
  destruct AT_ROOT as[[NORMAL[FIT HELD]][ROOT[PRIVATE[DESTROY DESCRIPTION]]]].
  destruct(gateway_reference_incref_borrowed_graph backend python objects decimal_float references ledger
    (gateway_reference_temporary 0 _value)held(Vptr metadata metadata_offset)description
    root_memory root_world root_result rooted root_next root_event WELL FIT TEMP_FREE HELD NORMAL ROOT PRIVATE DESTROY DESCRIPTION INCREMENT)
    as(minted &MINT &MINTED_WELL &COUNTS &METADATA_OWNED &CAPTURED &AFTER_NORMAL &INCREMENT_EFFECT).
  set(captured:={|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=Vptr metadata metadata_offset;
    gateway_held_view:=description|}).
  assert(DATA_AFTER:gateway_reference_owns minted(gateway_reference_temporary 0 _selected_data)data_ticket(Vptr data data_offset)).
  { unfold gateway_reference_owns;rewrite(proj1(gateway_reference_mint_entries _ _ _ _ MINT));right;exact DATA_OWNED. }
  assert(RESULT_AFTER:gateway_reference_take(gateway_reference_result 0)(gateway_reference_entries minted)=None).
  { eapply(gateway_reference_mint_keeps_vacant ledger(gateway_reference_temporary 0 _value)(Vptr metadata metadata_offset)
      (gateway_reference_result 0)minted);[exact RESULT_FREE|discriminate|exact MINT]. }
  assert(TICKET_DIFFERENT:gateway_reference_next ledger<>data_ticket).
  { pose proof(proj2(proj2 WELL))as BOUNDS;apply Forall_forall with
      (x:={|gateway_reference_ticket:=data_ticket;gateway_reference_owner:=gateway_reference_temporary 0 _selected_data;
        gateway_reference_pointer:=Vptr data data_offset|})in BOUNDS;[cbn in BOUNDS;lia|exact DATA_OWNED]. }
  assert(KEY_AFTER:gateway_reference_owns minted(gateway_reference_temporary 0 _key)key_ticket(Vptr key key_offset)).
  { unfold gateway_reference_owns;rewrite(proj1(gateway_reference_mint_entries _ _ _ _ MINT));right;exact KEY_OWNED. }
  assert(KEY_TICKET_DIFFERENT:gateway_reference_next ledger<>key_ticket).
  { pose proof(proj2(proj2 WELL))as BOUNDS;apply Forall_forall with
      (x:={|gateway_reference_ticket:=key_ticket;gateway_reference_owner:=gateway_reference_temporary 0 _key;
        gateway_reference_pointer:=Vptr key key_offset|})in BOUNDS;[cbn in BOUNDS;lia|exact KEY_OWNED]. }
  assert(OWNERS_DIFFERENT:data_ticket<>key_ticket).
  { intro SAME;rewrite<-SAME in KEY_OWNED.
    destruct(gateway_reference_owned_ticket_unique _ _ _ _ _ _ WELL DATA_OWNED KEY_OWNED)as[DIFFERENT _];discriminate. }
  assert(SELECTED_KEY:selected!_key=Some(Vptr key key_offset))by(congruence).
  assert(KEY_HELD_OTHER:forall entry,In entry(held++[captured])->gateway_held_ticket entry<>key_ticket).
  { intros entry MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|IMPOSSIBLE]].
    - apply KEY_OTHER;exact OLD.
    - subst entry;exact KEY_TICKET_DIFFERENT.
    - contradiction. }
  destruct(gateway_actual_owned_observation_key_release backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads public_references selected key key_offset root_result rooted root_next rest value after next
    minted key_ticket(held++[captured])decref SELECTED_KEY MINTED_WELL KEY_AFTER KEY_HELD_OTHER
    (conj AFTER_NORMAL(conj COUNTS CAPTURED))DEC_SYMBOL DEC_FUNCTION REST)
    as(key_released &key_prefix &key_suffix &key_memory &key_world &key_result &keyed &key_next &key_event
      &KEY_EVENTS &KEY_RELEASE &KEY_WELL &KEY_CONTEXT &KEY_RETAINED &KEY_DECREMENT &KEY_PREFIX &KEY_RETURN).
  assert(DATA_AFTER_KEY:gateway_reference_owns key_released(gateway_reference_temporary 0 _selected_data)data_ticket(Vptr data data_offset))
    by(apply KEY_RETAINED;assumption).
  assert(METADATA_AFTER_KEY:gateway_reference_owns key_released(gateway_reference_temporary 0 _value)
    (gateway_reference_next ledger)(Vptr metadata metadata_offset))by(apply KEY_RETAINED;assumption).
  assert(RESULT_AFTER_KEY:gateway_reference_take(gateway_reference_result 0)(gateway_reference_entries key_released)=None).
  { eapply gateway_reference_numeric_release_keeps_vacant;[exact RESULT_AFTER|exact KEY_RELEASE]. }
  set(at_release:=owned key_released(held++[captured])).
  assert(RELEASE_CLOSED:gateway_ambient_closed backend at_release).
  { eapply gateway_observation_owned_context_closed;[exact runtime|exact reference_threads]. }
  assert(SELECTED_DATA:selected!_selected_data=Some(Vptr data data_offset))by(congruence).
  assert(METADATA_POINTER:forall memory current,at_release memory current->
    Mem.weak_valid_pointer memory metadata(Ptrofs.unsigned metadata_offset)=true).
  { intros memory current[NORMAL_NOW[FIT_NOW HELD_NOW]].
    assert(ROOT_NOW:gateway_rooted(python current)(objects current)(Vptr metadata metadata_offset))
      by(eapply gateway_reference_owned_rooted;[exact FIT_NOW|exact METADATA_AFTER_KEY]).
    destruct(proj1 NORMAL_NOW)as[PYTHON_NOW[LIVE_NOW[BYTES_NOW[DICTIONARIES_NOW WEAK_NOW]]]].
    destruct(WEAK_NOW _ ROOT_NOW)as(object &offset &SAME &VALID);inversion SAME;subst;exact VALID. }
  destruct(gateway_observation_release_source_path backend ge at_release selected data data_offset metadata metadata_offset
    key_result keyed decref gateway_reference_decref_definition RELEASE_CLOSED SELECTED_DATA VALUE METADATA_POINTER
    DEC_SYMBOL DEC_FUNCTION eq_refl)as(updated &RELEASE_PATH &UPDATED_VALUE &UPDATED_DATA).
  assert(FINAL_VALUE:updated!_value=Some(Vptr metadata metadata_offset))by(congruence).
  destruct(gateway_source_object_receipt backend ge gateway_api_decref gateway_reference_decref_definition[Vptr data data_offset]
    (gateway_observation_release_cont updated)at_release _ keyed key_next key_suffix value after next eq_refl
    ltac:(cbn;exact I)ltac:(cbn;lia)RELEASE_CLOSED RELEASE_PATH KEY_CONTEXT KEY_RETURN)
    as(release_prefix &return_events &release_memory &release_world &release_result &unrooted &release_next &release_event
      &REST_EVENTS &[RELEASE_NORMAL[RELEASE_FIT RELEASE_HELD]]&RELEASE_PREFIX &DECREMENT &RETURN).
  destruct(gateway_public_release_keeps_independent_graphs backend python objects decimal_float public_references key_released
    (gateway_reference_temporary 0 _selected_data)data_ticket(Vptr data data_offset)(held++[captured])
    release_memory release_world release_result unrooted release_next release_event KEY_WELL RELEASE_FIT DATA_AFTER_KEY
    (gateway_normal_attached _ _ _ RELEASE_NORMAL)RELEASE_HELD)
    as(released &RELEASE &RELEASED_WELL &RELEASED_FIT &RELEASED_HELD &RELEASE_EFFECT &RETAINED).
  - intros entry MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|IMPOSSIBLE]].
    + apply HELD_OTHER;exact OLD.
    + subst entry;exact TICKET_DIFFERENT.
    + contradiction.
  - exact DECREMENT.
  - assert(RETURN_NORMAL:gateway_objects_ready(python release_next)(objects release_next)unrooted).
    { destruct(gateway_attached_reference_ready _ _ _ _ _ _ _ RELEASE_EFFECT)as[VALID GIL].
      split;[exact VALID|]. split;[exact GIL|].
      rewrite(gateway_attached_reference_pending _ _ _ _ _ _ _ RELEASE_EFFECT);exact(proj2(proj2 RELEASE_NORMAL)). }
    assert(RETURN_OWNED:gateway_reference_owns released(gateway_reference_temporary 0 _value)
      (gateway_reference_next ledger)(Vptr metadata metadata_offset))by(apply RETAINED;[exact TICKET_DIFFERENT|exact METADATA_AFTER_KEY]).
    assert(RETURN_FREE:gateway_reference_take(gateway_reference_result 0)(gateway_reference_entries released)=None).
    { eapply gateway_reference_numeric_release_keeps_vacant;[exact RESULT_AFTER_KEY|exact RELEASE]. }
    destruct(gateway_actual_owned_observation_return backend ge python objects decimal_float detached io stable thread_errno heap_allocation
      runtime reference_threads updated(Vptr metadata metadata_offset)release_result unrooted release_next return_events value after next
      released(gateway_reference_next ledger)(held++[captured])FINAL_VALUE ltac:(right;eexists;eexists;reflexivity)RELEASED_WELL RETURN_OWNED
      RETURN_FREE(conj RETURN_NORMAL(conj RELEASED_FIT RELEASED_HELD))RETURN)
      as(final &SAME &FINAL_WELL &MOVE &RESULT &BINDING &FINAL).
    exists minted,key_released,released,final;split;[exact SAME|]. split;[exact FINAL_WELL|]. split;[exact MINT|].
    split;[exact KEY_RELEASE|]. split;[exact RELEASE|]. split;[exact MOVE|]. split;[exact RESULT|]. split;[exact BINDING|]. split;[exact FINAL|].
    exists root_prefix,key_prefix,release_prefix,return_events,root_memory,root_world,root_result,rooted,root_next,root_event,
      key_memory,key_world,key_result,keyed,key_next,key_event,release_memory,release_world,release_result,unrooted,release_next,release_event,selected,updated.
    split;[rewrite EVENTS,KEY_EVENTS,REST_EVENTS;reflexivity|]. split;[exact INCREMENT|]. split;[exact KEY_DECREMENT|]. split;[exact DECREMENT|].
    split;[exact ROOT_PREFIX|]. split;[exact KEY_PREFIX|]. split;assumption.
Qed.
End OwnedObservationPresent.
