(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Tuple and callback credits originate at their actual SDK returns. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects GatewayReferences
  GatewayGraphSnapshots GatewayObjectThreads GatewayPresentationRuntime GatewayPresentationSource GatewayPresentationTrace GatewayReferenceLedger GatewayReferencePlaces
  GatewayReferenceAccounting GatewayReferenceRuntime GatewayReferenceNormalForm GatewayReferenceHeld GatewayReferenceRetained
  GatewayReferenceThreads GatewayReferenceBalance.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_presentation_actual_operation {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    api definition arguments continuation before world result after next observed:
  gateway_presentation_definition api=Some definition ->
  gateway_step backend ge(gateway_live(Callstate definition arguments continuation before)world)(gateway_primitive observed)
    (gateway_live(Returnstate result continuation after)next) ->
  gateway_presentation_operation backend api arguments before world result after next observed.
Proof.
  intros DEFINITION STEP;exists definition;split;[exact DEFINITION|].
  destruct definition;inversion STEP;subst;cbn[gateway_runtime_operation];eassumption.
Qed.

Lemma gateway_presentation_credit_mints {World}python objects decimal_float ledger owner held reserved pointer world next:
  gateway_reference_ledger_well_formed ledger ->
  (forall value,(count_occ Val.eq reserved value+gateway_reference_count ledger value<=python_native_strong(python world)value)%nat) ->
  gateway_reference_take owner(gateway_reference_entries ledger)=None ->
  @gateway_reference_held World python objects decimal_float ledger held world ->
  gateway_reference_credit(python world)(python next)pointer ->
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[] ->
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[] ->
  exists minted,
    gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid minted /\
    gateway_reference_ledger_well_formed minted /\
    gateway_reference_owns minted owner(gateway_reference_next ledger)pointer /\
    gateway_reference_scope python objects decimal_float minted held next /\
    (forall value,(count_occ Val.eq reserved value+gateway_reference_count minted value<=python_native_strong(python next)value)%nat) /\
    gateway_reference_balance(python world)(python next)ledger minted /\
    (forall place ticket value,gateway_reference_owns ledger place ticket value->gateway_reference_owns minted place ticket value).
Proof.
  intros WELL BUDGET VACANT HELD CREDIT FRAME PRIVACY.
  assert(FIT:gateway_reference_counts_fit ledger(python world))by(intro value;specialize(BUDGET value);lia).
  destruct(gateway_reference_credit_mints ledger owner pointer(python world)(python next)WELL FIT VACANT CREDIT)
    as(minted &MINT &MINTED_WELL &MINTED_FIT &MINTED_OWNER &RETAINED).
  assert(BALANCE:gateway_reference_balance(python world)(python next)ledger minted)
    by(eapply gateway_reference_balance_mint;eassumption).
  assert(MINTED_HELD:gateway_reference_held python objects decimal_float minted held next).
  { eapply gateway_reference_held_frame;[exact HELD|exact FIT|exact MINTED_FIT| |exact FRAME|exact PRIVACY].
    intros captured MEMBER;destruct(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OWNED]REST].
    exists place;apply RETAINED;exact OWNED. }
  exists minted;split;[exact MINT|]. split;[exact MINTED_WELL|]. split;[exact MINTED_OWNER|].
  split;[exact(conj MINTED_FIT MINTED_HELD)|]. split.
  - eapply gateway_reference_balance_reservations;[exact BUDGET|exact BALANCE].
  - split;assumption.
Qed.

Theorem gateway_actual_presentation_tuple_credit {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples storage decimal_float
    (runtime:gateway_presentation_runtime backend python objects tuples storage)
    ledger held reserved protected continuation before world tuple after next observed:
  gateway_reference_ledger_well_formed ledger ->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat) ->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth continuation))(gateway_reference_entries ledger)=None ->
  gateway_reference_held python objects decimal_float ledger held world ->
  gateway_objects_ready(python world)(objects world)before ->gateway_presentation_owned_region storage world before protected ->
  gateway_step backend ge
    (gateway_live(Callstate gateway_presentation_new_definition[Vlong Int64.one]continuation before)world)(gateway_primitive observed)
    (gateway_live(Returnstate tuple continuation after)next) ->tuple<>Vnullptr ->
  exists minted object offset,
    tuple=Vptr object offset /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_result(gateway_reference_depth continuation))tuple)
      (gateway_reference_valid ledger)=gateway_reference_valid minted /\
    gateway_reference_ledger_well_formed minted /\
    gateway_reference_owns minted(gateway_reference_result(gateway_reference_depth continuation))(gateway_reference_next ledger)tuple /\
    gateway_reference_place_value ge(Returnstate tuple continuation after)(gateway_reference_result(gateway_reference_depth continuation))tuple /\
    gateway_reference_scope python objects decimal_float minted held next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count minted pointer<=python_native_strong(python next)pointer)%nat) /\
    gateway_objects_ready(python next)(objects next)after /\tuples next tuple=Some[None] /\
    python_strong(python world)tuple=0%nat /\python_strong(python next)tuple=1%nat /\
    gateway_presentation_frame python objects storage protected before world after next /\
    gateway_reference_balance(python world)(python next)ledger minted.
Proof.
  intros WELL BUDGET VACANT HELD READY OWNED STEP NONNULL.
  pose proof(gateway_presentation_actual_operation backend ge gateway_presentation_tuple_new gateway_presentation_new_definition
    [Vlong Int64.one]continuation before world tuple after next observed eq_refl STEP)as OPERATION.
  destruct(gateway_presentation_new_operation _ _ _ _ _ runtime before world tuple after next observed protected READY OWNED OPERATION)
    as[FRAME[[NULL[PENDING COUNTS]]|[(object &offset &POINTER)[AFTER[CREDIT[ZERO[ONE CONTENTS]]]]]]];[contradiction|].
  destruct(gateway_presentation_credit_mints python objects decimal_float ledger
    (gateway_reference_result(gateway_reference_depth continuation))held reserved tuple world next
    WELL BUDGET VACANT HELD CREDIT(gateway_presentation_values _ _ _ _ _ _ _ _ FRAME)
    (gateway_presentation_privacy _ _ _ _ _ _ _ _ FRAME))
    as(minted &MINT &MINTED_WELL &MINTED_OWNER &SCOPE &MINTED_BUDGET &BALANCE &RETAINED).
  exists minted,object,offset;split;[exact POINTER|]. split;[exact MINT|]. split;[exact MINTED_WELL|]. split;[exact MINTED_OWNER|].
  split;[apply gateway_reference_result_binding|]. split;[exact SCOPE|]. split;[exact MINTED_BUDGET|].
  exact(conj AFTER(conj CONTENTS(conj ZERO(conj ONE(conj FRAME BALANCE))))).
Qed.

(* IncRef does not mutate an independently owned tuple. The input byte/object
   kind remains supplied by the source-created immutable argument producer. *)
Record gateway_presentation_reference_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (tuples:World->Values.val->option(list(option Values.val))):Prop:={
  gateway_presentation_incref_tuple:forall before world tuple contents child result after next observed,
    gateway_objects_ready(python world)(objects world)before ->tuples world tuple=Some contents ->
    (0<python_native_strong(python world)tuple)%nat ->python_live(python world)child ->
    gateway_presentation_immutable(objects world)child ->
    gateway_object_operation backend gateway_api_incref[child]before world result after next observed ->
    tuples next tuple=Some contents
}.

Lemma gateway_presentation_live_allocation python heap memory object offset:
  gateway_objects_ready python heap memory ->python_live python(Vptr object offset) ->python_runtime_owned python object.
Proof.
  intros READY[POSITIVE[value VALUE]].
  pose proof(proj2(proj2(proj2(proj1(proj1 READY))))(Vptr object offset)value VALUE POSITIVE)as[[actual[displacement[SAME OWNED]]]REST].
  inversion SAME;subst;exact OWNED.
Qed.

Definition gateway_presentation_argument_cell parameters array displacement child memory:Prop:=
  parameters!_values=Some(Vptr array displacement) /\parameters!_index=Some(Vint Int.zero) /\
  Mem.load Mptr memory array(Ptrofs.unsigned displacement)=Some child /\
  (Ptrofs.unsigned displacement+8<=Ptrofs.modulus)%Z.

Theorem gateway_actual_presentation_argument_credit {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples decimal_float
    (references:gateway_reference_runtime backend python objects)
    (metadata:gateway_presentation_reference_runtime backend python objects tuples)
    ledger held reserved context parameters tuple_ticket tuple contents array displacement child child_offset before world ignored after next observed:
  gateway_reference_ledger_well_formed ledger ->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat) ->
  gateway_reference_take(gateway_reference_cell array (Ptrofs.unsigned displacement))(gateway_reference_entries ledger)=None ->
  gateway_reference_held python objects decimal_float ledger held world ->
  gateway_objects_ready(python world)(objects world)before ->gateway_native_private(python world)array ->
  gateway_presentation_argument_cell parameters array displacement (Vptr child child_offset) before ->
  parameters!_arguments=Some tuple ->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_arguments)tuple_ticket tuple ->
  tuples world tuple=Some contents ->
  tuple<>Vptr child child_offset ->python_live(python world)(Vptr child child_offset) ->
  gateway_presentation_immutable(objects world)(Vptr child child_offset) ->
  gateway_step backend ge
    (gateway_live(Callstate python_incref_definition[Vptr child child_offset](plug_cont(gateway_presentation_incref_cont parameters)context) before)world)(gateway_primitive observed)
    (gateway_live(Returnstate ignored(plug_cont(gateway_presentation_incref_cont parameters)context)after)next) ->
  exists minted,
    gateway_reference_apply(gateway_reference_mint(gateway_reference_cell array (Ptrofs.unsigned displacement))(Vptr child child_offset))
      (gateway_reference_valid ledger)=gateway_reference_valid minted /\gateway_reference_ledger_well_formed minted /\
    gateway_reference_owns minted(gateway_reference_cell array (Ptrofs.unsigned displacement))(gateway_reference_next ledger)(Vptr child child_offset) /\
    gateway_reference_place_value ge(Returnstate ignored(plug_cont(gateway_presentation_incref_cont parameters)context)after)(gateway_reference_cell array (Ptrofs.unsigned displacement))(Vptr child child_offset) /\
    gateway_reference_scope python objects decimal_float minted held next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count minted pointer<=python_native_strong(python next)pointer)%nat) /\
    gateway_objects_ready(python next)(objects next)after /\
    tuples next tuple=Some contents /\python_strong(python next)tuple=python_strong(python world)tuple /\
    gateway_presentation_immutable(objects next)(Vptr child child_offset) /\
    python_private_frame(python world)before after /\
    (forall object,gateway_native_private(python world)object->gateway_native_private(python next)object) /\
    gateway_reference_balance(python world)(python next)ledger minted.
Proof.
  intros WELL BUDGET VACANT HELD READY NATIVE CELL ARGUMENTS TUPLE_TICKET TUPLE DIFFERENT LIVE IMMUTABLE STEP.
  destruct CELL as[VALUES[INDEX[LOAD NOWRAP]]].
  assert(TUPLE_OWNED:(0<python_native_strong(python world)tuple)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ TUPLE_TICKET);specialize(BUDGET tuple);lia. }
  assert(OPERATION:gateway_object_operation backend gateway_api_incref[Vptr child child_offset]before world ignored after next observed).
  { eapply gateway_object_operation_actual;[reflexivity|exact STEP]. }
  destruct(gateway_runtime_incref_objects _ _ _ references before world(Vptr child child_offset)ignored after next observed READY LIVE OPERATION)
    as[RETURN[AFTER[FRAME[PRIVACY[VALUE PRIVATE]]]]].
  destruct(gateway_presentation_credit_mints python objects decimal_float ledger(gateway_reference_cell array (Ptrofs.unsigned displacement))held reserved
    (Vptr child child_offset)world next WELL BUDGET VACANT HELD(gateway_incref_reference_credit _ _ _ _ _ RETURN)FRAME PRIVACY)
    as(minted &MINT &MINTED_WELL &MINTED_OWNER &SCOPE &MINTED_BUDGET &BALANCE &RETAINED).
  assert(CHILD_OWNED:python_runtime_owned(python world)child)by(eapply gateway_presentation_live_allocation;eassumption).
  destruct(python_incref_object _ _ _ _ _ RETURN)as(actual &child_displacement &SAME &MEMORY).
  inversion SAME;subst actual child_displacement.
  assert(NATIVE_FRAME:python_private_frame(python world)before after).
  { eapply Mem.unchanged_on_implies;[exact MEMORY|]. intros object position PRIVATE_OBJECT VALID.
    intro SAME_OBJECT;subst object;exact(PRIVATE_OBJECT CHILD_OWNED). }
  assert(AFTER_LOAD:Mem.load Mptr after array (Ptrofs.unsigned displacement)=Some(Vptr child child_offset)).
  { eapply Mem.load_unchanged_on;[exact NATIVE_FRAME|intros;exact NATIVE|exact LOAD]. }
  exists minted;split;[exact MINT|]. split;[exact MINTED_WELL|]. split;[exact MINTED_OWNER|].
  split;[exact AFTER_LOAD|]. split;[exact SCOPE|]. split;[exact MINTED_BUDGET|]. split;[exact AFTER|]. split.
  - eapply gateway_presentation_incref_tuple;[exact metadata|exact READY|exact TUPLE|exact TUPLE_OWNED|exact LIVE|exact IMMUTABLE|exact OPERATION].
  - split;[exact(proj1(python_incref_others _ _ _ _ _ RETURN tuple DIFFERENT))|]. split.
    + unfold gateway_presentation_immutable in *;rewrite VALUE;exact IMMUTABLE.
    + split;[exact NATIVE_FRAME|]. split;[|exact BALANCE].
      intros object PRIVATE_OBJECT;unfold gateway_native_private in *;rewrite(python_incref_heap _ _ _ _ _ RETURN);exact PRIVATE_OBJECT.
Qed.

Lemma gateway_presentation_release_credit {World}python objects decimal_float ledger owner ticket pointer held reserved world next:
  gateway_reference_ledger_well_formed ledger ->
  (forall value,(count_occ Val.eq reserved value+gateway_reference_count ledger value<=python_native_strong(python world)value)%nat) ->
  gateway_reference_owns ledger owner ticket pointer ->
  @gateway_reference_held World python objects decimal_float ledger held world ->
  (forall captured,In captured held->gateway_held_ticket captured<>ticket) ->
  gateway_presentation_debit(python world)(python next)pointer ->
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[] ->
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[] ->
  exists released,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid released /\
    gateway_reference_ledger_well_formed released /\gateway_reference_scope python objects decimal_float released held next /\
    (forall value,(count_occ Val.eq reserved value+gateway_reference_count released value<=python_native_strong(python next)value)%nat) /\
    gateway_reference_balance(python world)(python next)ledger released /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->gateway_reference_owns released place other value).
Proof.
  intros WELL BUDGET OWNED HELD DIFFERENT[DEBIT OTHERS]FRAME PRIVACY.
  assert(FIT:gateway_reference_counts_fit ledger(python world))by(intro value;specialize(BUDGET value);lia).
  destruct(gateway_reference_release_counts ledger owner ticket pointer(python world)(python next)WELL FIT OWNED DEBIT OTHERS)
    as(released &RELEASE &RELEASED_WELL &RELEASED_FIT &RETAINED).
  assert(BALANCE:gateway_reference_balance(python world)(python next)ledger released).
  { eapply gateway_reference_balance_release;[exact WELL|exact OWNED|exact RELEASE|exact DEBIT|].
    intros value OUTSIDE;apply OTHERS;intro SAME;apply OUTSIDE;subst value;left;reflexivity. }
  assert(RELEASED_HELD:gateway_reference_held python objects decimal_float released held next).
  { eapply gateway_reference_held_frame;[exact HELD|exact FIT|exact RELEASED_FIT| |exact FRAME|exact PRIVACY].
    intros captured MEMBER;destruct(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OLD]REST].
    exists place;apply RETAINED;[exact(DIFFERENT captured MEMBER)|exact OLD]. }
  exists released;split;[exact RELEASE|]. split;[exact RELEASED_WELL|]. split;[exact(conj RELEASED_FIT RELEASED_HELD)|]. split.
  - eapply gateway_reference_balance_reservations;[exact BUDGET|exact BALANCE].
  - split;assumption.
Qed.

Lemma gateway_presentation_keeps_immutable_argument {World}python objects decimal_float ledger final held captured child world next:
  @gateway_reference_scope World python objects decimal_float ledger held world ->
  gateway_reference_scope python objects decimal_float final held next ->In captured held ->
  gateway_object_reachable(objects world)(gateway_held_object captured)child ->gateway_presentation_immutable(objects world)child ->
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[] ->
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[] ->
  gateway_presentation_immutable(objects next)child /\gateway_object_reachable(objects next)(gateway_held_object captured)child.
Proof.
  intros[FIT HELD][FINAL_FIT FINAL_HELD]MEMBER REACHED IMMUTABLE FRAME PRIVACY.
  destruct(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OWNED][PRIVATE[DESTROY VIEW]]].
  destruct(proj1(Forall_forall _ _)FINAL_HELD captured MEMBER)as[[next_place NEXT_OWNED]REST].
  assert(ROOT:gateway_rooted(python world)(objects world)(gateway_held_object captured))by(eapply gateway_reference_owned_rooted;eassumption).
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)(gateway_held_object captured))by(eapply gateway_reference_owned_rooted;eassumption).
  destruct(gateway_private_tree_frame _ _ _ _ _ PRIVATE ROOT NEXT_ROOT FRAME PRIVACY child REACHED)as[_[_[VALUES AFTER_PRIVATE]]].
  split.
  - destruct IMMUTABLE as[[characters VALUE]|VALUE].
    + left;exists characters;apply VALUES;exact VALUE.
    + right;apply VALUES;exact VALUE.
  - pose proof(gateway_graph_snapshot_retained _ _ _ _ _ _ PRIVATE DESTROY ROOT NEXT_ROOT FRAME PRIVACY
      (gateway_graph_snapshot_refl _ _))as SNAPSHOT.
    eapply gateway_graph_snapshot_forward;[exact SNAPSHOT|exact REACHED].
Qed.

Theorem gateway_actual_presentation_argument_steal {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples storage decimal_float(runtime:gateway_presentation_runtime backend python objects tuples storage)
    ledger held reserved protected context parameters tuple_ticket tuple array displacement child child_offset ticket captured before world result after next observed:
  gateway_reference_ledger_well_formed ledger ->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat) ->
  gateway_reference_owns ledger(gateway_reference_cell array (Ptrofs.unsigned displacement))ticket(Vptr child child_offset) ->
  gateway_reference_scope python objects decimal_float ledger held world ->
  (forall current,In current held->gateway_held_ticket current<>ticket) ->In captured held ->
  gateway_object_reachable(objects world)(gateway_held_object captured)(Vptr child child_offset) ->
  gateway_objects_ready(python world)(objects world)before ->gateway_presentation_owned_region storage world before protected ->
  gateway_presentation_argument_cell parameters array displacement (Vptr child child_offset) before ->
  parameters!_arguments=Some tuple ->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_arguments)tuple_ticket tuple ->
  tuples world tuple=Some[None] ->python_live(python world)tuple ->
  python_strong(python world)tuple=1%nat ->
  python_live(python world)(Vptr child child_offset) ->gateway_presentation_immutable(objects world)(Vptr child child_offset) ->
  gateway_step backend ge
    (gateway_live(Callstate gateway_presentation_set_definition[tuple;Vlong Int64.zero;Vptr child child_offset](plug_cont(gateway_presentation_set_cont parameters)context) before)world)
    (gateway_primitive observed)(gateway_live(Returnstate result(plug_cont(gateway_presentation_set_cont parameters)context)after)next) ->
  exists released,
    result=Vint Int.zero /\
    gateway_reference_apply(gateway_reference_release(gateway_reference_cell array (Ptrofs.unsigned displacement))(Vptr child child_offset))
      (gateway_reference_valid ledger)=gateway_reference_valid released /\gateway_reference_ledger_well_formed released /\
    gateway_reference_scope python objects decimal_float released held next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count released pointer<=python_native_strong(python next)pointer)%nat) /\
    gateway_objects_ready(python next)(objects next)after /\tuples next tuple=Some[Some(Vptr child child_offset)] /\
    python_strong(python next)tuple=1%nat /\gateway_presentation_immutable(objects next)(Vptr child child_offset) /\
    gateway_object_reachable(objects next)(gateway_held_object captured)(Vptr child child_offset) /\
    gateway_presentation_frame python objects storage protected before world after next /\
    gateway_reference_balance(python world)(python next)ledger released /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->gateway_reference_owns released place other value).
Proof.
  intros WELL BUDGET OWNED SCOPE DIFFERENT CAPTURED REACHED READY PROTECTED CELL ARGUMENTS TUPLE_TICKET CONTENTS TUPLE_LIVE UNIQUE CHILD_LIVE IMMUTABLE STEP.
  destruct CELL as[VALUES[INDEX[LOAD NOWRAP]]].
  assert(TUPLE_OWNED:(0<python_native_strong(python world)tuple)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ TUPLE_TICKET);specialize(BUDGET tuple);lia. }
  assert(CHILD_OWNED:(0<python_native_strong(python world)(Vptr child child_offset))%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(BUDGET(Vptr child child_offset));lia. }
  pose proof(gateway_presentation_actual_operation backend ge gateway_presentation_tuple_set gateway_presentation_set_definition
    [tuple;Vlong Int64.zero;Vptr child child_offset](plug_cont(gateway_presentation_set_cont parameters)context) before world result after next observed eq_refl STEP)as OPERATION.
  destruct(gateway_presentation_set_operation _ _ _ _ _ runtime before world tuple(Vptr child child_offset)result after next observed protected
    READY PROTECTED CONTENTS TUPLE_LIVE TUPLE_OWNED UNIQUE CHILD_LIVE CHILD_OWNED IMMUTABLE OPERATION)
    as[RESULT[AFTER[FRAME[DEBIT[INSTALLED[CHILD_COUNT TUPLE_COUNT]]]]]].
  destruct(gateway_presentation_release_credit python objects decimal_float ledger(gateway_reference_cell array (Ptrofs.unsigned displacement))ticket(Vptr child child_offset)
    held reserved world next WELL BUDGET OWNED(proj2 SCOPE)DIFFERENT DEBIT(gateway_presentation_values _ _ _ _ _ _ _ _ FRAME)
    (gateway_presentation_privacy _ _ _ _ _ _ _ _ FRAME))
    as(released &RELEASE &RELEASED_WELL &RELEASED_SCOPE &RELEASED_BUDGET &BALANCE &RETAINED).
  destruct(gateway_presentation_keeps_immutable_argument python objects decimal_float ledger released held captured(Vptr child child_offset)world next
    SCOPE RELEASED_SCOPE CAPTURED REACHED IMMUTABLE(gateway_presentation_values _ _ _ _ _ _ _ _ FRAME)
    (gateway_presentation_privacy _ _ _ _ _ _ _ _ FRAME))as[AFTER_IMMUTABLE AFTER_REACHED].
  exists released;exact(conj RESULT(conj RELEASE(conj RELEASED_WELL(conj RELEASED_SCOPE(conj RELEASED_BUDGET
    (conj AFTER(conj INSTALLED(conj TUPLE_COUNT(conj AFTER_IMMUTABLE(conj AFTER_REACHED(conj FRAME(conj BALANCE RETAINED)))))))))))).
Qed.

Theorem gateway_actual_presentation_callback_credit {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples storage decimal_float(runtime:gateway_presentation_runtime backend python objects tuples storage)
    ledger held reserved protected continuation callable tuple child captured before world result after next observed:
  gateway_reference_ledger_well_formed ledger ->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat) ->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth continuation))(gateway_reference_entries ledger)=None ->
  gateway_reference_scope python objects decimal_float ledger held world ->In captured held ->
  gateway_object_reachable(objects world)(gateway_held_object captured)child ->
  gateway_objects_ready(python world)(objects world)before ->gateway_presentation_owned_region storage world before protected ->
  python_live(python world)callable ->python_live(python world)tuple ->
  (0<python_native_strong(python world)callable)%nat ->(0<python_native_strong(python world)tuple)%nat ->
  tuples world tuple=Some[Some child] ->gateway_presentation_immutable(objects world)child ->
  gateway_step backend ge(gateway_live(Callstate gateway_presentation_call_definition[callable;tuple]continuation before)world)
    (gateway_primitive observed)(gateway_live(Returnstate result continuation after)next) ->result<>Vnullptr ->
  exists minted object offset,
    result=Vptr object offset /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_result(gateway_reference_depth continuation))result)
      (gateway_reference_valid ledger)=gateway_reference_valid minted /\gateway_reference_ledger_well_formed minted /\
    gateway_reference_owns minted(gateway_reference_result(gateway_reference_depth continuation))(gateway_reference_next ledger)result /\
    gateway_reference_place_value ge(Returnstate result continuation after)(gateway_reference_result(gateway_reference_depth continuation))result /\
    gateway_reference_scope python objects decimal_float minted held next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count minted pointer<=python_native_strong(python next)pointer)%nat) /\
    gateway_objects_ready(python next)(objects next)after /\python_live(python next)result /\
    tuples next tuple=Some[Some child] /\gateway_presentation_immutable(objects next)child /\
    gateway_object_reachable(objects next)(gateway_held_object captured)child /\
    gateway_presentation_frame python objects storage protected before world after next /\
    gateway_reference_balance(python world)(python next)ledger minted.
Proof.
  intros WELL BUDGET VACANT SCOPE CAPTURED REACHED READY PROTECTED CALLABLE TUPLE CALLABLE_OWNED TUPLE_OWNED CONTENTS IMMUTABLE STEP NONNULL.
  pose proof(gateway_presentation_actual_operation backend ge gateway_presentation_call gateway_presentation_call_definition
    [callable;tuple]continuation before world result after next observed eq_refl STEP)as OPERATION.
  destruct(gateway_presentation_call_operation _ _ _ _ _ runtime before world callable tuple child result after next observed protected
    READY PROTECTED CALLABLE TUPLE CALLABLE_OWNED TUPLE_OWNED CONTENTS IMMUTABLE OPERATION)
    as[FRAME[CONTENTS_AFTER[[NULL[PENDING COUNTS]]|[(object &offset &POINTER)[AFTER[LIVE CREDIT]]]]]];[contradiction|].
  destruct(gateway_presentation_credit_mints python objects decimal_float ledger(gateway_reference_result(gateway_reference_depth continuation))
    held reserved result world next WELL BUDGET VACANT(proj2 SCOPE)CREDIT(gateway_presentation_values _ _ _ _ _ _ _ _ FRAME)
    (gateway_presentation_privacy _ _ _ _ _ _ _ _ FRAME))
    as(minted &MINT &MINTED_WELL &MINTED_OWNER &MINTED_SCOPE &MINTED_BUDGET &BALANCE &RETAINED).
  destruct(gateway_presentation_keeps_immutable_argument python objects decimal_float ledger minted held captured child world next
    SCOPE MINTED_SCOPE CAPTURED REACHED IMMUTABLE(gateway_presentation_values _ _ _ _ _ _ _ _ FRAME)
    (gateway_presentation_privacy _ _ _ _ _ _ _ _ FRAME))as[IMMUTABLE_AFTER REACHED_AFTER].
  exists minted,object,offset;split;[exact POINTER|]. split;[exact MINT|]. split;[exact MINTED_WELL|]. split;[exact MINTED_OWNER|].
  split;[apply gateway_reference_result_binding|]. split;[exact MINTED_SCOPE|]. split;[exact MINTED_BUDGET|].
  exact(conj AFTER(conj LIVE(conj CONTENTS_AFTER(conj IMMUTABLE_AFTER(conj REACHED_AFTER(conj FRAME BALANCE)))))).
Qed.

Theorem gateway_actual_presentation_tuple_release {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples storage decimal_float(runtime:gateway_presentation_runtime backend python objects tuples storage)
    ledger held reserved protected context parameters ticket tuple contents before world ignored after next observed:
  gateway_reference_ledger_well_formed ledger ->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat) ->
  gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_arguments)ticket tuple ->
  gateway_reference_held python objects decimal_float ledger held world ->
  (forall captured,In captured held->gateway_held_ticket captured<>ticket) ->
  gateway_objects_ready(python world)(objects world)before ->gateway_presentation_owned_region storage world before protected ->
  tuples world tuple=Some contents ->
  (contents=[None] \/exists child,contents=[Some child] /\gateway_presentation_immutable(objects world)child) ->
  parameters!_arguments=Some tuple ->
  gateway_step backend ge(gateway_live(Callstate gateway_presentation_release_definition[tuple](plug_cont(gateway_presentation_release_cont parameters)context) before)world)
    (gateway_primitive observed)(gateway_live(Returnstate ignored(plug_cont(gateway_presentation_release_cont parameters)context)after)next) ->
  exists released,
    gateway_reference_apply(gateway_reference_release(gateway_reference_temporary(gateway_reference_depth context)_arguments)tuple)(gateway_reference_valid ledger)=gateway_reference_valid released /\
    gateway_reference_ledger_well_formed released /\gateway_reference_scope python objects decimal_float released held next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count released pointer<=python_native_strong(python next)pointer)%nat) /\
    gateway_objects_ready(python next)(objects next)after /\
    gateway_presentation_frame python objects storage protected before world after next /\
    gateway_reference_balance(python world)(python next)ledger released /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->gateway_reference_owns released place other value).
Proof.
  intros WELL BUDGET OWNED HELD DIFFERENT READY PROTECTED CONTENTS CHILDREN ARGUMENTS STEP.
  assert(POSITIVE:(0<python_native_strong(python world)tuple)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(BUDGET tuple);lia. }
  pose proof(gateway_presentation_actual_operation backend ge gateway_presentation_tuple_release gateway_presentation_release_definition
    [tuple](plug_cont(gateway_presentation_release_cont parameters)context) before world ignored after next observed eq_refl STEP)as OPERATION.
  destruct(gateway_presentation_release_operation _ _ _ _ _ runtime before world tuple contents ignored after next observed protected
    (GatewayAttachedReferences.gateway_normal_attached _ _ _ READY)PROTECTED CONTENTS CHILDREN POSITIVE OPERATION)
    as[FRAME[PENDING DEBIT]].
  destruct(gateway_presentation_release_credit python objects decimal_float ledger(gateway_reference_temporary(gateway_reference_depth context)_arguments)ticket tuple held reserved world next WELL BUDGET OWNED HELD
    DIFFERENT DEBIT(gateway_presentation_values _ _ _ _ _ _ _ _ FRAME)(gateway_presentation_privacy _ _ _ _ _ _ _ _ FRAME))
    as(released &RELEASE &RELEASED_WELL &SCOPE &RELEASED_BUDGET &BALANCE &RETAINED).
  assert(AFTER:gateway_objects_ready(python next)(objects next)after).
  { destruct(gateway_presentation_attached _ _ _ _ _ _ _ _ FRAME)as[VALID GIL].
    split;[exact VALID|]. split;[exact GIL|]. rewrite PENDING;exact(proj2(proj2 READY)). }
  exists released;exact(conj RELEASE(conj RELEASED_WELL(conj SCOPE(conj RELEASED_BUDGET(conj AFTER(conj FRAME(conj BALANCE RETAINED))))))).
Qed.
