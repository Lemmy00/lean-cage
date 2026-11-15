(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The current source array and older received graph survive the
   actual callback helper. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame GatewayValueOwnership GatewayObjectDiscipline GatewayObjectThreads
  GatewayThreadRuntime GatewayStreamInterface GatewayNativeRegions GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceBalance GatewayPresentationRuntime GatewayPresentationCredits
  GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Record gateway_presentation_context {World}(python:World->python_world)(objects:World->gateway_object_heap)
    decimal_float ledger held reserved captured protected source array displacement child memory world:Prop:={
  gateway_presentation_context_ready:gateway_objects_ready(python world)(objects world)memory;
  gateway_presentation_context_scope:gateway_reference_scope python objects decimal_float ledger held world;
  gateway_presentation_context_budget:forall pointer,
    (count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat;
  gateway_presentation_context_owned:gateway_presentation_owned_region
    (fun current object=>gateway_native_private(python current)object)world memory protected;
  gateway_presentation_context_frame:Mem.unchanged_on protected source memory;
  gateway_presentation_context_array:Mem.load Mptr memory array(Ptrofs.unsigned displacement)=Some child;
  gateway_presentation_context_immutable:gateway_presentation_immutable(objects world)child;
  gateway_presentation_context_reached:gateway_object_reachable(objects world)(gateway_held_object captured)child
}.

Theorem gateway_presentation_context_effect {World}python objects decimal_float ledger final held reserved captured
    protected source array displacement child before world after next:
  @gateway_presentation_context World python objects decimal_float ledger held reserved captured protected source
    array displacement child before world ->In captured held ->
  (forall position,(Ptrofs.unsigned displacement<=position<Ptrofs.unsigned displacement+8)%Z->protected array position) ->
  gateway_objects_ready(python next)(objects next)after ->
  gateway_reference_scope python objects decimal_float final held next ->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat) ->
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[] ->
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[] ->
  Mem.unchanged_on protected before after ->
  (forall object position,protected object position->gateway_native_private(python next)object) ->
  gateway_presentation_context python objects decimal_float final held reserved captured protected source array displacement child after next.
Proof.
  intros CONTEXT CAPTURED ARRAY READY SCOPE BUDGET VALUES PRIVACY FRAME STORAGE.
  destruct CONTEXT as[OLD_READY OLD_SCOPE OLD_BUDGET OWNED ORIGINAL LOAD IMMUTABLE REACHED].
  destruct(gateway_presentation_keeps_immutable_argument python objects decimal_float ledger final held captured child world next
    OLD_SCOPE SCOPE CAPTURED REACHED IMMUTABLE VALUES PRIVACY)as[NEXT_IMMUTABLE NEXT_REACHED].
  constructor;[exact READY|exact SCOPE|exact BUDGET| | | |exact NEXT_IMMUTABLE|exact NEXT_REACHED].
  - intros object position MEMBER;split;[eapply STORAGE;exact MEMBER|].
    eapply Mem.perm_unchanged_on;[exact FRAME|exact MEMBER|exact(proj2(OWNED object position MEMBER))].
  - eapply Mem.unchanged_on_trans;eassumption.
  - eapply Mem.load_unchanged_on;[exact FRAME| |exact LOAD].
    intros position RANGE;apply ARRAY;change(Ptrofs.unsigned displacement<=position<Ptrofs.unsigned displacement+8)%Z in RANGE;exact RANGE.
Qed.

Theorem gateway_presentation_context_from_frame {World}python objects decimal_float ledger final held reserved captured
    protected source array displacement child before world after next:
  @gateway_presentation_context World python objects decimal_float ledger held reserved captured protected source
    array displacement child before world ->In captured held ->
  (forall position,(Ptrofs.unsigned displacement<=position<Ptrofs.unsigned displacement+8)%Z->protected array position) ->
  gateway_objects_ready(python next)(objects next)after ->
  gateway_reference_scope python objects decimal_float final held next ->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat) ->
  gateway_presentation_frame python objects(fun current object=>gateway_native_private(python current)object)
    protected before world after next ->
  gateway_presentation_context python objects decimal_float final held reserved captured protected source array displacement child after next.
Proof.
  intros CONTEXT CAPTURED ARRAY READY SCOPE BUDGET FRAME.
  eapply gateway_presentation_context_effect;[exact CONTEXT|exact CAPTURED|exact ARRAY|exact READY|exact SCOPE|exact BUDGET|
    exact(gateway_presentation_values _ _ _ _ _ _ _ _ FRAME)|exact(gateway_presentation_privacy _ _ _ _ _ _ _ _ FRAME)|
    exact(gateway_presentation_memory _ _ _ _ _ _ _ _ FRAME)|exact(gateway_presentation_storage _ _ _ _ _ _ _ _ FRAME)].
Qed.

Theorem gateway_presentation_context_counts {World}python objects decimal_float ledger final held reserved captured
    protected source array displacement child memory world:
  @gateway_presentation_context World python objects decimal_float ledger held reserved captured protected source
    array displacement child memory world ->
  gateway_reference_scope python objects decimal_float final held world ->
  (forall pointer,gateway_reference_count final pointer=gateway_reference_count ledger pointer) ->
  gateway_presentation_context python objects decimal_float final held reserved captured protected source array displacement child memory world.
Proof.
  intros[READY SCOPE BUDGET OWNED FRAME LOAD IMMUTABLE REACHED]AFTER COUNTS.
  constructor;try assumption;intro pointer;rewrite COUNTS;apply BUDGET.
Qed.

Theorem gateway_presentation_context_ambient {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger held reserved captured protected source array displacement child:
  In captured held ->
  (forall position,(Ptrofs.unsigned displacement<=position<Ptrofs.unsigned displacement+8)%Z->protected array position) ->
  gateway_ambient_closed backend(gateway_presentation_context python objects decimal_float ledger held reserved captured
    protected source array displacement child).
Proof.
  intros CAPTURED ARRAY before world after next CONTEXT AMBIENT.
  pose proof(gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT)as READY.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next READY AMBIENT)
    as[NORMAL[ACCESS FRAME]].
  pose proof(@gateway_reference_thread_ambient World Event backend _ stable
    (gateway_python_discipline python objects detached)heap_allocation python objects references None before world after next READY AMBIENT)as EFFECT.
  assert(SCOPE:gateway_reference_scope python objects decimal_float ledger held next).
  { eapply gateway_reference_scope_thread_effect;[exact(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT)|exact EFFECT]. }
  assert(REGION_FRAME:Mem.unchanged_on protected before after).
  { eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros object position MEMBER LIVE;split;[left;exact(proj1(gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT object position MEMBER))|
      unfold gateway_native_no_output;tauto]. }
  eapply gateway_presentation_context_effect;[exact CONTEXT|exact CAPTURED|exact ARRAY|exact NORMAL|exact SCOPE| | | |exact REGION_FRAME|].
  - intro pointer;pose proof(gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT pointer).
    pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia.
  - exact(gateway_reference_thread_values _ _ _ _ EFFECT).
  - exact(gateway_reference_thread_privacy _ _ _ _ EFFECT).
  - intros object position MEMBER;destruct(gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT object position MEMBER)as[NATIVE READABLE].
    apply(proj1 ACCESS);[eapply Mem.perm_valid_block;exact READABLE|exact NATIVE].
Qed.

Definition gateway_presentation_tuple_context {World}(python:World->python_world)(objects:World->gateway_object_heap)
    (tuples:World->val->option(list(option val)))decimal_float ledger held reserved captured protected source
    array displacement child tuple contents(unique:bool)memory world:Prop:=
  gateway_presentation_context python objects decimal_float ledger held reserved captured protected source array displacement child memory world /\
  tuples world tuple=Some contents /\(0<python_native_strong(python world)tuple)%nat /\
  (unique=true->python_strong(python world)tuple=1%nat).

Theorem gateway_presentation_tuple_context_counts {World}python objects tuples decimal_float ledger final held reserved captured
    protected source array displacement child tuple contents unique memory world:
  @gateway_presentation_tuple_context World python objects tuples decimal_float ledger held reserved captured protected source
    array displacement child tuple contents unique memory world ->
  gateway_reference_scope python objects decimal_float final held world ->
  (forall pointer,gateway_reference_count final pointer=gateway_reference_count ledger pointer) ->
  gateway_presentation_tuple_context python objects tuples decimal_float final held reserved captured protected source
    array displacement child tuple contents unique memory world.
Proof.
  intros[CONTEXT REST]SCOPE COUNTS;split;[eapply gateway_presentation_context_counts;eassumption|exact REST].
Qed.

Theorem gateway_presentation_tuple_context_ambient {World Event}(backend:gateway_backend World Event)
    python objects tuples decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (presentation:gateway_presentation_runtime backend python objects tuples(fun current object=>gateway_native_private(python current)object))
    ledger held reserved captured protected source array displacement child tuple contents unique:
  In captured held ->
  (forall position,(Ptrofs.unsigned displacement<=position<Ptrofs.unsigned displacement+8)%Z->protected array position) ->
  gateway_ambient_closed backend(gateway_presentation_tuple_context python objects tuples decimal_float ledger held reserved captured
    protected source array displacement child tuple contents unique).
Proof.
  intros CAPTURED ARRAY before world after next[CONTEXT[CONTENTS[OWNED UNIQUE]]]AMBIENT.
  assert(READY:gateway_objects_ready(python world)(objects world)before)
    by(exact(gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT)).
  destruct(gateway_presentation_tuple_ambient _ _ _ _ _ presentation before world after next tuple contents
    (GatewayAttachedReferences.gateway_normal_attached _ _ _ READY)CONTENTS OWNED AMBIENT)as[AFTER STRONG].
  split;[eapply gateway_presentation_context_ambient;eassumption|]. split;[exact AFTER|]. split.
  - pose proof(@gateway_reference_thread_ambient World Event backend _ stable
      (gateway_python_discipline python objects detached)heap_allocation python objects references None before world after next READY AMBIENT)as EFFECT.
    pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT tuple);lia.
  - intro SAME;rewrite STRONG;apply UNIQUE;exact SAME.
Qed.

Lemma gateway_presentation_positive_live python objects memory pointer:
  gateway_objects_ready python objects memory ->(0<python_native_strong python pointer)%nat ->python_live python pointer.
Proof.
  intros READY OWNED;apply(proj1(proj2(proj1 READY)));constructor;exact OWNED.
Qed.

Lemma gateway_presentation_positive_pointer python objects memory object offset:
  gateway_objects_ready python objects memory ->(0<python_native_strong python(Vptr object offset))%nat ->
  Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true.
Proof.
  intros READY OWNED.
  destruct(proj2(proj2(proj2(proj2(proj1 READY))))(Vptr object offset)(gateway_direct_root _ _ _ OWNED))
    as[actual[displacement[SAME POINTER]]];inversion SAME;subst;exact POINTER.
Qed.

Lemma gateway_presentation_context_child_live {World}python objects decimal_float ledger held reserved captured
    protected source array displacement child memory world:
  @gateway_presentation_context World python objects decimal_float ledger held reserved captured protected source
    array displacement child memory world ->In captured held ->python_live(python world)child.
Proof.
  intros[READY[SCOPE HELD]BUDGET OWNED FRAME LOAD IMMUTABLE REACHED]CAPTURED.
  destruct(proj1(Forall_forall _ _)HELD captured CAPTURED)as[[place TICKET]REST].
  assert(ROOT:gateway_rooted(python world)(objects world)(gateway_held_object captured))
    by(eapply gateway_reference_owned_rooted;eassumption).
  assert(CHILD:gateway_rooted(python world)(objects world)child).
  { eapply gateway_reachable_rooted;eassumption. }
  apply(proj1(proj2(proj1 READY)));exact CHILD.
Qed.
