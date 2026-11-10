(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Borrowed parser outputs gain native roots before callbacks. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayRuntime GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_argument_count(values:list val)object:=
  if Val.eq object Vnullptr then 0%nat else count_occ Val.eq values object.
Definition gateway_argument_live(python:python_world)object:=object=Vnullptr \/python_live python object.

(* Actual Python callbacks occur inside the individual SDK operations that can
   invoke them. Between those operations this attached native thread owns the
   GIL; asynchronous C signal bookkeeping does not execute a Python callback. *)
Record gateway_quiet_gil {World Event}(backend:gateway_backend World Event)(python:World->python_world):Prop:={
  gateway_quiet_gil_ambient:forall before world after next,
    python_gil(python world)=true->python_world_valid(python world)before->
    gateway_interference backend before world after next->
    python_gil(python next)=true /\python_pending(python next)=python_pending(python world) /\
    python_values(python next)=python_values(python world) /\
    python_strong(python next)=python_strong(python world) /\
    python_native_strong(python next)=python_native_strong(python world) /\
    (forall block,Mem.valid_block before block->
      (python_runtime_owned(python next)block<->python_runtime_owned(python world)block)) /\
    python_world_valid(python next)after /\python_private_frame(python world)before after /\
    (forall object block offset,python_live(python world)object->object=Vptr block offset->
      Mem.weak_valid_pointer before block(Ptrofs.unsigned offset)=true->
      Mem.weak_valid_pointer after block(Ptrofs.unsigned offset)=true)
}.

Record gateway_argument_context {World}(python:World->python_world)array offset values processed original memory world:Prop:={
  gateway_argument_gil:python_gil(python world)=true;
  gateway_argument_clear:python_pending(python world)=None;
  gateway_argument_valid:python_world_valid(python world)memory;
  gateway_argument_private:~python_runtime_owned(python world)array;
  gateway_argument_array_live:Mem.valid_block memory array;
  gateway_argument_bound:Ptrofs.unsigned offset+8*Z.of_nat(length values)<=Ptrofs.modulus;
  gateway_argument_cells:forall index object,nth_error values index=Some object->
    Mem.load Mptr memory array(Ptrofs.unsigned offset+8*Z.of_nat index)=Some object;
  gateway_argument_objects:Forall(gateway_argument_live(python world))values;
  gateway_argument_addresses:forall object block pointer,In object values->object=Vptr block pointer->
    Mem.weak_valid_pointer memory block(Ptrofs.unsigned pointer)=true;
  gateway_argument_native:forall object,
    (python_native_strong original object+gateway_argument_count processed object<=python_native_strong(python world)object)%nat
}.

Section ArgumentContext.
Context {World Event}(backend:gateway_backend World Event)(python:World->python_world).
Context(quiet:gateway_quiet_gil backend python).

Lemma gateway_argument_context_ambient array offset values processed original:
  gateway_ambient_closed backend(gateway_argument_context python array offset values processed original).
Proof.
  intros before world after next[GIL CLEAR VALID PRIVATE LIVE BOUND CELLS OBJECTS ADDRESSES NATIVE]INTERFERENCE.
  destruct(gateway_quiet_gil_ambient _ _ quiet _ _ _ _ GIL VALID INTERFERENCE)
    as[NEXT_GIL[PENDING[DESCRIPTIONS[STRONG[NATIVE_COUNTS[HEAP[NEXT_VALID[FRAME ADDRESS_FRAME]]]]]]]].
  constructor.
  - exact NEXT_GIL.
  - rewrite PENDING;exact CLEAR.
  - exact NEXT_VALID.
  - intro OWNED;apply PRIVATE;apply(proj1(HEAP array LIVE));exact OWNED.
  - eapply Mem.valid_block_unchanged_on;eassumption.
  - exact BOUND.
  - intros index object SELECTED;eapply Mem.load_unchanged_on;[exact FRAME| |apply CELLS;exact SELECTED].
    intros position RANGE;exact PRIVATE.
  - eapply Forall_impl;[|exact OBJECTS]. intros object[NULL|[ROOT VALUE]];[left;exact NULL|right].
    split;[rewrite STRONG;exact ROOT|rewrite DESCRIPTIONS;exact VALUE].
  - intros object block pointer MEMBER POINTER;eapply ADDRESS_FRAME.
    + rewrite Forall_forall in OBJECTS;destruct(OBJECTS object MEMBER)as[NULL|OBJECT].
      * rewrite POINTER in NULL;discriminate.
      * exact OBJECT.
    + exact POINTER.
    + eapply ADDRESSES;eassumption.
  - intros object;rewrite NATIVE_COUNTS;apply NATIVE.
Qed.

End ArgumentContext.

Lemma gateway_argument_live_pointer python memory object:
  python_world_valid python memory->python_live python object->exists block offset,object=Vptr block offset /\
    python_runtime_owned python block.
Proof.
  intros[_[_[_ OWNED]]][STRONG[value DESCRIPTION]].
  destruct(OWNED object value DESCRIPTION STRONG)as[POINTER REST];exact POINTER.
Qed.

Lemma gateway_incref_live before python object next after other:
  python_incref_return python object before next after->python_live python other->python_live next other.
Proof.
  intros RETURN[STRONG DESCRIPTION];split.
  - destruct(Val.eq other object)as[SAME|DIFFERENT].
    + subst other;rewrite(python_incref_count _ _ _ _ _ RETURN);lia.
    + rewrite(proj1(python_incref_others _ _ _ _ _ RETURN other DIFFERENT));exact STRONG.
  - rewrite(python_incref_values _ _ _ _ _ RETURN);exact DESCRIPTION.
Qed.

Lemma gateway_weak_pointer_permissions before after block offset:
  (forall block offset kind permission,
    Mem.perm before block offset kind permission<->Mem.perm after block offset kind permission)->
  Mem.weak_valid_pointer before block offset=true->Mem.weak_valid_pointer after block offset=true.
Proof.
  intros PERMISSIONS;rewrite !Mem.weak_valid_pointer_spec,!Mem.valid_pointer_nonempty_perm.
  intros[VALID|VALID];[left|right];apply(proj1(PERMISSIONS _ _ _ _));exact VALID.
Qed.

Lemma gateway_argument_context_incref {World}(python:World->python_world)
    array offset values processed original before world object after next:
  gateway_argument_context python array offset values processed original before world->
  python_live(python world)object->
  python_incref_return(python world)object before(python next)after->
  gateway_argument_context python array offset values(processed++[object])original after next.
Proof.
  intros[GIL CLEAR VALID PRIVATE LIVE BOUND CELLS OBJECTS ADDRESSES NATIVE]OBJECT RETURN.
  destruct(gateway_argument_live_pointer _ _ _ VALID OBJECT)as[object_block[object_offset[POINTER OWNED]]].
  assert(SEPARATE:array<>object_block)by(intro SAME;subst array;contradiction).
  destruct(python_incref_object _ _ _ _ _ RETURN)as[actual[actual_offset[ACTUAL FRAME]]].
  assert(SAME:actual=object_block)by congruence;subst actual.
  constructor.
  - exact(python_incref_next_gil _ _ _ _ _ RETURN).
  - rewrite(python_incref_pending _ _ _ _ _ RETURN);exact CLEAR.
  - exact(python_incref_next_valid _ _ _ _ _ RETURN).
  - rewrite(python_incref_heap _ _ _ _ _ RETURN);exact PRIVATE.
  - eapply Mem.valid_block_unchanged_on;eassumption.
  - exact BOUND.
  - intros index other SELECTED;eapply Mem.load_unchanged_on;[exact FRAME| |apply CELLS;exact SELECTED].
    intros position RANGE;exact SEPARATE.
  - eapply Forall_impl;[|exact OBJECTS]. intros other[NULL|OTHER];[left;exact NULL|].
    right;eapply gateway_incref_live;eassumption.
  - intros other block pointer MEMBER POINTER0;eapply gateway_weak_pointer_permissions.
    + exact(python_incref_permissions _ _ _ _ _ RETURN).
    + eapply ADDRESSES;eassumption.
  - intros other.
    destruct(Val.eq other Vnullptr)as[NULL|NONNULL].
    + subst other;assert(DIFFERENT:Vnullptr<>object)by(rewrite POINTER;discriminate).
      rewrite(proj2(python_incref_others _ _ _ _ _ RETURN Vnullptr DIFFERENT)).
      specialize(NATIVE Vnullptr);unfold gateway_argument_count in *;
        destruct(Val.eq Vnullptr Vnullptr);[exact NATIVE|contradiction].
    + unfold gateway_argument_count in *;destruct(Val.eq other Vnullptr);[contradiction|].
      rewrite count_occ_app;cbn.
      destruct(Val.eq other object)as[EQUAL|DIFFERENT].
      * subst other;destruct(Val.eq object object);[|contradiction].
        rewrite(python_incref_native _ _ _ _ _ RETURN);specialize(NATIVE object).
        destruct(Val.eq object Vnullptr);[contradiction|lia].
      * destruct(Val.eq object other);[congruence|].
        rewrite(proj2(python_incref_others _ _ _ _ _ RETURN other DIFFERENT));specialize(NATIVE other).
        destruct(Val.eq other Vnullptr);[contradiction|lia].
Qed.

Lemma gateway_argument_context_initial {World}(python:World->python_world)array offset values memory world:
  python_gil(python world)=true->python_pending(python world)=None->python_world_valid(python world)memory->
  ~python_runtime_owned(python world)array->Mem.valid_block memory array->
  Ptrofs.unsigned offset+8*Z.of_nat(length values)<=Ptrofs.modulus->
  (forall index object,nth_error values index=Some object->
    Mem.load Mptr memory array(Ptrofs.unsigned offset+8*Z.of_nat index)=Some object)->
  Forall(gateway_argument_live(python world))values->
  (forall object block pointer,In object values->object=Vptr block pointer->
    Mem.weak_valid_pointer memory block(Ptrofs.unsigned pointer)=true)->
  gateway_argument_context python array offset values[](python world)memory world.
Proof.
  intros;constructor;try assumption. intros object;unfold gateway_argument_count;destruct Val.eq;cbn;lia.
Qed.

Lemma gateway_argument_count_null values object:
  gateway_argument_count(values++[Vnullptr])object=gateway_argument_count values object.
Proof.
  unfold gateway_argument_count;destruct(Val.eq object Vnullptr)as[NULL|NONNULL];[reflexivity|].
  rewrite count_occ_app;cbn;destruct(Val.eq Vnullptr object);[congruence|lia].
Qed.

Lemma gateway_argument_context_skip_null {World}(python:World->python_world)
    array offset values processed original memory world:
  gateway_argument_context python array offset values processed original memory world->
  gateway_argument_context python array offset values(processed++[Vnullptr])original memory world.
Proof.
  intros[GIL CLEAR VALID PRIVATE LIVE BOUND CELLS OBJECTS ADDRESSES NATIVE];constructor;try assumption.
  intro object;rewrite gateway_argument_count_null;apply NATIVE.
Qed.

Definition gateway_argument_pointer object:Prop:=
  object=Vnullptr \/exists block offset,object=Vptr block offset.

Lemma gateway_argument_context_pointers {World}(python:World->python_world)
    array offset values processed original memory world:
  gateway_argument_context python array offset values processed original memory world->
  Forall gateway_argument_pointer values.
Proof.
  intro CONTEXT.
  eapply Forall_impl;[|exact(@gateway_argument_objects World python array offset values processed original memory world CONTEXT)].
  intros object[NULL|LIVE];[left;exact NULL|right].
  destruct(gateway_argument_live_pointer _ _ _
    (@gateway_argument_valid World python array offset values processed original memory world CONTEXT)LIVE)
    as[block[offset0[POINTER OWNED]]];exists block,offset0;exact POINTER.
Qed.

Lemma gateway_argument_context_member {World}(python:World->python_world)
    array offset values processed original memory world object:
  gateway_argument_context python array offset values processed original memory world->
  In object values->object<>Vnullptr->python_live(python world)object.
Proof.
  intros CONTEXT MEMBER NONNULL.
  pose proof(@gateway_argument_objects World python array offset values processed original memory world CONTEXT)as LIVE.
  rewrite Forall_forall in LIVE;destruct(LIVE object MEMBER);[contradiction|assumption].
Qed.

Theorem gateway_arguments_independently_rooted {World}(python:World->python_world)
    array offset values original memory world:
  gateway_argument_context python array offset values values original memory world->
  forall object,In object values->object<>Vnullptr->(0<python_native_strong(python world)object)%nat.
Proof.
  intros CONTEXT object MEMBER NONNULL.
  pose proof(@gateway_argument_native World python array offset values values original memory world CONTEXT object)as NATIVE.
  assert(POSITIVE:(0<gateway_argument_count values object)%nat).
  { unfold gateway_argument_count;destruct(Val.eq object Vnullptr);[contradiction|].
    apply count_occ_In;exact MEMBER. }
  lia.
Qed.
