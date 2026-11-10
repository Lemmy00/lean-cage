(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The actual recursive decoder allocates its own two word slots. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps ReceiverAllocation LocalAccess.
From HostGateway Require Import GatewaySource GatewayFunctionEntry GatewayFrames GatewayWordsMemory GatewayWordInputs
  GatewayStreamInterface GatewayStreamMemory.
Import ListNotations.
Open Scope Z_scope.

Record gateway_value_arguments :Type:={
  gateway_value_stream:Values.val;
  gateway_value_depth:int
}.
Definition gateway_value_arguments_list arguments:=
  [gateway_value_stream arguments;Vint(gateway_value_depth arguments)].
Definition gateway_value_parameters arguments:=
  PTree.set _depth(Vint(gateway_value_depth arguments))
    (PTree.set _stream(gateway_value_stream arguments)(create_undef_temps(fn_temps f_host_value))).

Record gateway_value_slots :Type:={gateway_value_tag_slot:block;gateway_value_size_slot:block}.
Definition gateway_value_environment slots:=
  PTree.set _size(gateway_value_size_slot slots,tulong)
    (PTree.set _tag(gateway_value_tag_slot slots,tulong)empty_env).
Definition gateway_value_allocations before slots after :Prop:=
  exists middle,Mem.alloc before 0 8=(middle,gateway_value_tag_slot slots) /\
    Mem.alloc middle 0 8=(after,gateway_value_size_slot slots).

Lemma gateway_value_allocation_chain before slots after :
  gateway_value_allocations before slots after ->
  local_allocations before[(gateway_value_tag_slot slots,8);(gateway_value_size_slot slots,8)]after.
Proof. intros[middle[TAG SIZE]];econstructor;[exact TAG|]. econstructor;[exact SIZE|constructor]. Qed.

Lemma gateway_value_function_entry ge before arguments slots after :
  gateway_value_allocations before slots after ->
  function_entry2 ge f_host_value(gateway_value_arguments_list arguments)before
    (gateway_value_environment slots)(gateway_value_parameters arguments)after.
Proof.
  intros[middle[TAG SIZE]];constructor.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros first second LEFT RIGHT.
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst first;
      repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst second;discriminate.
  - cbn[fn_vars];econstructor;[exact TAG|]. econstructor;[exact SIZE|constructor].
  - reflexivity.
Qed.

Theorem gateway_actual_value_entry ge before arguments environment temporaries after :
  function_entry2 ge f_host_value(gateway_value_arguments_list arguments)before environment temporaries after ->
  exists slots,environment=gateway_value_environment slots /\temporaries=gateway_value_parameters arguments /\
    gateway_value_allocations before slots after /\Mem.unchanged_on(fun _ _=>True)before after /\
    ~Mem.valid_block before(gateway_value_tag_slot slots) /\~Mem.valid_block before(gateway_value_size_slot slots) /\
    gateway_value_tag_slot slots<>gateway_value_size_slot slots /\
    Mem.range_perm after(gateway_value_tag_slot slots)0 8 Cur Freeable /\
    Mem.range_perm after(gateway_value_size_slot slots)0 8 Cur Freeable.
Proof.
  intro ENTRY;destruct(Mem.alloc before 0 8)as[middle tag]eqn:TAG.
  destruct(Mem.alloc middle 0 8)as[canonical size]eqn:SIZE.
  set(slots:={|gateway_value_tag_slot:=tag;gateway_value_size_slot:=size|}).
  assert(ALLOC:gateway_value_allocations before slots canonical)by(exists middle;auto).
  destruct(function_entry_unique _ _ _ _ _ _ _ _ _ _
    (gateway_value_function_entry ge before arguments slots canonical ALLOC)ENTRY)as[ENV[TEMPS MEMORY]].
  subst environment temporaries after.
  pose proof(gateway_value_allocation_chain _ _ _ ALLOC)as CHAIN.
  pose proof(local_allocations_objects _ _ _ CHAIN)as OBJECTS.
  inversion OBJECTS as[|? ? TAG_OBJECT TAIL];subst.
  inversion TAIL as[|? ? SIZE_OBJECT REST];subst.
  pose proof(local_allocations_distinct _ _ _ CHAIN)as DISTINCT.
  inversion DISTINCT as[|? ? NOTIN NO_DUP];subst.
  exists slots;split;[reflexivity|]. split;[reflexivity|]. split;[exact ALLOC|].
  split;[eapply local_allocations_unchanged;exact CHAIN|]. split;[exact(proj1 TAG_OBJECT)|].
  split;[exact(proj1 SIZE_OBJECT)|]. split;[intro SAME;apply NOTIN;cbn;auto|].
  split;[exact(proj2 TAG_OBJECT)|exact(proj2 SIZE_OBJECT)].
Qed.

Record gateway_value_inputs before stream_block stream_offset stream(readonly:block->Z->Prop) :Prop:={
  gateway_value_stream_cells:gateway_stream_memory before stream_block stream_offset stream;
  gateway_value_stream_bounds:Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus;
  gateway_value_stream_owned:Mem.range_perm before stream_block(Ptrofs.unsigned stream_offset)
    (Ptrofs.unsigned stream_offset+48)Cur Writable;
  gateway_value_readonly_live:forall block position,readonly block position->Mem.valid_block before block;
  gateway_value_readonly_readable:forall block position,readonly block position->Mem.perm before block position Cur Readable;
  gateway_value_readonly_cancel:forall position,
    Ptrofs.unsigned stream_offset+8<=position<Ptrofs.unsigned stream_offset+12 ->~readonly stream_block position;
  gateway_value_readonly_counters:forall position,
    Ptrofs.unsigned stream_offset+24<=position<Ptrofs.unsigned stream_offset+40 ->~readonly stream_block position
}.

Definition gateway_value_input_region stream_block stream_offset readonly object position :Prop:=
  gateway_stream_region stream_block stream_offset object position \/readonly object position.

Lemma gateway_value_inputs_frame before after stream_block stream_offset stream readonly :
  Mem.unchanged_on(gateway_value_input_region stream_block stream_offset readonly)before after ->
  gateway_value_inputs before stream_block stream_offset stream readonly ->
  gateway_value_inputs after stream_block stream_offset stream readonly.
Proof.
  intros FRAME INPUT;destruct INPUT as[CELLS BOUNDS OWNED LIVE READABLE CANCEL COUNTERS];constructor;try assumption.
  - eapply gateway_stream_memory_closed;[exact BOUNDS|exact CELLS|].
    eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption].
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|left;split;[reflexivity|exact RANGE]|].
    apply OWNED;exact RANGE.
  - intros object position READ;eapply Mem.valid_block_unchanged_on;[exact FRAME|apply(LIVE object position);exact READ].
  - intros object position READ;eapply Mem.perm_unchanged_on;[exact FRAME|right;exact READ|apply READABLE;exact READ].
Qed.

Theorem gateway_value_slots_separate before after slots stream_block stream_offset stream readonly :
  gateway_value_inputs before stream_block stream_offset stream readonly ->gateway_value_allocations before slots after ->
  gateway_value_inputs after stream_block stream_offset stream readonly /\
  gateway_value_tag_slot slots<>stream_block /\gateway_value_size_slot slots<>stream_block /\
  (forall position,~readonly(gateway_value_tag_slot slots)position) /\
  (forall position,~readonly(gateway_value_size_slot slots)position).
Proof.
  intros INPUT ALLOC;pose proof(gateway_value_allocation_chain _ _ _ ALLOC)as CHAIN.
  pose proof(local_allocations_objects _ _ _ CHAIN)as OBJECTS.
  inversion OBJECTS as[|? ? TAG TAIL];subst;inversion TAIL as[|? ? SIZE REST];subst.
  assert(STREAM:Mem.valid_block before stream_block).
  { eapply Mem.perm_valid_block.
    apply(gateway_value_stream_owned _ _ _ _ _ INPUT(Ptrofs.unsigned stream_offset));lia. }
  split.
  - eapply gateway_value_inputs_frame;[eapply local_allocations_unchanged;exact CHAIN|exact INPUT].
  - split;[intro SAME;apply(proj1 TAG);rewrite SAME;exact STREAM|].
    split;[intro SAME;apply(proj1 SIZE);rewrite SAME;exact STREAM|].
    split;intros position READ;[apply(proj1 TAG)|apply(proj1 SIZE)];
      eapply gateway_value_readonly_live;eassumption.
Qed.
