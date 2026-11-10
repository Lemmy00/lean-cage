(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual entry allocation and argument binding produce address scopes. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Cop Clight.
From HostGateway Require Import GatewayPointerOrigins GatewayPointerMemory.
Import ListNotations.
Local Transparent Mem.storev Mem.free_list.

Definition gateway_locals_avoid private (environment : env) :=
  forall identifier object ty, environment ! identifier = Some (object, ty) -> ~ private object.
Definition gateway_temporaries_avoid private (temporaries : temp_env) :=
  forall identifier value, temporaries ! identifier = Some value -> gateway_pointer_avoids private value.

Lemma gateway_temporaries_store private temporaries identifier value :
  gateway_temporaries_avoid private temporaries -> gateway_pointer_avoids private value ->
  gateway_temporaries_avoid private (PTree.set identifier value temporaries).
Proof.
  intros SAFE VALUE current stored LOOKUP; rewrite PTree.gsspec in LOOKUP.
  destruct (peq current identifier); [inversion LOOKUP; subst; exact VALUE |eapply SAFE; exact LOOKUP].
Qed.

Theorem gateway_undef_temporaries_avoid private declarations :
  gateway_temporaries_avoid private (create_undef_temps declarations).
Proof.
  induction declarations as [|[identifier ty] rest IH]; cbn.
  - intros current value LOOKUP; rewrite PTree.gempty in LOOKUP; discriminate.
  - apply gateway_temporaries_store; [exact IH |exact I].
Qed.

Theorem gateway_bind_temporaries_avoid private formals arguments before after :
  gateway_temporaries_avoid private before -> Forall (gateway_pointer_avoids private) arguments ->
  bind_parameter_temps formals arguments before = Some after -> gateway_temporaries_avoid private after.
Proof.
  revert arguments before after; induction formals as [|[identifier ty] rest IH];
    intros arguments before after SAFE ARGS BIND; destruct arguments as [|value values]; try discriminate.
  - inversion BIND; subst; exact SAFE.
  - cbn in BIND; inversion ARGS; subst; eapply IH; [apply gateway_temporaries_store; eassumption |eassumption |exact BIND].
Qed.

Theorem gateway_assign_avoids private ge ty before object offset field value after :
  gateway_memory_avoids private before -> gateway_pointer_avoids private value ->
  assign_loc ge ty before object offset field value after -> gateway_memory_avoids private after.
Proof.
  intros SAFE VALUE STORE; inversion STORE; subst.
  - eapply gateway_storev_avoids; eassumption.
  - eapply gateway_storebytes_avoids; [exact SAFE |eapply gateway_loadbytes_avoids; eassumption |eassumption].
  - match goal with BITFIELD : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion BITFIELD; subst end.
    eapply gateway_storev_avoids; [exact SAFE | |eassumption]; exact I.
Qed.

Lemma gateway_storev_blocks before after chunk address value :
  Mem.storev chunk before address value = Some after ->
  forall object, Mem.valid_block before object -> Mem.valid_block after object.
Proof.
  intro STORE; unfold Mem.storev in STORE; destruct address; try discriminate.
  destruct (zle _ _) as [BOUND |BOUND]; [|discriminate].
  eapply Mem.store_valid_block_1; exact STORE.
Qed.

Theorem gateway_assign_blocks ge ty before object offset field value after :
  assign_loc ge ty before object offset field value after ->
  forall candidate, Mem.valid_block before candidate -> Mem.valid_block after candidate.
Proof.
  intro STORE; inversion STORE; subst.
  - eapply gateway_storev_blocks; eassumption.
  - eapply Mem.storebytes_valid_block_1; eassumption.
  - match goal with BITFIELD : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion BITFIELD; subst end.
    eapply gateway_storev_blocks; eassumption.
Qed.

Theorem gateway_free_list_blocks before after bindings :
  Mem.free_list before bindings = Some after ->
  forall object, Mem.valid_block before object -> Mem.valid_block after object.
Proof.
  revert before after; induction bindings as [|[[released low] high] rest IH]; intros before after FREE object LIVE; cbn in FREE.
  - inversion FREE; subst; exact LIVE.
  - destruct (Mem.free before released low high) as [middle |] eqn:RELEASE; [|discriminate].
    eapply IH; [exact FREE |eapply Mem.valid_block_free_1; eassumption].
Qed.

Theorem gateway_allocate_variables_avoid private ge environment before declarations final after :
  (forall object, private object -> Mem.valid_block before object) ->
  gateway_memory_avoids private before -> gateway_locals_avoid private environment ->
  alloc_variables ge environment before declarations final after ->
  gateway_memory_avoids private after /\ gateway_locals_avoid private final /\
    (forall object, private object -> Mem.valid_block after object).
Proof.
  intros PRIVATE MEMORY LOCALS ALLOCATE; induction ALLOCATE.
  - repeat split; assumption.
  - apply IHALLOCATE.
    + intros object SELECTED; eapply Mem.valid_block_alloc; [exact H |apply PRIVATE; exact SELECTED].
    + eapply gateway_alloc_avoids; eassumption.
    + intros identifier object value LOOKUP; rewrite PTree.gsspec in LOOKUP.
      destruct (peq identifier id).
      * inversion LOOKUP; subst; intro SELECTED.
        exact (Mem.fresh_block_alloc _ _ _ _ _ H (PRIVATE _ SELECTED)).
      * eapply LOCALS; exact LOOKUP.
Qed.

Theorem gateway_function_entry_avoids private ge function arguments before environment temporaries after :
  (forall object, private object -> Mem.valid_block before object) ->
  gateway_memory_avoids private before -> Forall (gateway_pointer_avoids private) arguments ->
  function_entry2 ge function arguments before environment temporaries after ->
  gateway_memory_avoids private after /\ gateway_locals_avoid private environment /\
    gateway_temporaries_avoid private temporaries /\
    (forall object, private object -> Mem.valid_block after object).
Proof.
  intros PRIVATE MEMORY ARGUMENTS ENTRY; inversion ENTRY; subst.
  match goal with ALLOCATE : alloc_variables _ _ _ _ _ _ |- _ =>
    destruct (gateway_allocate_variables_avoid private _ _ _ _ _ _ PRIVATE MEMORY
      ltac:(intros identifier object ty LOOKUP; rewrite PTree.gempty in LOOKUP; discriminate) ALLOCATE)
      as [FINAL_MEMORY [LOCALS FINAL_PRIVATE]] end.
  split; [exact FINAL_MEMORY |]. split; [exact LOCALS |]. split; [|exact FINAL_PRIVATE].
  eapply gateway_bind_temporaries_avoid; [apply gateway_undef_temporaries_avoid |exact ARGUMENTS |eassumption].
Qed.
