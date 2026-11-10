(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Byte stores retain logical pointer provenance, including partial fragments. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayPointerOrigins.
Import ListNotations.
Local Transparent Mem.loadv Mem.loadbytes Mem.storev Mem.alloc Mem.free Mem.free_list.

Definition gateway_memval_avoids (private : block -> Prop) (value : memval) : Prop :=
  match value with Fragment original _ _ => gateway_pointer_avoids private original | _ => True end.

Definition gateway_memory_avoids (private : block -> Prop) (memory : mem) : Prop :=
  forall object offset,
    gateway_memval_avoids private (ZMap.get offset (PMap.get object (Mem.mem_contents memory))).

Lemma gateway_load_result_avoids private chunk value :
  gateway_pointer_avoids private value -> gateway_pointer_avoids private (Val.load_result chunk value).
Proof.
  destruct value; destruct chunk; cbn [Val.load_result gateway_pointer_avoids Archi.ptr64];
    intros; try exact I; try assumption.
  destruct (Val.norm_bool_cases (Vint (Int.zero_ext 8 i))) as [SAME |[SAME |SAME]];
    rewrite SAME; exact I.
Qed.

Lemma gateway_shape_avoids private chunk bytes value :
  shape_decoding chunk bytes value -> Forall (gateway_memval_avoids private) bytes ->
  gateway_pointer_avoids private value.
Proof.
  intros SHAPE SAFE; inversion SHAPE; subst.
  - inversion SAFE; apply gateway_load_result_avoids; assumption.
  - destruct value; try exact I; contradiction.
  - exact I.
Qed.

Theorem gateway_decode_avoids private chunk bytes :
  Forall (gateway_memval_avoids private) bytes -> gateway_pointer_avoids private (decode_val chunk bytes).
Proof.
  intro SAFE; destruct bytes as [|first rest].
  - destruct chunk; exact I.
  - eapply gateway_shape_avoids; [apply decode_val_shape |exact SAFE].
Qed.

Lemma gateway_getN_avoids private count offset contents :
  (forall position, gateway_memval_avoids private (ZMap.get position contents)) ->
  Forall (gateway_memval_avoids private) (Mem.getN count offset contents).
Proof.
  revert offset; induction count; intros offset SAFE; cbn; constructor; auto.
Qed.

Theorem gateway_load_avoids private memory chunk object offset value :
  gateway_memory_avoids private memory -> Mem.load chunk memory object offset = Some value ->
  gateway_pointer_avoids private value.
Proof.
  intros SAFE LOAD; rewrite (Mem.load_result _ _ _ _ _ LOAD).
  apply gateway_decode_avoids, gateway_getN_avoids; apply SAFE.
Qed.

Theorem gateway_loadv_avoids private memory chunk address value :
  gateway_memory_avoids private memory -> Mem.loadv chunk memory address = Some value ->
  gateway_pointer_avoids private value.
Proof.
  intros SAFE LOAD; unfold Mem.loadv in LOAD; destruct address; try discriminate.
  destruct (zle _ _) as [BOUND |BOUND]; [|discriminate].
  eapply gateway_load_avoids; eassumption.
Qed.

Theorem gateway_loadbytes_avoids private memory object offset count bytes :
  gateway_memory_avoids private memory -> Mem.loadbytes memory object offset count = Some bytes ->
  Forall (gateway_memval_avoids private) bytes.
Proof.
  intros SAFE LOAD; unfold Mem.loadbytes in LOAD.
  destruct (Mem.range_perm_dec _ _ _ _ _ _); [|discriminate].
  inversion LOAD; subst; apply gateway_getN_avoids, SAFE.
Qed.

Lemma gateway_bytes_avoid private bytes : Forall (gateway_memval_avoids private) (inj_bytes bytes).
Proof. induction bytes as [|byte rest IH]; cbn; [constructor |constructor; [exact I |exact IH]]. Qed.

Lemma gateway_fragments_avoid private count value quantity :
  gateway_pointer_avoids private value ->
  Forall (gateway_memval_avoids private) (inj_value_rec count value quantity).
Proof. intro SAFE; induction count; cbn; constructor; assumption. Qed.

Lemma gateway_undefined_avoid private count :
  Forall (gateway_memval_avoids private) (repeat Undef count).
Proof. induction count; constructor; [exact I |exact IHcount]. Qed.

Theorem gateway_encode_avoids private chunk value :
  gateway_pointer_avoids private value -> Forall (gateway_memval_avoids private) (encode_val chunk value).
Proof.
  intro SAFE; destruct value; destruct chunk;
    cbv beta iota zeta delta [encode_val Archi.ptr64 inj_value];
    solve [apply gateway_bytes_avoid |apply gateway_fragments_avoid; exact SAFE |apply gateway_undefined_avoid].
Qed.

Lemma gateway_setN_avoids private bytes offset contents :
  Forall (gateway_memval_avoids private) bytes ->
  (forall position, gateway_memval_avoids private (ZMap.get position contents)) ->
  forall position, gateway_memval_avoids private (ZMap.get position (Mem.setN bytes offset contents)).
Proof.
  intro SAFE; revert offset contents; induction SAFE; intros offset contents PREVIOUS position; cbn.
  - apply PREVIOUS.
  - apply IHSAFE; intro current; destruct (zeq current offset) as [SAME |DIFFERENT].
    + subst; rewrite ZMap.gss; exact H.
    + rewrite ZMap.gso by exact DIFFERENT; apply PREVIOUS.
Qed.

Theorem gateway_store_avoids private before after chunk object offset value :
  gateway_memory_avoids private before -> gateway_pointer_avoids private value ->
  Mem.store chunk before object offset value = Some after -> gateway_memory_avoids private after.
Proof.
  intros SAFE VALUE STORE candidate position.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ STORE).
  destruct (peq candidate object) as [SAME |DIFFERENT].
  - subst candidate; rewrite PMap.gss; apply gateway_setN_avoids;
      [apply gateway_encode_avoids; exact VALUE |apply SAFE].
  - rewrite PMap.gso by exact DIFFERENT; apply SAFE.
Qed.

Theorem gateway_storev_avoids private before after chunk address value :
  gateway_memory_avoids private before -> gateway_pointer_avoids private value ->
  Mem.storev chunk before address value = Some after -> gateway_memory_avoids private after.
Proof.
  intros SAFE VALUE STORE; unfold Mem.storev in STORE; destruct address; try discriminate.
  destruct (zle _ _) as [BOUND |BOUND]; [|discriminate].
  eapply gateway_store_avoids; eassumption.
Qed.

Theorem gateway_storebytes_avoids private before after object offset bytes :
  gateway_memory_avoids private before -> Forall (gateway_memval_avoids private) bytes ->
  Mem.storebytes before object offset bytes = Some after -> gateway_memory_avoids private after.
Proof.
  intros SAFE BYTES STORE candidate position.
  rewrite (Mem.storebytes_mem_contents _ _ _ _ _ STORE).
  destruct (peq candidate object) as [SAME |DIFFERENT].
  - subst candidate; rewrite PMap.gss; apply gateway_setN_avoids; [exact BYTES |apply SAFE].
  - rewrite PMap.gso by exact DIFFERENT; apply SAFE.
Qed.

Theorem gateway_alloc_avoids private before after object low high :
  gateway_memory_avoids private before -> Mem.alloc before low high = (after, object) ->
  gateway_memory_avoids private after.
Proof.
  intros SAFE ALLOC; unfold Mem.alloc in ALLOC; inversion ALLOC; subst; clear ALLOC.
  intros candidate position; cbn.
  destruct (peq candidate (Mem.nextblock before)) as [SAME |DIFFERENT].
  - subst candidate; rewrite PMap.gss, ZMap.gi; exact I.
  - rewrite PMap.gso by exact DIFFERENT; apply SAFE.
Qed.

Theorem gateway_free_avoids private before after object low high :
  gateway_memory_avoids private before -> Mem.free before object low high = Some after ->
  gateway_memory_avoids private after.
Proof.
  intros SAFE FREE; unfold Mem.free in FREE.
  destruct (Mem.range_perm_dec _ _ _ _ _ _); [|discriminate].
  inversion FREE; subst; exact SAFE.
Qed.

Theorem gateway_free_list_avoids private before after bindings :
  gateway_memory_avoids private before -> Mem.free_list before bindings = Some after ->
  gateway_memory_avoids private after.
Proof.
  revert before after; induction bindings as [|[[object low] high] rest IH]; intros before after SAFE FREE; cbn in FREE.
  - inversion FREE; subst; exact SAFE.
  - destruct (Mem.free before object low high) as [middle |] eqn:RELEASE; [|discriminate].
    apply IH with (before := middle); [eapply gateway_free_avoids; eassumption |exact FREE].
Qed.
