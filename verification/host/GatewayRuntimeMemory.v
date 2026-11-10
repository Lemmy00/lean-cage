(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Individual runtime memory actions retain actual pointer origins. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Cop Clight.
From HostGateway Require Import GatewayPointerOrigins GatewayPointerMemory GatewayPointerEntry.
Import ListNotations.
Open Scope Z_scope.

(* The pool records concrete values held by this runtime episode. It grants no
   authority to guess a source address from an integer or from arbitrary bytes.
   Callback memory changes are deliberately separate, rather than framed here. *)
Inductive gateway_runtime_memory_step (ge : Clight.genv) (storage : block -> Prop)
    (callback : mem -> list val -> mem -> val -> Prop) : mem -> list val -> mem -> list val -> Prop :=
| gateway_runtime_scalar : forall memory pool value,
    (forall object offset, value <> Vptr object offset) ->
    gateway_runtime_memory_step ge storage callback memory pool memory (value :: pool)
| gateway_runtime_storage : forall memory pool object offset,
    storage object -> Mem.valid_block memory object ->
    gateway_runtime_memory_step ge storage callback memory pool memory (Vptr object offset :: pool)
| gateway_runtime_argument : forall memory pool value,
    In value pool -> gateway_runtime_memory_step ge storage callback memory pool memory (value :: pool)
| gateway_runtime_load : forall memory pool address chunk value,
    In address pool -> Mem.loadv chunk memory address = Some value ->
    gateway_runtime_memory_step ge storage callback memory pool memory (value :: pool)
| gateway_runtime_cast : forall memory pool value original target result,
    In value pool -> Cop.sem_cast value original target memory = Some result ->
    gateway_runtime_memory_step ge storage callback memory pool memory (result :: pool)
| gateway_runtime_binary : forall memory pool operation first first_type second second_type result,
    In first pool -> In second pool ->
    Cop.sem_binary_operation ge operation first first_type second second_type memory = Some result ->
    gateway_runtime_memory_step ge storage callback memory pool memory (result :: pool)
| gateway_runtime_store : forall before pool address chunk value after,
    In address pool -> In value pool -> Mem.storev chunk before address value = Some after ->
    gateway_runtime_memory_step ge storage callback before pool after pool
| gateway_runtime_copy : forall before pool source source_offset target target_offset count bytes after,
    In (Vptr source source_offset) pool -> In (Vptr target target_offset) pool ->
    Mem.loadbytes before source (Ptrofs.unsigned source_offset) count = Some bytes ->
    Mem.storebytes before target (Ptrofs.unsigned target_offset) bytes = Some after ->
    gateway_runtime_memory_step ge storage callback before pool after pool
| gateway_runtime_bytes : forall before pool target target_offset bytes after,
    In (Vptr target target_offset) pool ->
    Mem.storebytes before target (Ptrofs.unsigned target_offset) (inj_bytes bytes) = Some after ->
    gateway_runtime_memory_step ge storage callback before pool after pool
| gateway_runtime_allocate : forall before pool low high after object,
    Mem.alloc before low high = (after, object) ->
    gateway_runtime_memory_step ge storage callback before pool after (Vptr object Ptrofs.zero :: pool)
| gateway_runtime_release : forall before pool object offset low high after,
    In (Vptr object offset) pool -> Mem.free before object low high = Some after ->
    gateway_runtime_memory_step ge storage callback before pool after pool
| gateway_runtime_callback : forall before pool arguments after result,
    Forall (fun argument => In argument pool) arguments -> callback before arguments after result ->
    gateway_runtime_memory_step ge storage callback before pool after (result :: pool).

Inductive gateway_runtime_memory_steps ge storage callback : mem -> list val -> mem -> list val -> Prop :=
| gateway_runtime_memory_nil : forall memory pool,
    gateway_runtime_memory_steps ge storage callback memory pool memory pool
| gateway_runtime_memory_cons : forall before pool middle held after final,
    gateway_runtime_memory_step ge storage callback before pool middle held ->
    gateway_runtime_memory_steps ge storage callback middle held after final ->
    gateway_runtime_memory_steps ge storage callback before pool after final.

Definition gateway_runtime_memory_scope private memory pool : Prop :=
  gateway_memory_avoids private memory /\
  (forall object, private object -> Mem.valid_block memory object) /\
  Forall (gateway_pointer_avoids private) pool.

Definition gateway_callback_memory_origin private (guard : mem -> Prop) (callback : mem -> list val -> mem -> val -> Prop) : Prop :=
  forall before arguments after result,
    gateway_memory_avoids private before ->
    (forall object, private object -> Mem.valid_block before object) ->
    Forall (gateway_pointer_avoids private) arguments -> callback before arguments after result ->
    gateway_memory_avoids private after /\
    (forall object, private object -> Mem.valid_block after object) /\
    gateway_pointer_avoids private result /\ (guard before -> Mem.unchanged_on (fun object _ => private object) before after).

Definition gateway_callback_pointer_origin private (callback : mem -> list val -> mem -> val -> Prop) : Prop :=
  forall before arguments after result,
    gateway_memory_avoids private before ->
    (forall object, private object -> Mem.valid_block before object) ->
    Forall (gateway_pointer_avoids private) arguments -> callback before arguments after result ->
    gateway_memory_avoids private after /\
    (forall object, private object -> Mem.valid_block after object) /\ gateway_pointer_avoids private result.

Theorem gateway_callback_pointer_law private callback :
  gateway_callback_pointer_origin private callback -> gateway_callback_memory_origin private (fun _ => False) callback.
Proof.
  intros CALLBACK before arguments after result MEMORY LIVE ARGUMENTS RUN.
  destruct (CALLBACK before arguments after result MEMORY LIVE ARGUMENTS RUN) as [NEXT [RETAINED RESULT]].
  split; [exact NEXT |split; [exact RETAINED |split; [exact RESULT |tauto]]].
Qed.

Lemma gateway_runtime_pool_origin private pool value :
  Forall (gateway_pointer_avoids private) pool -> In value pool -> gateway_pointer_avoids private value.
Proof. intros POOL MEMBER; exact (proj1 (Forall_forall _ _) POOL value MEMBER). Qed.

Theorem gateway_runtime_memory_step_origin ge storage callback private (guard : mem -> Prop) before pool after final :
  (forall object, storage object -> ~ private object) -> gateway_callback_memory_origin private guard callback ->
  gateway_runtime_memory_scope private before pool ->
  gateway_runtime_memory_step ge storage callback before pool after final ->
  gateway_runtime_memory_scope private after final /\
  (guard before -> Mem.unchanged_on (fun object _ => private object) before after).
Proof.
  intros STORAGE CALLBACK [MEMORY [LIVE POOL]] STEP; inversion STEP; subst.
  - split; [split; [exact MEMORY |split; [exact LIVE |constructor; [|exact POOL]]] |intro ACTIVE; apply Mem.unchanged_on_refl].
    destruct value; try exact I; exfalso; eapply H; reflexivity.
  - split; [split; [exact MEMORY |split; [exact LIVE |constructor; [|exact POOL]]] |intro ACTIVE; apply Mem.unchanged_on_refl].
    apply STORAGE; assumption.
  - split; [split; [exact MEMORY |split; [exact LIVE |constructor; [|exact POOL]]] |intro ACTIVE; apply Mem.unchanged_on_refl].
    eapply gateway_runtime_pool_origin; eassumption.
  - split; [split; [exact MEMORY |split; [exact LIVE |constructor; [|exact POOL]]] |intro ACTIVE; apply Mem.unchanged_on_refl].
    eapply gateway_loadv_avoids; eassumption.
  - split; [split; [exact MEMORY |split; [exact LIVE |constructor; [|exact POOL]]] |intro ACTIVE; apply Mem.unchanged_on_refl].
    eapply gateway_cast_avoids; [eapply gateway_runtime_pool_origin; eassumption |eassumption].
  - split; [split; [exact MEMORY |split; [exact LIVE |constructor; [|exact POOL]]] |intro ACTIVE; apply Mem.unchanged_on_refl].
    eapply gateway_binary_avoids with (first := first) (second := second); [eapply gateway_runtime_pool_origin; eassumption
      |eapply gateway_runtime_pool_origin; eassumption |eassumption].
  - assert (ADDRESS : gateway_pointer_avoids private address) by (eapply gateway_runtime_pool_origin; eassumption).
    split.
    + split; [eapply gateway_storev_avoids; [exact MEMORY |eapply gateway_runtime_pool_origin; eassumption |eassumption] |].
      split; [intros object PRIVATE; eapply gateway_storev_blocks; [eassumption |apply LIVE; exact PRIVATE] |exact POOL].
    + intro ACTIVE; destruct address; try discriminate; eapply Mem.storev_unchanged_on; [eassumption |intros; exact ADDRESS].
  - assert (TARGET : ~ private target) by (eapply gateway_runtime_pool_origin with (value := Vptr target target_offset); eassumption).
    split.
    + split; [eapply gateway_storebytes_avoids; [exact MEMORY |eapply gateway_loadbytes_avoids; eassumption |eassumption] |].
      split; [intros object PRIVATE; eapply Mem.storebytes_valid_block_1; [eassumption |apply LIVE; exact PRIVATE] |exact POOL].
    + intro ACTIVE; eapply Mem.storebytes_unchanged_on; [eassumption |intros; exact TARGET].
  - assert (TARGET : ~ private target) by (eapply gateway_runtime_pool_origin with (value := Vptr target target_offset); eassumption).
    split.
    + split; [eapply gateway_storebytes_avoids; [exact MEMORY |apply gateway_bytes_avoid |eassumption] |].
      split; [intros object PRIVATE; eapply Mem.storebytes_valid_block_1; [eassumption |apply LIVE; exact PRIVATE] |exact POOL].
    + intro ACTIVE; eapply Mem.storebytes_unchanged_on; [eassumption |intros; exact TARGET].
  - split.
    + split; [eapply gateway_alloc_avoids; eassumption |]. split.
      * intros current PRIVATE; eapply Mem.valid_block_alloc; [eassumption |apply LIVE; exact PRIVATE].
      * constructor; [|exact POOL]. intro PRIVATE.
        eapply Mem.fresh_block_alloc; [eassumption |apply LIVE; exact PRIVATE].
    + intro ACTIVE; eapply Mem.alloc_unchanged_on; eassumption.
  - assert (TARGET : ~ private object) by (eapply gateway_runtime_pool_origin with (value := Vptr object offset); eassumption).
    split.
    + split; [eapply gateway_free_avoids; eassumption |].
      split; [intros current PRIVATE; eapply Mem.valid_block_free_1; [eassumption |apply LIVE; exact PRIVATE] |exact POOL].
    + intro ACTIVE; eapply Mem.free_unchanged_on; [eassumption |intros; exact TARGET].
  - assert (ARGUMENTS : Forall (gateway_pointer_avoids private) arguments).
    { eapply Forall_impl; [|eassumption]. intros argument MEMBER; eapply gateway_runtime_pool_origin; eassumption. }
    destruct (CALLBACK before arguments after result MEMORY LIVE ARGUMENTS H0) as [NEXT [RETAINED [RESULT FRAME]]].
    split; [split; [exact NEXT |split; [exact RETAINED |constructor; assumption]] |exact FRAME].
Qed.

Theorem gateway_runtime_memory_steps_origin ge storage callback private (guard : mem -> Prop) before pool after final :
  (forall object, storage object -> ~ private object) -> gateway_callback_memory_origin private guard callback ->
  (forall before after, Mem.unchanged_on (fun object _ => private object) before after -> guard before -> guard after) ->
  gateway_runtime_memory_scope private before pool ->
  gateway_runtime_memory_steps ge storage callback before pool after final ->
  gateway_runtime_memory_scope private after final /\
  (guard before -> Mem.unchanged_on (fun object _ => private object) before after).
Proof.
  intros STORAGE CALLBACK PRESERVES READY RUN; revert READY; induction RUN; intro READY.
  - split; [exact READY |intro ACTIVE; apply Mem.unchanged_on_refl].
  - destruct (gateway_runtime_memory_step_origin ge storage callback private guard _ _ _ _ STORAGE CALLBACK READY H)
      as [MIDDLE FIRST].
    destruct (IHRUN MIDDLE) as [FINAL LAST]; split; [exact FINAL |].
    intro ACTIVE; pose proof (FIRST ACTIVE) as INITIAL.
    eapply Mem.unchanged_on_trans; [exact INITIAL |apply LAST; eapply PRESERVES; eassumption].
Qed.

Theorem gateway_runtime_memory_pointer_scope ge storage callback private before pool after final :
  (forall object, storage object -> ~ private object) -> gateway_callback_pointer_origin private callback ->
  gateway_runtime_memory_scope private before pool ->
  gateway_runtime_memory_steps ge storage callback before pool after final ->
  gateway_runtime_memory_scope private after final.
Proof.
  intros STORAGE CALLBACK READY RUN.
  exact (proj1 (gateway_runtime_memory_steps_origin ge storage callback private (fun _ => False)
    before pool after final STORAGE (gateway_callback_pointer_law private callback CALLBACK)
    (fun _ _ _ impossible => False_rect _ impossible) READY RUN)).
Qed.
