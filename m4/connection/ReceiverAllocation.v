(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.input: All receiver locals are fresh and remain owned after allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import FreshMemory ReceiverSource.
Import ListNotations.
Open Scope Z_scope.

Inductive local_allocations : mem -> list (block*Z) -> mem -> Prop :=
| local_allocations_nil : forall m,local_allocations m [] m
| local_allocations_next : forall before mid after b size rest,
    Mem.alloc before 0 size=(mid,b) -> local_allocations mid rest after ->
    local_allocations before ((b,size)::rest) after.

Lemma local_allocations_unchanged : forall before objects after,
  local_allocations before objects after ->
  forall P,Mem.unchanged_on P before after.
Proof.
  intros before objects after RUN;induction RUN;intros P.
  - apply Mem.unchanged_on_refl.
  - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact H|apply IHRUN].
Qed.
Lemma local_allocations_perms : forall before objects after,
  local_allocations before objects after ->
  forall b pos kind permission,Mem.perm before b pos kind permission ->
    Mem.perm after b pos kind permission.
Proof.
  intros before objects after RUN;induction RUN;intros;[assumption|].
  apply IHRUN;eapply Mem.perm_alloc_1;eassumption.
Qed.
Lemma local_allocations_objects : forall before objects after,
  local_allocations before objects after ->
  Forall (fun obj=>~Mem.valid_block before (fst obj) /\
    Mem.range_perm after (fst obj) 0 (snd obj) Cur Freeable) objects.
Proof.
  intros before objects after RUN;induction RUN;[constructor|]. constructor.
  - cbn;split;[eapply Mem.fresh_block_alloc;exact H|].
    intros pos RANGE;eapply local_allocations_perms;[exact RUN|].
    eapply Mem.perm_alloc_2;eassumption.
  - rewrite Forall_forall in *;intros [other limit] IN;cbn in *.
    destruct (IHRUN _ IN) as [FRESH PERM];split;[|exact PERM].
    intro VALID;apply FRESH;eapply Mem.valid_block_alloc;eassumption.
Qed.
Lemma local_allocations_distinct : forall before objects after,
  local_allocations before objects after -> NoDup (map fst objects).
Proof.
  intros before objects after RUN;induction RUN;[constructor|]. cbn;constructor;[|exact IHRUN].
  intro IN;apply in_map_iff in IN;destruct IN as [[other size'] [SAME IN]];cbn in SAME;subst other.
  pose proof (local_allocations_objects _ _ _ RUN) as OBJECTS;rewrite Forall_forall in OBJECTS.
  destruct (OBJECTS _ IN) as [FRESH _];cbn in FRESH;apply FRESH;eapply Mem.valid_new_block;exact H.
Qed.

Definition receiver_objects b :=
  [(rb_pipe b,4);(rb_result b,144);(rb_bytes b,9);(rb_unknown b,144);
   (rb_signal b,144);(rb_exit b,144);(rb_setup b,144)].
Theorem receiver_allocation_chain : forall base b allocated,
  receiver_allocations base b allocated -> local_allocations base (receiver_objects b) allocated.
Proof.
  intros base b allocated
    [m1 [m2 [m3 [m4 [m5 [m6 [A1 [A2 [A3 [A4 [A5 [A6 A7]]]]]]]]]]]].
  unfold receiver_objects.
  econstructor;[exact A1|]. econstructor;[exact A2|]. econstructor;[exact A3|].
  econstructor;[exact A4|]. econstructor;[exact A5|]. econstructor;[exact A6|].
  econstructor;[exact A7|]. constructor.
Qed.
Theorem receiver_allocation_ownership : forall base b allocated,
  receiver_allocations base b allocated ->
  old_memory base allocated /\ NoDup (map fst (receiver_objects b)) /\
  Forall (fun obj=>~Mem.valid_block base (fst obj) /\
    Mem.range_perm allocated (fst obj) 0 (snd obj) Cur Freeable) (receiver_objects b).
Proof.
  intros base b allocated ALLOC;pose proof (receiver_allocation_chain _ _ _ ALLOC) as CHAIN.
  split;[eapply local_allocations_unchanged;exact CHAIN|].
  split;[eapply local_allocations_distinct|eapply local_allocations_objects];exact CHAIN.
Qed.
