(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source arithmetic cannot manufacture a private allocation identity. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Cop Clight.
Import ListNotations.

Ltac gateway_pointer_origin_cases call :=
  repeat first [discriminate call |progress cbn in call |
    lazymatch type of call with
    | context [match ?condition with Some _ => _ | None => _ end] => destruct condition eqn:?
    | context [if ?condition then _ else _] => destruct condition eqn:?
    end].

Theorem gateway_cast_pointer_origin memory value source target object offset :
  Cop.sem_cast value source target memory = Some (Vptr object offset) ->
  exists original, value = Vptr object original.
Proof.
  unfold Cop.sem_cast; destruct (Cop.classify_cast source target); destruct value; intro CALL;
    gateway_pointer_origin_cases CALL; try (inversion CALL; subst; eexists; reflexivity).
Qed.

Lemma gateway_binarith_pointer_origin sem_int sem_long sem_float sem_single
    first first_type second second_type memory object offset :
  (forall sign left right, sem_int sign left right <> Some (Vptr object offset)) ->
  (forall sign left right, sem_long sign left right <> Some (Vptr object offset)) ->
  (forall left right, sem_float left right <> Some (Vptr object offset)) ->
  (forall left right, sem_single left right <> Some (Vptr object offset)) ->
  Cop.sem_binarith sem_int sem_long sem_float sem_single
    first first_type second second_type memory <> Some (Vptr object offset).
Proof.
  intros INTEGER LONG FLOAT SINGLE CALL; unfold Cop.sem_binarith in CALL.
  destruct (Cop.classify_binarith first_type second_type);
    destruct (Cop.sem_cast first first_type _ memory) as [left |]; try discriminate;
    destruct (Cop.sem_cast second second_type _ memory) as [right |]; try discriminate;
    destruct left; destruct right; cbn in CALL; try discriminate;
    [eapply INTEGER |eapply LONG |eapply FLOAT |eapply SINGLE]; exact CALL.
Qed.

Theorem gateway_unary_pointer_impossible operation value source memory object offset :
  Cop.sem_unary_operation operation value source memory <> Some (Vptr object offset).
Proof.
  destruct operation; unfold Cop.sem_unary_operation, Cop.sem_notbool, Cop.sem_notint,
    Cop.sem_neg, Cop.sem_absfloat; intro CALL.
  - unfold option_map in CALL; destruct (Cop.bool_val value source memory) as [answer |];
      try discriminate; destruct answer; discriminate.
  - destruct (Cop.classify_notint source); destruct value; discriminate.
  - destruct (Cop.classify_neg source); destruct value; discriminate.
  - destruct (Cop.classify_neg source); destruct value; discriminate.
Qed.

Lemma gateway_add_pointer_origin environment first first_type second second_type memory object offset :
  Cop.sem_add environment first first_type second second_type memory = Some (Vptr object offset) ->
  (exists original, first = Vptr object original) \/ (exists original, second = Vptr object original).
Proof.
  unfold Cop.sem_add; destruct (Cop.classify_add first_type second_type).
  all: try solve [intro CALL; exfalso; eapply gateway_binarith_pointer_origin;
    [| | | |exact CALL]; intros; discriminate].
  all: unfold Cop.sem_add_ptr_int, Cop.sem_add_ptr_long;
    destruct first; destruct second; intro CALL;
    cbv beta iota zeta delta [Archi.ptr64] in CALL; try discriminate;
    inversion CALL; subst; first [left; eexists; reflexivity |right; eexists; reflexivity].
Qed.

Lemma gateway_sub_pointer_origin environment first first_type second second_type memory object offset :
  Cop.sem_sub environment first first_type second second_type memory = Some (Vptr object offset) ->
  exists original, first = Vptr object original.
Proof.
  unfold Cop.sem_sub; destruct (Cop.classify_sub first_type second_type).
  all: try solve [intro CALL; exfalso; eapply gateway_binarith_pointer_origin;
    [| | | |exact CALL]; intros; discriminate].
  all: destruct first; destruct second; intro CALL;
    cbv beta iota zeta delta [Archi.ptr64] in CALL; try discriminate.
  all: repeat match type of CALL with
    | (if ?answer then _ else _) = _ => destruct answer eqn:?
    end; try discriminate.
  all: try solve [inversion CALL; subst; eexists; reflexivity].
  all: unfold Vptrofs in CALL; cbv beta iota zeta delta [Archi.ptr64] in CALL; discriminate.
Qed.

Lemma gateway_comparison_pointer_impossible comparison first first_type second second_type memory object offset :
  Cop.sem_cmp comparison first first_type second second_type memory <> Some (Vptr object offset).
Proof.
  unfold Cop.sem_cmp, Cop.cmp_ptr; destruct (Cop.classify_cmp first_type second_type).
  all: try solve [intro CALL; eapply gateway_binarith_pointer_origin; [| | | |exact CALL];
    intros; unfold Val.of_bool; destruct (_ : bool); discriminate].
  all: destruct first; destruct second; intro CALL;
    cbv beta iota zeta delta [Archi.ptr64 option_map] in CALL; try discriminate.
  all: repeat match type of CALL with
    | match ?answer with Some _ => _ | None => _ end = _ => destruct answer eqn:?
    end; try discriminate.
  all: unfold Val.of_bool in CALL; destruct (_ : bool); discriminate.
Qed.

Theorem gateway_binary_pointer_origin environment operation first first_type second second_type memory object offset :
  Cop.sem_binary_operation environment operation first first_type second second_type memory = Some (Vptr object offset) ->
  (exists original, first = Vptr object original) \/ (exists original, second = Vptr object original).
Proof.
  destruct operation; cbn [Cop.sem_binary_operation].
  all: try solve [apply gateway_add_pointer_origin].
  all: try solve [intro CALL; left; eapply gateway_sub_pointer_origin; exact CALL].
  all: try solve [intro CALL; exfalso; eapply gateway_comparison_pointer_impossible; exact CALL].
  all: try solve [unfold Cop.sem_shl, Cop.sem_shr, Cop.sem_shift;
    destruct (Cop.classify_shift first_type second_type); destruct first; destruct second;
    intro CALL; gateway_pointer_origin_cases CALL].
  all: unfold Cop.sem_mul, Cop.sem_div, Cop.sem_mod, Cop.sem_and, Cop.sem_or, Cop.sem_xor;
    intro CALL; exfalso; eapply gateway_binarith_pointer_origin; [| | | |exact CALL];
    intros; repeat match goal with sign : signedness |- _ => destruct sign end;
    intro RESULT; gateway_pointer_origin_cases RESULT.
Qed.

Definition gateway_pointer_avoids (private : block -> Prop) (value : val) : Prop :=
  match value with Vptr object _ => ~ private object | _ => True end.

Theorem gateway_cast_avoids private memory value source target result :
  gateway_pointer_avoids private value -> Cop.sem_cast value source target memory = Some result ->
  gateway_pointer_avoids private result.
Proof.
  intros SAFE CAST; destruct result; try exact I.
  destruct (gateway_cast_pointer_origin _ _ _ _ _ _ CAST) as [original SAME];
    subst value; exact SAFE.
Qed.

Theorem gateway_binary_avoids private environment operation first first_type second second_type memory result :
  gateway_pointer_avoids private first -> gateway_pointer_avoids private second ->
  Cop.sem_binary_operation environment operation first first_type second second_type memory = Some result ->
  gateway_pointer_avoids private result.
Proof.
  intros FIRST SECOND RESULT; destruct result; try exact I.
  destruct (gateway_binary_pointer_origin _ _ _ _ _ _ _ _ _ RESULT)
    as [[original SAME] |[original SAME]]; [subst first; exact FIRST |subst second; exact SECOND].
Qed.
