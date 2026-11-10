(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual native stack allocation establishes separate packet buffers. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps AST Values Memory Ctypes Clight.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_alloc_variables_frame ge initial before variables environment after:
  alloc_variables ge initial before variables environment after->
  Mem.unchanged_on(fun _ _=>True)before after.
Proof.
  intro ALLOC;induction ALLOC;[apply Mem.unchanged_on_refl|].
  eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;eassumption|exact IHALLOC].
Qed.

Lemma gateway_alloc_variables_lookup ge initial before variables environment after identifier:
  alloc_variables ge initial before variables environment after->
  ~In identifier(map fst variables)->environment!identifier=initial!identifier.
Proof.
  intro ALLOC;induction ALLOC;intro ABSENT;[reflexivity|].
  cbn in ABSENT;rewrite IHALLOC by tauto;apply PTree.gso;intro SAME;subst;tauto.
Qed.

Lemma gateway_alloc_variables_member ge initial before variables environment after identifier ty:
  alloc_variables ge initial before variables environment after->
  list_norepet(map fst variables)->In(identifier,ty)variables->
  exists object,environment!identifier=Some(object,ty) /\~Mem.valid_block before object /\
    Mem.range_perm after object 0(sizeof ge ty)Cur Freeable.
Proof.
  intro ALLOC;induction ALLOC;intros UNIQUE MEMBER;[contradiction|].
  cbn in UNIQUE;inversion UNIQUE;subst.
  destruct MEMBER as[SAME|LATER].
  - inversion SAME;subst identifier ty.
    exists b1;split.
    + rewrite(gateway_alloc_variables_lookup ge _ _ _ _ _ id ALLOC)by assumption;apply PTree.gss.
    + split;[eapply Mem.fresh_block_alloc;eassumption|].
      intros position RANGE.
      eapply Mem.perm_unchanged_on;[eapply gateway_alloc_variables_frame;exact ALLOC|exact I|].
      eapply Mem.perm_alloc_2;eassumption.
  - destruct(IHALLOC ltac:(assumption)LATER)as[object[LOOK[FRESH PERMISSIONS]]].
    exists object;split;[exact LOOK|]. split;[|exact PERMISSIONS].
    intro LIVE;apply FRESH;eapply Mem.valid_block_alloc;eassumption.
Qed.

Definition gateway_stack_environment(memory:mem)(environment:env):Prop:=
  (forall identifier object ty,environment!identifier=Some(object,ty)->Mem.valid_block memory object) /\
  (forall first second object other first_type second_type,
    environment!first=Some(object,first_type)->environment!second=Some(other,second_type)->
    first<>second->object<>other).

Lemma gateway_empty_stack_environment memory:gateway_stack_environment memory empty_env.
Proof.
  split;intros;match goal with LOOK:empty_env!_=Some _|-_=>rewrite PTree.gempty in LOOK;discriminate end.
Qed.

Lemma gateway_alloc_variables_stack ge initial before variables environment after:
  alloc_variables ge initial before variables environment after->
  gateway_stack_environment before initial->gateway_stack_environment after environment.
Proof.
  intro ALLOC;induction ALLOC;intro INPUT;[exact INPUT|].
  apply IHALLOC;destruct INPUT as[LIVE DISTINCT];split.
  - intros identifier object other LOOK.
    destruct(peq identifier id)as[SAME|DIFFERENT].
    + subst identifier;rewrite PTree.gss in LOOK;inversion LOOK;subst;eapply Mem.valid_new_block;eassumption.
    + rewrite PTree.gso in LOOK by exact DIFFERENT;eapply Mem.valid_block_alloc;[eassumption|eapply LIVE;eassumption].
  - intros first second object other first_type second_type FIRST SECOND DIFFERENT.
    destruct(peq first id)as[FIRST_ID|FIRST_ID];destruct(peq second id)as[SECOND_ID|SECOND_ID].
    + congruence.
    + subst first;rewrite PTree.gss in FIRST;inversion FIRST;subst object first_type.
      rewrite PTree.gso in SECOND by exact SECOND_ID.
      intro SAME;subst other;eapply Mem.fresh_block_alloc;[eassumption|eapply LIVE;exact SECOND].
    + subst second;rewrite PTree.gss in SECOND;inversion SECOND;subst other second_type.
      rewrite PTree.gso in FIRST by exact FIRST_ID.
      intro SAME;subst object;eapply Mem.fresh_block_alloc;[eassumption|eapply LIVE;exact FIRST].
    + rewrite PTree.gso in FIRST by exact FIRST_ID;rewrite PTree.gso in SECOND by exact SECOND_ID.
      eapply DISTINCT;eassumption.
Qed.
