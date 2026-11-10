(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Existing logical allocation cells retain every Cur/Max
   permission or are fully revoked; address reuse receives a new allocation identity. *)
From Stdlib Require Import ZArith List Lia Classical_Prop.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Cop Clight.
Require Import Machine.
From HostGateway Require Import GatewayPermissionScopes.
Import ListNotations.

Record gateway_permission_survival(before after:mem):Prop:={
  gateway_survival_live:forall object,Mem.valid_block before object->Mem.valid_block after object;
  gateway_survival_cell:forall object position,Mem.valid_block before object->
    (forall kind permission,Mem.perm before object position kind permission<->Mem.perm after object position kind permission) \/
    (forall kind permission,~Mem.perm after object position kind permission)
}.

Lemma gateway_survival_refl memory:gateway_permission_survival memory memory.
Proof. split;[intros;assumption|intros;left;intros;tauto]. Qed.
Lemma gateway_survival_trans before middle after:
  gateway_permission_survival before middle->gateway_permission_survival middle after->gateway_permission_survival before after.
Proof.
  intros[FIRST_LIVE FIRST][SECOND_LIVE SECOND];split;[auto|]. intros object position LIVE.
  destruct(FIRST object position LIVE)as[OLD|REVOKED];
    destruct(SECOND object position(FIRST_LIVE object LIVE))as[NEXT|ABSENT].
  - left;intros;etransitivity;[apply OLD|apply NEXT].
  - right;exact ABSENT.
  - right;intros kind permission PRESENT;apply(REVOKED kind permission);apply(proj2(NEXT kind permission));exact PRESENT.
  - right;exact ABSENT.
Qed.
Lemma gateway_survival_exact before after:
  gateway_permission_frame(fun _ _=>True)before after->gateway_permission_survival before after.
Proof. intros[LIVE CELLS];split;[exact LIVE|intros;left;intros;apply CELLS;auto]. Qed.

Lemma gateway_survival_alloc before after object low high:
  Mem.alloc before low high=(after,object)->gateway_permission_survival before after.
Proof.
  intro ALLOC;split;[intros;eapply Mem.valid_block_alloc;eassumption|]. intros candidate position LIVE;left;intros kind permission;split.
  - eapply Mem.perm_alloc_1;exact ALLOC.
  - intro PERM;eapply Mem.perm_alloc_4;[exact ALLOC|exact PERM|].
    intro SAME;subst candidate;exact(Mem.fresh_block_alloc _ _ _ _ _ ALLOC LIVE).
Qed.
Lemma gateway_survival_store before after chunk object offset value:
  Mem.store chunk before object offset value=Some after->gateway_permission_survival before after.
Proof. intro STORE;apply gateway_survival_exact;eapply gateway_permission_store;exact STORE. Qed.
Lemma gateway_survival_storebytes before after object offset bytes:
  Mem.storebytes before object offset bytes=Some after->gateway_permission_survival before after.
Proof. intro STORE;apply gateway_survival_exact;eapply gateway_permission_storebytes;exact STORE. Qed.

Lemma gateway_survival_free before after object low high:
  Mem.free before object low high=Some after->gateway_permission_survival before after.
Proof.
  intro FREE;split.
  - intros candidate LIVE;unfold Mem.valid_block in *;rewrite(Mem.nextblock_free _ _ _ _ _ FREE);exact LIVE.
  - intros candidate position LIVE;destruct(Classical_Prop.classic(candidate=object /\(low<=position<high)%Z))as[[SAME RANGE]|OUTSIDE].
    + subst candidate;right;intros kind permission;eapply Mem.perm_free_2;[exact FREE|exact RANGE].
    + left;intros kind permission;split.
      * intro PERM;eapply Mem.perm_free_1;[exact FREE| |exact PERM]. destruct(Pos.eq_dec candidate object);[subst candidate;right;lia|left;assumption].
      * intro PERM;eapply Mem.perm_free_3;[exact FREE|exact PERM].
Qed.
Lemma gateway_survival_free_list regions before after:
  Mem.free_list before regions=Some after->gateway_permission_survival before after.
Proof.
  revert before;induction regions as[|[[object low]high]rest IH];intros before FREE;cbn in FREE.
  - inversion FREE;subst;apply gateway_survival_refl.
  - destruct(Mem.free before object low high)as[middle|]eqn:FIRST;[|discriminate].
    eapply gateway_survival_trans;[eapply gateway_survival_free;exact FIRST|apply IH;exact FREE].
Qed.
Lemma gateway_survival_variables ge environment before variables next after:
  alloc_variables ge environment before variables next after->gateway_permission_survival before after.
Proof.
  intro ALLOC;induction ALLOC;[apply gateway_survival_refl|].
  eapply gateway_survival_trans;[eapply gateway_survival_alloc;eassumption|exact IHALLOC].
Qed.

Lemma gateway_survival_assignment ce ty before object offset bitfield value after:
  assign_loc ce ty before object offset bitfield value after->gateway_permission_survival before after.
Proof.
  intro ASSIGN;apply gateway_survival_exact;eapply gateway_assignment_permission;exact ASSIGN.
Qed.

Theorem gateway_internal_permission_survival ge source trace after:
  internal_state source->step2 ge source trace after->gateway_permission_survival(memory_of source)(memory_of after).
Proof.
  intros INTERNAL STEP;inversion STEP;subst;try contradiction;cbn[memory_of].
  all:try apply gateway_survival_refl.
  - eapply gateway_survival_assignment;eassumption.
  - eapply gateway_survival_free_list;eassumption.
  - eapply gateway_survival_free_list;eassumption.
  - eapply gateway_survival_free_list;eassumption.
  - match goal with ENTRY:function_entry2 _ _ _ _ _ _ _|-_=>inversion ENTRY;subst end.
    eapply gateway_survival_variables;eassumption.
Qed.

Theorem gateway_survival_observed_permissions protected before after:
  gateway_permission_survival before after->
  (forall object position,protected object position->exists kind permission,Mem.perm after object position kind permission)->
  gateway_permission_frame protected before after.
Proof.
  intros[LIVE CELLS]OBSERVED;split;[exact LIVE|]. intros object position kind permission MEMBER VALID.
  destruct(CELLS object position VALID)as[SAME|REVOKED];[apply SAME|].
  destruct(OBSERVED object position MEMBER)as[selected[authority PRESENT]];exfalso;exact(REVOKED selected authority PRESENT).
Qed.
