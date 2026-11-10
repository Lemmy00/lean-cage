(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Native counts are an actual fixed-token projection, not all callback roots. *)
From Stdlib Require Import List PeanoNat Lia.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayPython GatewayReferenceRuntime GatewayReferenceTokens.
Import ListNotations.

Definition gateway_token_all_count pool pointer:=count_occ Val.eq(map gateway_token_pointer pool)pointer.
Definition gateway_token_physical_budget pool python:Prop:=
  forall pointer,(gateway_token_all_count pool pointer<=python_strong python pointer)%nat.

Lemma gateway_token_projection_bounded current captured pool pointer:
  (gateway_token_count current captured pool pointer<=gateway_token_all_count pool pointer)%nat.
Proof.
  unfold gateway_token_all_count;induction pool as[|head rest IH];cbn[gateway_token_count map count_occ];[lia|].
  destruct(gateway_token_selected current captured head);destruct(Val.eq(gateway_token_pointer head)pointer);cbn;lia.
Qed.

Definition gateway_token_project_python current captured pool(physical:python_world):python_world:={|
  python_values:=python_values physical;
  python_strong:=python_strong physical;
  python_native_strong:=gateway_token_count current captured pool;
  python_runtime_owned:=python_runtime_owned physical;
  python_gil:=python_gil physical;
  python_pending:=python_pending physical
|}.

Definition gateway_token_python_for {World}current captured(pool:World->list gateway_reference_token)
    (physical:World->python_world):World->python_world:=
  fun world=>gateway_token_project_python current captured(pool world)(physical world).

Theorem gateway_token_project_valid current captured pool physical memory:
  python_world_valid physical memory->gateway_token_physical_budget pool physical->
  python_world_valid(gateway_token_project_python current captured pool physical)memory.
Proof.
  intros[COUNTS[BYTES[OWNED VALUES]]]BUDGET;split.
  - intro pointer;eapply Nat.le_trans;[apply gateway_token_projection_bounded|apply BUDGET].
  - exact(conj BYTES(conj OWNED VALUES)).
Qed.

Lemma gateway_token_project_live current captured pool physical pointer:
  python_live(gateway_token_project_python current captured pool physical)pointer<->python_live physical pointer.
Proof. reflexivity. Qed.

Theorem gateway_token_project_credit current captured token before_pool after_pool physical next_physical:
  gateway_token_selected current captured token=true->
  gateway_token_apply(gateway_token_mint token)(gateway_tokens_valid before_pool)=gateway_tokens_valid after_pool->
  gateway_reference_credit(gateway_token_project_python current captured before_pool physical)
    (gateway_token_project_python current captured after_pool next_physical)(gateway_token_pointer token).
Proof.
  intros SELECTED APPLY;destruct(gateway_token_mint_selected_count _ _ _ _ _ SELECTED APPLY)as[TARGET OTHERS].
  constructor;assumption.
Qed.

Theorem gateway_token_project_foreign current captured action before_pool after_pool physical next_physical:
  gateway_token_foreign current captured action->
  gateway_token_apply action(gateway_tokens_valid before_pool)=gateway_tokens_valid after_pool->
  forall pointer,python_native_strong(gateway_token_project_python current captured after_pool next_physical)pointer=
    python_native_strong(gateway_token_project_python current captured before_pool physical)pointer.
Proof. intros FOREIGN APPLY pointer;eapply gateway_token_foreign_count;eassumption. Qed.

Theorem gateway_token_project_release current captured key pointer before_pool after_pool physical next_physical:
  (forall selected,gateway_token_identity selected=key->gateway_token_selected current captured selected=true)->
  gateway_token_apply(gateway_token_release key pointer)(gateway_tokens_valid before_pool)=gateway_tokens_valid after_pool->
  python_native_strong(gateway_token_project_python current captured before_pool physical)pointer=
    S(python_native_strong(gateway_token_project_python current captured after_pool next_physical)pointer) /\
  (forall other,other<>pointer->
    python_native_strong(gateway_token_project_python current captured after_pool next_physical)other=
      python_native_strong(gateway_token_project_python current captured before_pool physical)other).
Proof. intros SELECTED APPLY;exact(gateway_token_remove_selected_count _ _ _ _ _ _ SELECTED APPLY). Qed.

Theorem gateway_token_project_handoff current captured key pointer before_pool after_pool physical next_physical:
  (forall selected,gateway_token_identity selected=key->gateway_token_selected current captured selected=true)->
  gateway_token_apply(gateway_token_handoff key pointer)(gateway_tokens_valid before_pool)=gateway_tokens_valid after_pool->
  python_native_strong(gateway_token_project_python current captured before_pool physical)pointer=
    S(python_native_strong(gateway_token_project_python current captured after_pool next_physical)pointer) /\
  (forall other,other<>pointer->
    python_native_strong(gateway_token_project_python current captured after_pool next_physical)other=
      python_native_strong(gateway_token_project_python current captured before_pool physical)other).
Proof. intros SELECTED APPLY;exact(gateway_token_remove_selected_count _ _ _ _ _ _ SELECTED APPLY). Qed.

Theorem gateway_token_project_callback_credit current captured prefix suffix token before_pool after_pool physical next_physical:
  Forall(gateway_token_foreign current captured)prefix->Forall(gateway_token_foreign current captured)suffix->
  gateway_token_selected current captured token=true->
  gateway_token_batch(prefix++gateway_token_mint token::suffix)(gateway_tokens_valid before_pool)=gateway_tokens_valid after_pool->
  gateway_reference_credit(gateway_token_project_python current captured before_pool physical)
    (gateway_token_project_python current captured after_pool next_physical)(gateway_token_pointer token).
Proof.
  intros BEFORE AFTER SELECTED EXECUTION.
  destruct(gateway_token_valid_batch_cut prefix(gateway_token_mint token::suffix)before_pool after_pool EXECUTION)
    as(middle &PREFIX &REST).
  change(gateway_token_batch suffix(gateway_token_apply(gateway_token_mint token)(gateway_tokens_valid middle))=
    gateway_tokens_valid after_pool)in REST.
  destruct(gateway_token_apply(gateway_token_mint token)(gateway_tokens_valid middle))as[minted|reason]eqn:MINT.
  - pose proof(gateway_token_foreign_batch_count _ _ _ _ _ BEFORE PREFIX)as BEFORE_COUNTS.
    pose proof(gateway_token_foreign_batch_count _ _ _ _ _ AFTER REST)as AFTER_COUNTS.
    destruct(gateway_token_mint_selected_count _ _ _ _ _ SELECTED MINT)as[CREDIT OTHERS].
    constructor;cbn.
    + rewrite AFTER_COUNTS,CREDIT,BEFORE_COUNTS;reflexivity.
    + intros pointer DIFFERENT;rewrite AFTER_COUNTS,OTHERS,BEFORE_COUNTS;[reflexivity|exact DIFFERENT].
  - rewrite gateway_token_invalid_batch in REST;discriminate.
Qed.

Theorem gateway_token_unselected_strong_gap current captured pool token physical:
  In token pool->gateway_token_selected current captured token=false->gateway_token_physical_budget pool physical->
  (python_native_strong(gateway_token_project_python current captured pool physical)(gateway_token_pointer token)<
    python_strong physical(gateway_token_pointer token))%nat.
Proof.
  intros MEMBER OUTSIDE BUDGET.
  assert(GAP:(gateway_token_count current captured pool(gateway_token_pointer token)<
    gateway_token_all_count pool(gateway_token_pointer token))%nat).
  { clear BUDGET;unfold gateway_token_all_count;induction pool as[|head rest IH];[contradiction|].
    cbn[gateway_token_count map count_occ]. destruct MEMBER as[SAME|MEMBER].
    - subst head;rewrite OUTSIDE.
      destruct(Val.eq(gateway_token_pointer token)(gateway_token_pointer token));[|contradiction].
      pose proof(gateway_token_projection_bounded current captured rest(gateway_token_pointer token));unfold gateway_token_all_count in H;lia.
    - specialize(IH MEMBER).
      destruct(gateway_token_selected current captured head);destruct(Val.eq(gateway_token_pointer head)(gateway_token_pointer token));cbn;lia. }
  specialize(BUDGET(gateway_token_pointer token));cbn;lia.
Qed.
