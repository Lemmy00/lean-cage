(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Both ownership projections cover the same actual prefixes and loss. *)
From Stdlib Require Import List PeanoNat.
From HostGateway Require Import GatewayMachine GatewayReferenceLedger GatewayReferenceExecution GatewayReferenceTokens.
Import ListNotations.

Definition gateway_token_selector(World Event:Type):Type:=
  nat->gateway_state World->gateway_event Event->gateway_state World->gateway_token_status->list gateway_token_action.

Inductive gateway_token_execution {World Event}(backend:gateway_backend World Event)ge
    (source_select:gateway_reference_selector World Event)(token_select:gateway_token_selector World Event):
    nat->gateway_state World->gateway_reference_status->gateway_token_status->list(gateway_event Event)->
      gateway_state World->gateway_reference_status->gateway_token_status->Prop:=
|gateway_token_execution_nil:forall position state source tokens,
    gateway_token_execution backend ge source_select token_select position state source tokens[]state source tokens
|gateway_token_execution_cons:forall position first source tokens event middle rest last final_source final_tokens,
    gateway_step backend ge first event middle->
    gateway_token_execution backend ge source_select token_select(S position)middle
      (gateway_reference_apply(source_select first event middle source)source)
      (gateway_token_batch(token_select position first event middle tokens)tokens)rest last final_source final_tokens->
    gateway_token_execution backend ge source_select token_select position first source tokens(event::rest)last final_source final_tokens.

Theorem gateway_token_execution_erases {World Event}(backend:gateway_backend World Event)ge source_select token_select
    position first source tokens events last final_source final_tokens:
  gateway_token_execution backend ge source_select token_select position first source tokens events last final_source final_tokens->
  gateway_steps backend ge first events last.
Proof. intro RUN;induction RUN;[constructor|econstructor;eassumption]. Qed.

Theorem gateway_token_execution_source {World Event}(backend:gateway_backend World Event)ge source_select token_select
    position first source tokens events last final_source final_tokens:
  gateway_token_execution backend ge source_select token_select position first source tokens events last final_source final_tokens->
  gateway_reference_execution backend ge source_select first source events last final_source.
Proof. intro RUN;induction RUN;[constructor|econstructor;eassumption]. Qed.

(* The selectors are total instrumentation. Unknown or mismatching events
   produce sticky invalid status; they never remove a physical execution. *)
Theorem gateway_token_execution_covers {World Event}(backend:gateway_backend World Event)ge source_select token_select
    first events last:
  gateway_steps backend ge first events last->forall position source tokens,
  exists final_source final_tokens,
    gateway_token_execution backend ge source_select token_select position first source tokens events last final_source final_tokens.
Proof.
  intro RUN;induction RUN;intros position source tokens.
  - exists source,tokens;constructor.
  - destruct(IHRUN(S position)(gateway_reference_apply(source_select first observed middle source)source)
      (gateway_token_batch(token_select position first observed middle tokens)tokens))as(final_source &final_tokens &TAIL).
    exists final_source,final_tokens;econstructor;eassumption.
Qed.

Theorem gateway_token_execution_append {World Event}(backend:gateway_backend World Event)ge source_select token_select
    position first source tokens prefix middle intermediate_source intermediate_tokens suffix last final_source final_tokens:
  gateway_token_execution backend ge source_select token_select position first source tokens prefix middle intermediate_source intermediate_tokens->
  gateway_token_execution backend ge source_select token_select(position+length prefix)middle intermediate_source intermediate_tokens
    suffix last final_source final_tokens->
  gateway_token_execution backend ge source_select token_select position first source tokens(prefix++suffix)last final_source final_tokens.
Proof.
  intro PREFIX;induction PREFIX;cbn;intro SUFFIX.
  - rewrite Nat.add_0_r in SUFFIX;exact SUFFIX.
  - econstructor;[exact H|]. apply IHPREFIX;rewrite Nat.add_succ_r in SUFFIX;exact SUFFIX.
Qed.

Theorem gateway_token_execution_split {World Event}(backend:gateway_backend World Event)ge source_select token_select
    position first source tokens prefix suffix last final_source final_tokens:
  gateway_token_execution backend ge source_select token_select position first source tokens(prefix++suffix)last final_source final_tokens->
  exists middle intermediate_source intermediate_tokens,
    gateway_token_execution backend ge source_select token_select position first source tokens prefix middle intermediate_source intermediate_tokens /\
    gateway_token_execution backend ge source_select token_select(position+length prefix)middle intermediate_source intermediate_tokens
      suffix last final_source final_tokens.
Proof.
  revert position first source tokens;induction prefix as[|event prefix IH];intros position first source tokens RUN;cbn in RUN.
  - exists first,source,tokens;rewrite Nat.add_0_r;split;[constructor|exact RUN].
  - inversion RUN as[|start_position start initial_source initial_tokens observed following rest terminal final_s final_t HEAD TAIL];subst.
    destruct(IH _ _ _ _ TAIL)as(middle &intermediate_source &intermediate_tokens &PREFIX &SUFFIX).
    exists middle,intermediate_source,intermediate_tokens;split;[econstructor;eassumption|].
    cbn;rewrite Nat.add_succ_r;exact SUFFIX.
Qed.

Theorem gateway_token_execution_invalid_stays {World Event}(backend:gateway_backend World Event)ge source_select token_select
    position first source reason events last final_source final_tokens:
  gateway_token_execution backend ge source_select token_select position first source(gateway_tokens_invalid reason)events
    last final_source final_tokens->final_tokens=gateway_tokens_invalid reason.
Proof.
  revert position first source;induction events as[|event rest IH];intros position first source RUN.
  - inversion RUN;reflexivity.
  - inversion RUN as[|start_position start initial_source initial_tokens observed following remaining terminal final_s final_t HEAD TAIL];subst.
    rewrite gateway_token_invalid_batch in TAIL;eapply IH;exact TAIL.
Qed.
