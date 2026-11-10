(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One actual mandatory source cut retains both caller temporary facts. *)
From Stdlib Require Import List Classical_Prop.
From compcert Require Import Maps AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayMandatoryCut GatewayFailurePaths GatewayReturns GatewayOperations.
Import ListNotations.

Lemma gateway_mandatory_nested_stop owner environment protected expected marker tail continuation :
  call_cont continuation = Kstop ->
  ~ gateway_mandatory_nested owner environment protected expected marker tail continuation.
Proof. induction continuation; cbn; intros STOP; try discriminate; tauto. Qed.

Lemma gateway_mandatory_at_other owner environment first first_value second second_value marker tail source :
  call_cont tail = Kstop -> gateway_mandatory_at owner environment first first_value marker tail source ->
  gateway_mandatory_source owner environment second second_value marker tail source ->
  gateway_mandatory_at owner environment second second_value marker tail source.
Proof.
  intros STOP [parameters [memory [SOURCE VALUE]]] OTHER; subst source.
  destruct OTHER as [[_ [_ [SECOND _]]] |NESTED].
  - exists parameters, memory; split; [reflexivity |exact SECOND].
  - exfalso; exact (gateway_mandatory_nested_stop _ _ _ _ _ _ _ STOP NESTED).
Qed.

Theorem gateway_mandatory_pair_cut {World Event} (backend : gateway_backend World Event) ge
    owner environment first first_value second second_value marker tail source world events value after next :
  gateway_pointer_return owner -> gateway_mandatory_sequential tail = true -> call_cont tail = Kstop ->
  gateway_mandatory_source owner environment first first_value marker tail source ->
  gateway_mandatory_source owner environment second second_value marker tail source ->
  gateway_steps backend ge (gateway_live source world) events (gateway_live (Returnstate value Kstop after) next) ->
  value <> Vnullptr -> exists prefix suffix parameters memory current,
    events = prefix ++ suffix /\ parameters ! first = Some first_value /\ parameters ! second = Some second_value /\
    gateway_steps backend ge (gateway_live source world) prefix
      (gateway_live (State owner marker tail environment parameters memory) current) /\
    gateway_steps backend ge (gateway_live (State owner marker tail environment parameters memory) current) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros POINTER SEQUENTIAL STOP; revert source world.
  induction events as [|event rest IH]; intros source world FIRST SECOND RUN NONNULL.
  - inversion RUN; subst; cbn in FIRST; destruct FIRST as [IMPOSSIBLE |[RETURN NULL]]; contradiction.
  - destruct (classic (gateway_mandatory_at owner environment first first_value marker tail source)) as [AT |NOT_AT].
    + pose proof (gateway_mandatory_at_other _ _ _ _ _ _ _ _ _ STOP AT SECOND) as OTHER.
      destruct AT as [parameters [memory [SOURCE FIRST_VALUE]]]; subst source.
      destruct OTHER as [selected [changed [SAME SECOND_VALUE]]]; inversion SAME; subst selected changed.
      exists [], (event :: rest), parameters, memory, world; cbn.
      split; [reflexivity |split; [exact FIRST_VALUE |split; [exact SECOND_VALUE |split; [constructor |exact RUN]]]].
    + assert (NOT_SECOND : ~ gateway_mandatory_at owner environment second second_value marker tail source).
      { intro AT; apply NOT_AT; eapply gateway_mandatory_at_other; [exact STOP |exact AT |exact FIRST]. }
      inversion RUN as [|start observed middle remaining last HEAD TAIL]; subst.
      destruct middle as [target current |memory current].
      * destruct (gateway_mandatory_live_step backend ge _ _ _ _ _ _ _ _ _ _ _
          POINTER SEQUENTIAL FIRST NOT_AT HEAD) as [READY_FIRST |BLOCKED].
        -- destruct (gateway_mandatory_live_step backend ge _ _ _ _ _ _ _ _ _ _ _
            POINTER SEQUENTIAL SECOND NOT_SECOND HEAD) as [READY_SECOND |BLOCKED].
           ++ destruct (IH target current READY_FIRST READY_SECOND TAIL NONNULL)
                as (prefix & suffix & parameters & memory & reached & EVENTS & FIRST_VALUE & SECOND_VALUE & PREFIX & SUFFIX).
              exists (event :: prefix), suffix, parameters, memory, reached.
              split; [cbn; congruence |split; [exact FIRST_VALUE |split; [exact SECOND_VALUE |split; [|exact SUFFIX]]]].
              econstructor; [exact HEAD |exact PREFIX].
           ++ exfalso; eapply gateway_blocked_cannot_return; eassumption.
        -- exfalso; eapply gateway_blocked_cannot_return; eassumption.
      * destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ IMPOSSIBLE]; discriminate.
Qed.
