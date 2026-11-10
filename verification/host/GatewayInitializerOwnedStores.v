(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Real class stores retain overwritten retry roots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayInitializerGlobalStores
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHistory
  GatewayReferenceAbandon GatewayReferenceOverwrite.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_initializer_owning_store {World Event} : gateway_history_selector World Event :=
  fun _ first observed _ _ =>
    match first, observed with
    | gateway_live (State _ (Sassign (Evar global _) (Etempvar temporary _)) continuation _ parameters _) _,
        gateway_source _ =>
        match parameters ! temporary with
        | Some value =>
            if Val.eq value Vnullptr then gateway_history_clear (gateway_reference_global global)
            else gateway_history_assign
              (gateway_reference_temporary (gateway_reference_depth continuation) temporary)
              (gateway_reference_global global)
        | None => gateway_history_current gateway_reference_unclassified
        end
    | _, _ => gateway_history_current gateway_reference_keep
    end.

Theorem gateway_initializer_owned_pointer_store {World Event} (backend : gateway_backend World Event)
    (python : World -> python_world) (ge : Clight.genv) global temporary symbol object offset parameters continuation before trace target
    world position ledger retired ticket :
  Genv.find_symbol ge global = Some symbol -> parameters ! temporary = Some (Vptr object offset) ->
  gateway_history_well_formed position ledger retired -> gateway_history_counts_fit ledger retired (python world) ->
  gateway_reference_owns ledger
    (gateway_reference_temporary (gateway_reference_depth continuation) temporary) ticket (Vptr object offset) ->
  step2 ge (State f_host_initialize (initializer_pointer_assignment global temporary)
    continuation empty_env parameters before) trace target ->
  exists after final archived,
    trace = E0 /\ target = State f_host_initialize Sskip continuation empty_env parameters after /\
    Mem.store Mptr before symbol 0 (Vptr object offset) = Some after /\
    Mem.load Mptr after symbol 0 = Some (Vptr object offset) /\
    gateway_history_execution backend ge gateway_initializer_owning_store position
      (gateway_live (State f_host_initialize (initializer_pointer_assignment global temporary)
        continuation empty_env parameters before) world)
      {| gateway_history_active := gateway_reference_valid ledger; gateway_history_abandoned := retired |}
      [gateway_source E0]
      (gateway_live target world)
      {| gateway_history_active := gateway_reference_valid final; gateway_history_abandoned := archived |} /\
    gateway_history_well_formed (S position) final archived /\
    gateway_history_counts_fit final archived (python world) /\
    gateway_reference_owns final (gateway_reference_global global) ticket (Vptr object offset) /\
    gateway_reference_place_value ge target (gateway_reference_global global) (Vptr object offset) /\
    (forall pointer, gateway_history_total_count final archived pointer =
      gateway_history_total_count ledger retired pointer).
Proof.
  intros SYMBOL VALUE FORMED FIT OWNED STEP.
  destruct (gateway_initializer_pointer_store ge global temporary symbol (Vptr object offset)
    parameters before continuation trace target SYMBOL VALUE STEP)
    as (after & TRACE & TARGET & STORE).
  assert (LOAD : Mem.load Mptr after symbol 0 = Some (Vptr object offset)).
  { pose proof (Mem.load_store_same _ _ _ _ _ _ STORE) as LOAD; exact LOAD. }
  destruct (gateway_history_assign_owned position ledger retired
    (gateway_reference_temporary (gateway_reference_depth continuation) temporary)
    (gateway_reference_global global) ticket (Vptr object offset) FORMED OWNED)
    as (final & archived & ASSIGN & NEXT_FORMED & NEXT_OWNED & COUNTS & RETAINED).
  exists after, final, archived; split; [exact TRACE |]. split; [exact TARGET |].
  split; [exact STORE |]. split; [exact LOAD |]. split.
  - econstructor.
    + apply gateway_internal; [exact I |rewrite <- TRACE; exact STEP].
    + cbn [gateway_initializer_owning_store initializer_pointer_assignment].
      rewrite VALUE; destruct (Val.eq (Vptr object offset) Vnullptr) as [BAD |NONNULL]; [discriminate BAD |].
      rewrite ASSIGN; constructor.
  - split; [exact NEXT_FORMED |]. split.
    + intro pointer; rewrite COUNTS; exact (FIT pointer).
    + split; [exact NEXT_OWNED |]. split.
      * rewrite TARGET; eapply gateway_reference_global_binding; eassumption.
      * exact COUNTS.
Qed.

Theorem gateway_initializer_null_pointer_store {World Event} (backend : gateway_backend World Event)
    (python : World -> python_world) (ge : Clight.genv) global temporary symbol
    parameters continuation before trace target world position ledger retired :
  Genv.find_symbol ge global = Some symbol -> parameters ! temporary = Some Vnullptr ->
  gateway_history_well_formed position ledger retired -> gateway_history_counts_fit ledger retired (python world) ->
  step2 ge (State f_host_initialize (initializer_pointer_assignment global temporary)
    continuation empty_env parameters before) trace target ->
  exists after final archived,
    trace = E0 /\ target = State f_host_initialize Sskip continuation empty_env parameters after /\
    Mem.store Mptr before symbol 0 Vnullptr = Some after /\ Mem.load Mptr after symbol 0 = Some Vnullptr /\
    gateway_history_execution backend ge gateway_initializer_owning_store position
      (gateway_live (State f_host_initialize (initializer_pointer_assignment global temporary)
        continuation empty_env parameters before) world)
      {| gateway_history_active := gateway_reference_valid ledger; gateway_history_abandoned := retired |}
      [gateway_source E0] (gateway_live target world)
      {| gateway_history_active := gateway_reference_valid final; gateway_history_abandoned := archived |} /\
    gateway_history_well_formed (S position) final archived /\
    gateway_history_counts_fit final archived (python world) /\
    gateway_reference_take (gateway_reference_global global) (gateway_reference_entries final) = None /\
    (forall pointer, gateway_history_total_count final archived pointer =
      gateway_history_total_count ledger retired pointer).
Proof.
  intros SYMBOL VALUE FORMED FIT STEP.
  destruct (gateway_initializer_pointer_store ge global temporary symbol Vnullptr
    parameters before continuation trace target SYMBOL VALUE STEP)
    as (after & TRACE & TARGET & STORE).
  assert (LOAD : Mem.load Mptr after symbol 0 = Some Vnullptr).
  { pose proof (Mem.load_store_same _ _ _ _ _ _ STORE) as LOAD; exact LOAD. }
  destruct (gateway_history_clear_owned position ledger retired (gateway_reference_global global) FORMED)
    as (final & archived & CLEAR & NEXT_FORMED & ABSENT & COUNTS).
  exists after, final, archived; split; [exact TRACE |]. split; [exact TARGET |].
  split; [exact STORE |]. split; [exact LOAD |]. split.
  - econstructor.
    + apply gateway_internal; [exact I |rewrite <- TRACE; exact STEP].
    + cbn [gateway_initializer_owning_store initializer_pointer_assignment].
      rewrite VALUE; destruct (Val.eq Vnullptr Vnullptr) as [_ |BAD]; [|contradict BAD; reflexivity].
      rewrite CLEAR; constructor.
  - split; [exact NEXT_FORMED |]. split.
    + intro pointer; rewrite COUNTS; exact (FIT pointer).
    + split; assumption.
Qed.
