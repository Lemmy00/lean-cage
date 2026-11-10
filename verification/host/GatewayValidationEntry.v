(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original Outcome call allocates the actual validation output slots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayObjects GatewayPython GatewayOutcomeEntry
  GatewayOutcomeValidationContext GatewayFunctionEntry GatewayStackAllocation GatewayScopedMemory GatewayNativeRegions
  GatewayObjectDiscipline GatewayThreadRuntime GatewayLocalRuntime GatewayStreamInterface GatewayFramedRuntime GatewayCalls
  GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_validation_allocated_slots ge before environment after :
  alloc_variables ge empty_env before (fn_vars f_host_outcome_from) environment after ->
  forall identifier object ty, environment ! identifier = Some (object, ty) -> Mem.valid_access after Mint64 object 0 Writable.
Proof.
  intros ALLOC identifier object ty LOOK.
  destruct (in_dec peq identifier (map fst (fn_vars f_host_outcome_from))) as [MEMBER |ABSENT].
  - apply in_map_iff in MEMBER; destruct MEMBER as [[name actual_type] [SAME MEMBER]]; cbn in SAME; subst name.
    destruct (gateway_alloc_variables_member ge empty_env before (fn_vars f_host_outcome_from) environment after identifier actual_type
      ALLOC gateway_outcome_variables_unique MEMBER) as [actual [BINDING [FRESH PERMISSIONS]]].
    rewrite LOOK in BINDING; inversion BINDING; subst actual actual_type.
    assert (SIZE : sizeof ge ty = 8).
    { cbn [fn_vars] in MEMBER; repeat destruct MEMBER as [SAME |MEMBER]; try contradiction;
        inversion SAME; subst ty; reflexivity. }
    split.
    + intros position RANGE; eapply Mem.perm_implies; [apply PERMISSIONS; rewrite SIZE; cbn in RANGE; lia |constructor].
    + exists 0; reflexivity.
  - rewrite (gateway_alloc_variables_lookup ge empty_env before (fn_vars f_host_outcome_from) environment after identifier ALLOC ABSENT)
      in LOOK; rewrite PTree.gempty in LOOK; discriminate.
Qed.

Theorem gateway_actual_validation_entry {World Event} (backend : gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    ge ledger held reserved captured original protected source before world events value after next :
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source empty_env before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_outcome_from) [original] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix suffix memory current environment allocated,
    events = prefix ++ gateway_source E0 :: suffix /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_outcome_from) [original] Kstop before) world) prefix
      (gateway_live (Callstate (Internal f_host_outcome_from) [original] Kstop memory) current) /\
    function_entry2 ge f_host_outcome_from [original] memory environment (gateway_outcome_parameters original) allocated /\
    gateway_outcome_stack_buffers ge memory environment allocated /\
    gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment allocated current /\
    gateway_steps backend ge
      (gateway_live (State f_host_outcome_from (fn_body f_host_outcome_from) Kstop environment
        (gateway_outcome_parameters original) allocated) current) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros INPUT RUN.
  destruct (actual_gateway_function_entry_ambient backend ge f_host_outcome_from [original] Kstop before world events value Kstop after next RUN)
    as (prefix &suffix &memory &current &environment &parameters &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &REST).
  assert (CONTEXT : gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source empty_env memory current).
  { exact (gateway_ambient_run_ready backend ge _
      (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
        runtime references ledger held reserved captured original protected source empty_env)
      (Callstate (Internal f_host_outcome_from) [original] Kstop before) before world prefix memory current INPUT AMBIENT PREFIX). }
  destruct (gateway_outcome_entry_canonical ge original memory environment parameters allocated ENTRY) as [PARAMETERS ALLOC].
  subst parameters.
  pose proof (gateway_alloc_variables_frame ge empty_env memory (fn_vars f_host_outcome_from) environment allocated ALLOC) as FRAME.
  destruct (gateway_native_alloc_variables backend io (fun current object => gateway_native_private (python current) object) stable
    (gateway_python_discipline python objects detached) thread_errno runtime ge None empty_env memory (fn_vars f_host_outcome_from)
    environment allocated current ALLOC (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT)
    (gateway_native_environment_empty _ current memory)) as [READY NATIVE].
  assert (REGIONS : gateway_native_region_owned (fun current object => gateway_native_private (python current) object) protected memory current)
    by exact (gateway_validation_regions _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT).
  destruct (gateway_scope_allocation ge protected empty_env memory (fn_vars f_host_outcome_from) environment allocated ALLOC
    ltac:(intros object position MEMBER; exact (proj1 (REGIONS object position MEMBER)))
    ltac:(intros identifier object ty position LOOK; rewrite PTree.gempty in LOOK; discriminate)) as [AVOIDS REGION_FRAME].
  exists prefix, suffix, memory, current, environment, allocated.
  split; [exact EVENTS |split; [exact PREFIX |split; [exact ENTRY |split]]].
  - apply gateway_actual_outcome_allocations; exact ALLOC.
  - split; [|exact REST].
    destruct CONTEXT as [OLD_READY OLD_ENV SCOPE BUDGET CREDIT PRIVATE DESTROY SNAPSHOT OLD_REGIONS OLD_FRAME OLD_SLOTS OLD_OUTSIDE].
    constructor; try assumption.
    + eapply gateway_native_region_memory_frame; eassumption.
    + eapply Mem.unchanged_on_trans; eassumption.
    + eapply gateway_validation_allocated_slots; exact ALLOC.
    + intros identifier object ty LOOK position; exact (AVOIDS identifier object ty position LOOK).
Qed.
