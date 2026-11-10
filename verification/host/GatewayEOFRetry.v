(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual interrupted EOF receives take the source's retry branch. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayRuntime GatewayRuntimeABI GatewayStreamInterface GatewayReadonly GatewayRuntimeCuts GatewayBoundaryValues GatewayErrnoFragment
  GatewayExchangeTransport GatewayEOFSource GatewayEOFReceiveSource GatewayEOFCountSource GatewayEOFCountError.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_eof_critical identifier:=Pos.eqb identifier _count||Pos.eqb identifier _result.

Theorem actual_eof_negative_retry {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (io:Event->option gateway_native_io)property(CLOSED:gateway_ambient_closed backend property)
    environment temporaries before world events value after next:
  environment!___errno_location=None->gateway_function_binding ge ___errno_location gateway_errno_location_definition->
  (forall memory current returned changed future observed,property memory current->
    gateway_runtime_operation backend gateway_errno_location_definition[]memory current returned changed future observed->
    property changed future /\io observed=None)->
  temporaries!_count=Some(Vlong(Int64.repr(-1)))->property before world->value<>Vnullptr->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\gateway_errno_silent io prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange exchange_eof_loop exchange_eof_cont environment final_temps memory)current) /\
    property memory current /\gateway_errno_temps gateway_eof_critical temporaries final_temps /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange exchange_eof_loop exchange_eof_cont environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros LOCAL FUNCTION OPERATION COUNT READY NONNULL RUN.
  destruct(gateway_actual_errno_fragment backend ge io property CLOSED gateway_eof_critical f_host_exchange environment
    LOCAL FUNCTION OPERATION exchange_eof_retry_compute ltac:(vm_compute;reflexivity)
    exchange_eof_retry_cont temporaries before world events value after next READY RUN)
    as(p1&r1&m1&w1&temps1&E1&Q1&P1&C1&F1&S1).
  assert(RETAINED:temps1!_count=Some(Vlong(Int64.repr(-1)))).
  { rewrite(F1 _count ltac:(reflexivity));exact COUNT. }
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (State f_host_exchange Sskip exchange_eof_retry_cont environment temps1 m1)
    (State f_host_exchange exchange_eof_retry_test(Kseq exchange_eof_after_retry exchange_eof_iteration_cont)environment temps1 m1)
    m1 w1 r1 value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)C1 S1)
    as(p2&r2&m2&w2&E2&Q2&P2&C2&S2).
  cbn[gateway_replace_memory]in P2,S2.
  destruct(gateway_boundary_if_cut backend ge property CLOSED f_host_exchange(Etempvar _t'48 tint)Scontinue Sskip
    (Kseq exchange_eof_after_retry exchange_eof_iteration_cont)environment temps1 m2 w2 r2(Returnstate value Kstop after)next
    I C2 S2)
    as(p3&r3&m3&w3&tested&branch&E3&Q3&P3&EXPR&BOOL&C3&S3).
  destruct branch.
  - destruct(gateway_memory_prefix_cut backend ge _ _ _ _ m3 w3 r3(Returnstate value Kstop after)next
      (actual_eof_retry_continue_path backend ge property CLOSED environment temps1 m3)I C3 S3)
      as(p4&suffix&memory&current&E4&Q4&P4&FINAL&SUFFIX).
    cbn[gateway_replace_memory]in P4,SUFFIX.
    exists(p1++p2++gateway_source E0::p3++gateway_source E0::p4),suffix,memory,current,temps1.
    split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;cbn[app];repeat rewrite<-app_assoc;reflexivity|]. split.
    + apply gateway_errno_silent_append;[exact Q1|].
      apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact Q2|].
      apply gateway_errno_silent_append with(first:=[gateway_source E0]);[apply gateway_errno_silent_source|].
      apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact Q3|].
      apply gateway_errno_silent_append with(first:=[gateway_source E0]);[apply gateway_errno_silent_source|].
      apply gateway_errno_silent_quiet;exact Q4.
    + split.
      * eapply gateway_steps_append;[exact P1|]. eapply gateway_steps_append;[exact P2|].
        econstructor;[apply gateway_internal;[cbn;tauto|constructor]|].
        eapply gateway_steps_append;[exact P3|].
        econstructor;[apply gateway_internal;[cbn;tauto|eapply step_ifthenelse;[exact EXPR|exact BOOL]]|exact P4].
      * split;[exact FINAL|]. split;assumption.
  - exfalso;apply NONNULL.
    exact(actual_eof_nonzero_skipped_failure backend ge environment temps1 m3(Int64.repr(-1))RETAINED
      ltac:(reflexivity)m3 w3 r3 value after next S3).
Qed.
