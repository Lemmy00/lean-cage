(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual exchange allocation cannot shadow the fixed executable or SDK function. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewaySpawnVectors GatewayStackAllocation.
Import ListNotations.

Theorem actual_exchange_launch_globals_absent ge before environment after :
  alloc_variables ge empty_env before (fn_vars f_host_exchange) environment after ->
  environment ! _host_engine = None /\ environment ! (spawn_vector_literal 3) = None /\
  environment ! (spawn_vector_literal 4) = None /\ environment ! _posix_spawn = None.
Proof.
  intro ALLOC.
  assert (DOMAIN : forall identifier, ~ In identifier (map fst (fn_vars f_host_exchange)) ->
    environment ! identifier = None).
  { intros identifier ABSENT.
    rewrite (gateway_alloc_variables_lookup _ _ _ _ _ _ identifier ALLOC ABSENT); apply PTree.gempty. }
  repeat split; apply DOMAIN; cbn; intuition discriminate.
Qed.
