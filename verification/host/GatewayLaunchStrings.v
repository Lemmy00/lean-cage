(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Regional loader bytes survive the actual caller frame. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayErrorRuntime GatewayCStringRetention
  GatewaySpawnVectors GatewaySpawnVectorMemory GatewaySpawnVectorStores.
Open Scope Z_scope.

Record gateway_global_launch_strings (readonly:block->Z->Prop) memory (engine:list Byte.int):Prop:={
  gateway_global_engine_string:forall symbol,
    Genv.find_symbol(Clight.globalenv prog)_host_engine=Some symbol->
    gateway_error_cstring memory(Vptr symbol Ptrofs.zero)engine /\
    gateway_cstring_covered readonly(Vptr symbol Ptrofs.zero)engine;
  gateway_global_path_string:forall symbol,
    Genv.find_symbol(Clight.globalenv prog)(spawn_vector_literal 3)=Some symbol->
    gateway_error_cstring memory(Vptr symbol Ptrofs.zero)spawn_path_bytes /\
    gateway_cstring_covered readonly(Vptr symbol Ptrofs.zero)spawn_path_bytes;
  gateway_global_locale_string:forall symbol,
    Genv.find_symbol(Clight.globalenv prog)(spawn_vector_literal 4)=Some symbol->
    gateway_error_cstring memory(Vptr symbol Ptrofs.zero)spawn_locale_bytes /\
    gateway_cstring_covered readonly(Vptr symbol Ptrofs.zero)spawn_locale_bytes
}.

Theorem gateway_global_launch_strings_retained readonly before after engine:
  gateway_global_launch_strings readonly before engine->Mem.unchanged_on readonly before after->
  gateway_global_launch_strings readonly after engine.
Proof.
  intros[ENGINE PATH LOCALE]FRAME;constructor;intros symbol SYMBOL.
  - destruct(ENGINE symbol SYMBOL)as[STRING COVER];split;[|exact COVER].
    eapply gateway_cstring_readonly_retained;eassumption.
  - destruct(PATH symbol SYMBOL)as[STRING COVER];split;[|exact COVER].
    eapply gateway_cstring_readonly_retained;eassumption.
  - destruct(LOCALE symbol SYMBOL)as[STRING COVER];split;[|exact COVER].
    eapply gateway_cstring_readonly_retained;eassumption.
Qed.

Theorem gateway_launch_strings_selected readonly memory engine environment blocks symbols:
  gateway_global_launch_strings readonly memory engine->
  gateway_spawn_vector_locations(Clight.globalenv prog)environment blocks symbols->
  gateway_error_cstring memory(Vptr(spawn_engine_symbol symbols)Ptrofs.zero)engine /\
  gateway_error_cstring memory(Vptr(spawn_path_symbol symbols)Ptrofs.zero)spawn_path_bytes /\
  gateway_error_cstring memory(Vptr(spawn_locale_symbol symbols)Ptrofs.zero)spawn_locale_bytes.
Proof.
  intros[ENGINE PATH LOCALE][CHILD ARGUMENTS ENVIRONMENT E_LOCAL P_LOCAL L_LOCAL E_SYMBOL P_SYMBOL L_SYMBOL].
  split;[exact(proj1(ENGINE _ E_SYMBOL))|].
  split;[exact(proj1(PATH _ P_SYMBOL))|exact(proj1(LOCALE _ L_SYMBOL))].
Qed.
