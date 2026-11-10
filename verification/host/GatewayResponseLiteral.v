(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Reply magic comes from the actual retained native string initializer. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
Require Import ScalarMemory.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayLoaderRegions GatewayModuleRegions.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_response_magic:list Byte.int:=map Byte.repr[76;67;72;82;69;83;49;0].

Theorem actual_response_magic_initializer ge:
  gateway_program_definition ___stringlit_25 global_definitions=Some(Gvar v___stringlit_25) /\
  gvar_readonly v___stringlit_25=true /\gvar_volatile v___stringlit_25=false /\
  init_data_list_size(gvar_init v___stringlit_25)=9 /\
  Genv.bytes_of_init_data_list(Clight.genv_genv ge)(gvar_init v___stringlit_25)=
    inj_bytes(gateway_response_magic++[Byte.zero]).
Proof. repeat split;reflexivity. Qed.

Theorem gateway_response_magic_loaded ge memory:
  gateway_module_descriptor_regions ge memory->
  exists object,Genv.find_symbol ge ___stringlit_25=Some object /\
    Mem.loadbytes memory object 0 8=Some(inj_bytes gateway_response_magic) /\
    Mem.range_perm memory object 0 8 Cur Readable.
Proof.
  intro REGIONS.
  destruct(actual_response_magic_initializer ge)as[DEFINITION[READONLY[NONVOLATILE[SIZE BYTES]]]].
  destruct(REGIONS ___stringlit_25 v___stringlit_25 DEFINITION NONVOLATILE ltac:(rewrite SIZE;lia)(or_introl READONLY))
    as[object[ACTUAL[NONVOL[SYMBOL[BOUND READABLE LOADED VALUES]]]]].
  rewrite SIZE,BYTES in LOADED;rewrite SIZE in READABLE.
  exists object;split;[exact SYMBOL|]. split.
  - pose proof(loadbytes_slice memory object 0(inj_bytes(gateway_response_magic++[Byte.zero]))0 8)as SLICE.
    change(length(inj_bytes(gateway_response_magic++[Byte.zero])))with 9%nat in SLICE.
    specialize(SLICE LOADED ltac:(lia)ltac:(lia)ltac:(lia)).
    exact SLICE.
  - intros position INSIDE;apply READABLE;lia.
Qed.
