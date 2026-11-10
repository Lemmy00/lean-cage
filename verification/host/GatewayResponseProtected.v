(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The selected magic literal is sampled from the actual retained snapshot. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayProtectedMemory GatewayProtectedThreads GatewayInitializerProtection
  GatewayResponseLiteral GatewayBootstrapRuntime GatewayModuleRegions.
Open Scope Z_scope.

Theorem gateway_response_magic_descriptor magic:
  Genv.find_symbol(Clight.globalenv prog)___stringlit_25=Some magic->
  gateway_descriptor_object(Clight.globalenv prog)magic /\gateway_immutable_object(Clight.globalenv prog)magic.
Proof.
  intro SYMBOL;split;exists ___stringlit_25,v___stringlit_25.
  - split;[reflexivity|]. split;[reflexivity|]. split;[change(0<9);lia|].
    split;[left;reflexivity|exact SYMBOL].
  - split;[reflexivity|]. split;[reflexivity|exact SYMBOL].
Qed.

Theorem gateway_response_literal_from_protected {World}native stable protected immutable snapshot memory world magic:
  @gateway_protected_memory World native protected immutable snapshot memory world->protected magic->immutable magic->
  Mem.loadbytes snapshot magic 0 8=Some(inj_bytes gateway_response_magic)->
  gateway_bootstrap_protected(gateway_protected_native native protected immutable)stable memory world
    (Vptr magic Ptrofs.zero)gateway_response_magic.
Proof.
  intros STATE SELECTED IMMUTABLE LOADED.
  exists magic,Ptrofs.zero;split;[reflexivity|]. split.
  - exists magic,Ptrofs.zero;split;[reflexivity|]. split;[change(8<=18446744073709551616);lia|].
    eapply Mem.loadbytes_unchanged_on;[exact(gateway_protected_snapshot _ _ _ _ _ _ STATE)| |exact LOADED].
    intros position INSIDE;exact SELECTED.
  - intros position INSIDE;left;split.
    + eapply gateway_protected_owned;[exact STATE|exact SELECTED].
    + intro AGAIN;exact IMMUTABLE.
Qed.
