(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Strict Unicode mode comes from the actual initialized source literal. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayGlobals GatewayCancellationInputs GatewayObjects GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_scalar_strict_bytes:=map Byte.repr[115;116;114;105;99;116].

Theorem actual_gateway_scalar_strict_literal:gateway_static_cstring ___stringlit_8 v___stringlit_8 gateway_scalar_strict_bytes.
Proof.
  eapply gateway_static_string_from_registration.
  - vm_compute;reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute;intuition discriminate.
  - change(7<=18446744073709551616);lia.
Qed.

Lemma gateway_scalar_strict_mode_of_loaded memory symbol :
  gateway_error_cstring memory(Vptr symbol Ptrofs.zero)gateway_scalar_strict_bytes ->
  gateway_unicode_strict_mode memory(Vptr symbol Ptrofs.zero).
Proof.
  intros[object[offset[POINTER[NONZERO[BOUND LOAD]]]]];inversion POINTER;subst object offset.
  right;exists symbol,Ptrofs.zero;split;[reflexivity|]. split.
  - pose proof(Mem.loadbytes_range_perm _ _ _ _ _ LOAD)as PERMISSIONS.
    eapply Mem.perm_valid_block;apply(PERMISSIONS 0);change(0<=0<7);lia.
  - split.
    + change(0+Z.of_nat(length(gateway_scalar_strict_bytes++[Byte.zero]))<=Ptrofs.modulus).
      rewrite length_app;cbn;exact BOUND.
    + change(Mem.loadbytes memory symbol 0 7=Some(inj_bytes(gateway_scalar_strict_bytes++[Byte.zero])));exact LOAD.
Qed.

Theorem actual_gateway_scalar_strict_mode initial :Genv.init_mem prog=Some initial ->
  exists symbol,Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some symbol /\
    gateway_unicode_strict_mode initial(Vptr symbol Ptrofs.zero).
Proof.
  intro INITIAL;destruct(gateway_static_cstring_loaded ___stringlit_8 v___stringlit_8 gateway_scalar_strict_bytes initial
    actual_gateway_scalar_strict_literal INITIAL)as(symbol &SYMBOL &LOADED).
  exists symbol;split;[exact SYMBOL|eapply gateway_scalar_strict_mode_of_loaded;exact LOADED].
Qed.
