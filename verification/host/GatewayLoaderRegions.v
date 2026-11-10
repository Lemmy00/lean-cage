(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Native initializer regions coexist with the actual linked CPython heap. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayGlobals GatewayRegistry GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

(* A per-segment ELF/ABI observation at native module load. It gives only the
   identified source initializer, readable extent and actual relocated loads.
   Application writes and later retention require their own source proof. *)
Record gateway_loaded_native_region (ge : Clight.genv) (memory : mem)
    (variable : globvar type) (object : block) : Prop := {
  gateway_loaded_region_bound : 0 < init_data_list_size (gvar_init variable) <= Ptrofs.modulus;
  gateway_loaded_region_readable : Mem.range_perm memory object 0
    (init_data_list_size (gvar_init variable)) Cur Readable;
  gateway_loaded_region_bytes : Mem.loadbytes memory object 0 (init_data_list_size (gvar_init variable)) =
    Some (Genv.bytes_of_init_data_list (Clight.genv_genv ge) (gvar_init variable));
  gateway_loaded_region_values : Genv.load_store_init_data (Clight.genv_genv ge) memory object 0 (gvar_init variable)
}.

Definition gateway_native_initializer_view (ge : Clight.genv) identifier variable object memory : Prop :=
  gateway_program_definition identifier global_definitions = Some (Gvar variable) /\
  gvar_volatile variable = false /\ Genv.find_symbol ge identifier = Some object /\
  gateway_loaded_native_region ge memory variable object.

(* Linked SDK declarations with empty initializers are intentionally excluded.
   Their genuine objects/headers are supplied by individual CPython contracts. *)
Record gateway_native_loader_boundary (ge : Clight.genv) (memory : mem) : Prop := {
  gateway_native_initialized : forall identifier variable,
    gateway_program_definition identifier global_definitions = Some (Gvar variable) ->
    gvar_volatile variable = false -> 0 < init_data_list_size (gvar_init variable) ->
    exists object, gateway_native_initializer_view ge identifier variable object memory
}.

Theorem gateway_loaded_region_cstring identifier variable object memory bytes :
  gateway_static_cstring identifier variable bytes ->
  gateway_native_initializer_view (Clight.globalenv prog) identifier variable object memory ->
  gateway_error_cstring memory (Vptr object Ptrofs.zero) bytes.
Proof.
  intros [_ [_ [NONZERO [BOUND [SIZE CONTENTS]]]]] [_ [_ [_ REGION]]].
  destruct REGION as [WIDTH READABLE LOAD VALUES].
  exists object, Ptrofs.zero; split; [reflexivity |]. split; [exact NONZERO |]. split.
  - change (0 + Z.of_nat (length bytes) + 1 <= Ptrofs.modulus); exact BOUND.
  - change (Mem.loadbytes memory object 0 (Z.of_nat (length bytes) + 1) = Some (inj_bytes (bytes ++ [Byte.zero]))).
    rewrite SIZE, CONTENTS in LOAD; exact LOAD.
Qed.
