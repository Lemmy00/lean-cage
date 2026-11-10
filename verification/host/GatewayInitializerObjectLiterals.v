(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Initializer names are actual retained source bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayGlobals GatewayModuleRegions
  GatewayLoaderRegions GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition initializer_object_names : list (ident * list Byte.int) :=
  [(___stringlit_127, map Byte.repr [112; 97; 116; 104; 108; 105; 98]);
   (___stringlit_128, map Byte.repr [80; 97; 116; 104]);
   (___stringlit_129, map Byte.repr [87; 111; 114; 107; 115; 112; 97; 99; 101]);
   (___stringlit_130, map Byte.repr [67; 97; 110; 99; 101; 108; 108; 97; 116; 105; 111; 110]);
   (___stringlit_131, map Byte.repr [79; 117; 116; 99; 111; 109; 101])].

Theorem gateway_actual_initializer_object_literal identifier bytes :
  In (identifier, bytes) initializer_object_names ->
  exists variable,
    gateway_program_definition identifier global_definitions = Some (Gvar variable) /\
    gvar_readonly variable = true /\ gateway_static_cstring identifier variable bytes.
Proof.
  cbn [initializer_object_names In]; intro MEMBER;
    repeat destruct MEMBER as [MEMBER |MEMBER]; try contradiction;
    inversion MEMBER; subst.
  all: eexists; split; [reflexivity |split; [reflexivity |]].
  all: eapply gateway_static_string_from_registration;
    [vm_compute; reflexivity |reflexivity |reflexivity |vm_compute; intuition discriminate |
     change Ptrofs.modulus with 18446744073709551616; cbn; lia].
Qed.

Theorem gateway_initializer_object_name_bytes memory identifier bytes symbol :
  gateway_module_descriptor_regions (Clight.globalenv prog) memory ->
  In (identifier, bytes) initializer_object_names ->
  Genv.find_symbol (Clight.globalenv prog) identifier = Some symbol ->
  gateway_error_cstring memory (Vptr symbol Ptrofs.zero) bytes.
Proof.
  intros REGIONS MEMBER SYMBOL.
  destruct (gateway_actual_initializer_object_literal identifier bytes MEMBER)
    as (variable & DEFINITION & READONLY & STATIC).
  assert (POSITIVE : 0 < init_data_list_size (gvar_init variable)).
  { destruct STATIC as (_ & _ & _ & _ & SIZE & _); rewrite SIZE; lia. }
  assert (NONVOLATILE : gvar_volatile variable = false) by (exact (proj1 (proj2 STATIC))).
  destruct (REGIONS identifier variable DEFINITION NONVOLATILE POSITIVE (or_introl READONLY)) as (object & VIEW).
  assert (SAME : object = symbol) by (destruct VIEW as (_ & _ & ACTUAL & _); congruence).
  subst symbol; eapply gateway_loaded_region_cstring; eassumption.
Qed.
