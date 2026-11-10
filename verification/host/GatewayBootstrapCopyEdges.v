(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real copy calls use actual source expressions and fixed SDK arguments. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayBootstrapABI GatewayBootstrapCopySource.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_array_reference ge environment temporaries memory identifier count object :
  environment ! identifier = Some (object, tarray tschar count) ->
  expression_value ge environment temporaries memory (Evar identifier (tarray tschar count))
    (Vptr object Ptrofs.zero).
Proof.
  intro LOCATION; eapply location_read_value; [apply local_location_value; exact LOCATION |].
  apply deref_loc_reference; reflexivity.
Qed.

Theorem gateway_bootstrap_global_array_reference (ge : Clight.genv) environment temporaries memory
    identifier count object :
  environment ! identifier = None -> Genv.find_symbol ge identifier = Some object ->
  expression_value ge environment temporaries memory (Evar identifier (tarray tschar count))
    (Vptr object Ptrofs.zero).
Proof.
  intros LOCAL SYMBOL; apply old_expression_value; eapply value_function;
    [exact LOCAL |exact SYMBOL |reflexivity].
Qed.

Theorem gateway_bootstrap_copy_call_edge (ge : Clight.genv) environment temporaries memory continuation
    target source amount target_value source_value count symbol :
  environment ! _memcpy = None -> Genv.find_symbol ge _memcpy = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api) ->
  expression_value ge environment temporaries memory target target_value ->
  expression_value ge environment temporaries memory source source_value ->
  expression_value ge environment temporaries memory amount (Vlong count) ->
  sem_cast target_value (typeof target) (tptr tvoid) memory = Some target_value ->
  sem_cast source_value (typeof source) (tptr tvoid) memory = Some source_value ->
  sem_cast (Vlong count) (typeof amount) tulong memory = Some (Vlong count) ->
  store_edge ge (State f_host_bootstrap (bootstrap_copy target source amount) continuation
      environment temporaries memory)
    (Callstate (gateway_bootstrap_signature gateway_memory_copy_api)
      [target_value; source_value; Vlong count]
      (Kcall None f_host_bootstrap environment temporaries continuation) memory).
Proof.
  intros LOCAL SYMBOL FUNCTION TARGET SOURCE AMOUNT TARGET_CAST SOURCE_CAST AMOUNT_CAST.
  eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [exact LOCAL |exact SYMBOL |reflexivity].
  - eapply cons_argument_values; [exact TARGET |exact TARGET_CAST |].
    eapply cons_argument_values; [exact SOURCE |exact SOURCE_CAST |].
    eapply cons_argument_values; [exact AMOUNT |exact AMOUNT_CAST |apply no_argument_values].
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.
