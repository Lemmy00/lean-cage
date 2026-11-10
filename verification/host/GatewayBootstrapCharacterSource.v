(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Absolute-path guards load the actual source filename byte. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess Readers.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewayFramedRuntime
  GatewayBootstrapSource GatewayBootstrapValidationSource GatewayBootstrapFilename GatewayBootstrapByte GatewayBootstrapInformation
  GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_character_expression ge environment temporaries memory path object offset bytes :
  typeof path = tptr tschar \/ typeof path = tarray tschar 4096 ->
  expression_value ge environment temporaries memory path (Vptr object offset) ->
  gateway_error_cstring memory (Vptr object offset) bytes ->
  expression_value ge environment temporaries memory
    (Ederef (Ebinop Oadd path (Econst_int Int.zero tint) (tptr tschar)) tschar)
    (Vint (Int.sign_ext 8 (Readers.byte_word (hd Byte.zero bytes)))).
Proof.
  intros TYPE PATH STRING; eapply location_read_value.
  - apply pointer_location_value; eapply binary_expression_value;
      [exact PATH |apply old_expression_value; constructor |].
    destruct TYPE as [TYPE |TYPE]; rewrite TYPE; cbn; rewrite Ptrofs.add_zero; reflexivity.
  - eapply deref_loc_value; [reflexivity |].
    exact (gateway_bootstrap_first_character memory object offset bytes STRING).
Qed.

Section LoadedCharacter.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
  (runtime : gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge : Clight.genv.
Hypothesis LAYOUT : gateway_bootstrap_information_layout ge.
Variables (information resolved object : block) (offset : ptrofs) (bytes : list Byte.int).
Let filename := Vptr object offset.
Let character := Vint (Int.sign_ext 8 (Readers.byte_word (hd Byte.zero bytes))).
Variable property : mem -> World -> Prop.
Hypothesis CLOSED : gateway_ambient_closed backend property.
Hypothesis INFORMATION : forall memory world, property memory world ->
  gateway_bootstrap_filename_information native stable discipline information filename bytes memory world.

Theorem actual_bootstrap_loaded_character definition arguments target temporaries memory continuation following result :
  gateway_source_path backend ge definition arguments target property
    (State f_host_bootstrap following continuation (bootstrap_environment information resolved)
      (PTree.set _t'19 character (PTree.set _t'18 filename temporaries)) memory) result ->
  gateway_source_path backend ge definition arguments target property
    (State f_host_bootstrap (bootstrap_loaded_byte_setup following) continuation
      (bootstrap_environment information resolved) temporaries memory) result.
Proof.
  intro REST.
  eapply gateway_source_same with (target := State f_host_bootstrap (Sset _t'18 bootstrap_filename_expression)
    (Kseq (Ssequence (Sset _t'19 (Ederef (Ebinop Oadd (Etempvar _t'18 (tptr tschar))
      (Econst_int Int.zero tint) (tptr tschar)) tschar)) following) continuation)
    (bootstrap_environment information resolved) temporaries memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq (Ssequence (Sset _t'19 (Ederef (Ebinop Oadd (Etempvar _t'18 (tptr tschar))
      (Econst_int Int.zero tint) (tptr tschar)) tschar)) following) continuation)
    (bootstrap_environment information resolved) (PTree.set _t'18 filename temporaries) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [[_ [_ LOAD]] _]; apply certified_set_edge, gateway_bootstrap_filename_value;
      [exact LAYOUT |exact LOAD].
  - eapply gateway_source_same with (target := State f_host_bootstrap
      (Ssequence (Sset _t'19 (Ederef (Ebinop Oadd (Etempvar _t'18 (tptr tschar))
        (Econst_int Int.zero tint) (tptr tschar)) tschar)) following) continuation
      (bootstrap_environment information resolved) (PTree.set _t'18 filename temporaries) memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_source_same with (target := State f_host_bootstrap
      (Sset _t'19 (Ederef (Ebinop Oadd (Etempvar _t'18 (tptr tschar))
        (Econst_int Int.zero tint) (tptr tschar)) tschar)) (Kseq following continuation)
      (bootstrap_environment information resolved) (PTree.set _t'18 filename temporaries) memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
    eapply gateway_source_same with (target := State f_host_bootstrap Sskip (Kseq following continuation)
      (bootstrap_environment information resolved)
      (PTree.set _t'19 character (PTree.set _t'18 filename temporaries)) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [_ [STRING PROTECTED]]; apply certified_set_edge.
      eapply gateway_bootstrap_character_expression;
        [left; reflexivity |apply old_expression_value, value_temp, PTree.gss |exact STRING].
    + eapply gateway_source_same with (target := State f_host_bootstrap following continuation
        (bootstrap_environment information resolved)
        (PTree.set _t'19 character (PTree.set _t'18 filename temporaries)) memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |exact REST].
Qed.
End LoadedCharacter.
