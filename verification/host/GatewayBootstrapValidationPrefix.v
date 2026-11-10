(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real length guards precede any filename-byte access. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewayFramedRuntime
  GatewayBootstrapValidationSource.
Import ListNotations.
Open Scope Z_scope.

Section ValidationPrefix.
Context {World Event} (backend : gateway_backend World Event).
Variable ge : Clight.genv.
Variables low prefix suffix compared character : ident.
Variables (byte_setup prepare_compare : statement -> statement) (path : expr).
Let validation := bootstrap_validation low prefix suffix compared character byte_setup prepare_compare path.
Let first := match validation with Ssequence first _ => first | _ => Sskip end.
Let guard := match validation with Ssequence _ rest => rest | _ => Sskip end.
Let initial := match first with Ssequence first _ => first | _ => Sskip end.
Let compare := match first with Ssequence _ rest => rest | _ => Sskip end.
Let size_test := match initial with Ssequence first _ => first | _ => Sskip end.
Let prefix_test := match initial with Ssequence _ rest => rest | _ => Sskip end.
Let byte_test := Sset prefix (Ecast (Ebinop One (Etempvar character tschar)
  (Econst_int (Int.repr 47) tint) tint) tbool).

Theorem gateway_bootstrap_validation_lengths definition arguments target property
    function environment temporaries memory continuation size result :
  gateway_ambient_closed backend property ->
  temporaries ! GatewaySource._size = Some (Vlong size) ->
  temporaries ! GatewaySource._tail = Some (Vlong (Int64.repr 30)) ->
  Int64.cmpu Cgt size (Int64.repr 4095) = false ->
  Int64.cmpu Cle size (Int64.repr 30) = false ->
  gateway_source_path backend ge definition arguments target property
    (State function (byte_setup byte_test) (Kseq compare (Kseq guard continuation)) environment
      (PTree.set low (Vint Int.zero) temporaries) memory) result ->
  gateway_source_path backend ge definition arguments target property
    (State function validation continuation environment temporaries memory) result.
Proof.
  intros CLOSED SIZE TAIL BOUNDED LONG REST.
  set (after_low := PTree.set low (Vint Int.zero) temporaries).
  eapply gateway_source_same with (target := State function first (Kseq guard continuation)
    environment temporaries memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_source_same with (target := State function initial (Kseq compare (Kseq guard continuation))
    environment temporaries memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_source_same with (target := State function size_test
    (Kseq prefix_test (Kseq compare (Kseq guard continuation))) environment temporaries memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_source_same with (target := State function (Sset low (Ecast bootstrap_tail_test tbool))
    (Kseq prefix_test (Kseq compare (Kseq guard continuation))) environment temporaries memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply certified_if_edge with (v := Vint Int.zero) (b := false).
    + pose proof (gateway_bootstrap_size_expression ge environment temporaries memory0 size SIZE) as VALUE.
      rewrite BOUNDED in VALUE; exact VALUE.
    + reflexivity.
  - eapply gateway_source_same with (target := State function Sskip
      (Kseq prefix_test (Kseq compare (Kseq guard continuation))) environment after_low memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply certified_set_edge; eapply cast_expression_value with (v := Vint Int.zero).
      * pose proof (gateway_bootstrap_tail_expression ge environment temporaries memory0 size SIZE TAIL) as VALUE.
        rewrite LONG in VALUE; exact VALUE.
      * reflexivity.
    + eapply gateway_source_same with (target := State function prefix_test
        (Kseq compare (Kseq guard continuation)) environment after_low memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
      eapply gateway_source_same with (target := State function (byte_setup byte_test)
        (Kseq compare (Kseq guard continuation)) environment after_low memory).
      * exact CLOSED.
      * cbn; tauto.
      * intros; apply certified_if_edge with (v := Vint Int.zero) (b := false);
          [apply old_expression_value, value_temp, PTree.gss |reflexivity].
      * exact REST.
Qed.

Theorem gateway_bootstrap_validation_character definition arguments target property
    function environment temporaries memory continuation result :
  gateway_ambient_closed backend property ->
  temporaries ! character = Some (Vint (Int.repr 47)) ->
  gateway_source_path backend ge definition arguments target property
    (State function (prepare_compare (bootstrap_suffix_call compared path))
      (Kseq (Sset suffix (Ecast (Etempvar compared tint) tbool)) (Kseq guard continuation))
      environment (PTree.set prefix (Vint Int.zero) temporaries) memory) result ->
  gateway_source_path backend ge definition arguments target property
    (State function byte_test (Kseq compare (Kseq guard continuation))
      environment temporaries memory) result.
Proof.
  intros CLOSED CHARACTER REST.
  set (after_prefix := PTree.set prefix (Vint Int.zero) temporaries).
  eapply gateway_source_same with (target := State function Sskip
    (Kseq compare (Kseq guard continuation)) environment after_prefix memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply certified_set_edge; eapply cast_expression_value with (v := Vint Int.zero).
    + apply old_expression_value; eapply value_binary;
        [apply value_temp; exact CHARACTER |constructor |reflexivity].
    + reflexivity.
  - eapply gateway_source_same with (target := State function compare (Kseq guard continuation)
      environment after_prefix memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_source_same with (target := State function
      (Ssequence (prepare_compare (bootstrap_suffix_call compared path))
        (Sset suffix (Ecast (Etempvar compared tint) tbool)))
      (Kseq guard continuation) environment after_prefix memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply certified_if_edge with (v := Vint Int.zero) (b := false);
        [apply old_expression_value, value_temp, PTree.gss |reflexivity].
    + eapply gateway_source_same with (target := State function
        (prepare_compare (bootstrap_suffix_call compared path))
        (Kseq (Sset suffix (Ecast (Etempvar compared tint) tbool)) (Kseq guard continuation))
        environment after_prefix memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |exact REST].
Qed.
End ValidationPrefix.
