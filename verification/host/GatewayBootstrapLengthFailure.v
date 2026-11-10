(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Both actual oversize path branches return failure before reading a byte. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewayMachine GatewayReturns GatewayBootstrapValidationSource.
From HostGateway Require Import GatewaySource.
Open Scope Z_scope.

Section Oversize.
Variables low prefix suffix compared character : ident.
Variables (byte_setup prepare_compare : statement -> statement) (path : expr).
Let validation := bootstrap_validation low prefix suffix compared character byte_setup prepare_compare path.
Let first := match validation with Ssequence first _ => first | _ => Sskip end.
Let guard := match validation with Ssequence _ rest => rest | _ => Sskip end.
Let initial := match first with Ssequence first _ => first | _ => Sskip end.
Let compare := match first with Ssequence _ rest => rest | _ => Sskip end.
Let size_test := match initial with Ssequence first _ => first | _ => Sskip end.
Let prefix_test := match initial with Ssequence _ rest => rest | _ => Sskip end.

Theorem gateway_bootstrap_oversize_script ge function environment temporaries memory continuation size :
  fn_return function = tint -> call_cont continuation = Kstop ->
  temporaries ! GatewaySource._size = Some (Vlong size) ->
  Int64.cmpu Cgt size (Int64.repr 4095) = true ->
  gateway_constant_path ge (Vint (Int.neg Int.one))
    (State function validation continuation environment temporaries memory).
Proof.
  intros TYPE STOP SIZE LARGE.
  set (after_low := PTree.set low (Vint Int.one) temporaries).
  set (after_prefix := PTree.set prefix (Vint Int.one) after_low).
  set (after_suffix := PTree.set suffix (Vint Int.one) after_prefix).
  eapply gateway_constant_next with (next := State function first (Kseq guard continuation)
    environment temporaries memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_constant_next with (next := State function initial (Kseq compare (Kseq guard continuation))
    environment temporaries memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_constant_next with (next := State function size_test
    (Kseq prefix_test (Kseq compare (Kseq guard continuation))) environment temporaries memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_constant_next with (next := State function (Sset low (Econst_int Int.one tint))
    (Kseq prefix_test (Kseq compare (Kseq guard continuation))) environment temporaries memory).
  - cbn; tauto.
  - intro another; apply certified_if_edge with (v := Vint Int.one) (b := true).
    + pose proof (gateway_bootstrap_size_expression ge environment temporaries another size SIZE) as VALUE.
      rewrite LARGE in VALUE; exact VALUE.
    + reflexivity.
  - eapply gateway_constant_next with (next := State function Sskip
      (Kseq prefix_test (Kseq compare (Kseq guard continuation))) environment after_low memory);
      [cbn; tauto |intros; apply certified_set_edge, old_expression_value; constructor |].
    eapply gateway_constant_next with (next := State function prefix_test
      (Kseq compare (Kseq guard continuation)) environment after_low memory);
      [cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_constant_next with (next := State function (Sset prefix (Econst_int Int.one tint))
      (Kseq compare (Kseq guard continuation)) environment after_low memory).
    + cbn; tauto.
    + intros; apply certified_if_edge with (v := Vint Int.one) (b := true);
        [apply old_expression_value, value_temp, PTree.gss |reflexivity].
    + eapply gateway_constant_next with (next := State function Sskip
        (Kseq compare (Kseq guard continuation)) environment after_prefix memory);
        [cbn; tauto |intros; apply certified_set_edge, old_expression_value; constructor |].
      eapply gateway_constant_next with (next := State function compare (Kseq guard continuation)
        environment after_prefix memory);
        [cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
      eapply gateway_constant_next with (next := State function (Sset suffix (Econst_int Int.one tint))
        (Kseq guard continuation) environment after_prefix memory).
      * cbn; tauto.
      * intros; apply certified_if_edge with (v := Vint Int.one) (b := true);
          [apply old_expression_value, value_temp, PTree.gss |reflexivity].
      * eapply gateway_constant_next with (next := State function Sskip (Kseq guard continuation)
          environment after_suffix memory);
          [cbn; tauto |intros; apply certified_set_edge, old_expression_value; constructor |].
        eapply gateway_constant_next with (next := State function guard continuation environment after_suffix memory);
          [cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
        eapply gateway_constant_next with (next := State function bootstrap_path_reject continuation
          environment after_suffix memory).
        -- cbn; tauto.
        -- intros; apply certified_if_edge with (v := Vint Int.one) (b := true);
             [apply old_expression_value, value_temp, PTree.gss |reflexivity].
        -- eapply gateway_constant_at_return with (value := Vint (Int.neg Int.one)).
           ++ exact STOP.
           ++ intros; apply old_expression_value; eapply value_unary; [constructor |reflexivity].
           ++ intros; rewrite TYPE; reflexivity.
Qed.
End Oversize.

Theorem gateway_actual_bootstrap_oversize {World Event} (backend : gateway_backend World Event)
    ge (canonical : bool) environment temporaries memory continuation size world events returned after next :
  temporaries ! _size = Some (Vlong size) -> Int64.cmpu Cgt size (Int64.repr 4095) = true ->
  call_cont continuation = Kstop ->
  gateway_steps backend ge
    (gateway_live (State f_host_bootstrap
      (if canonical then bootstrap_canonical_validation else bootstrap_loaded_validation)
      continuation environment temporaries memory) world) events
    (gateway_live (Returnstate returned Kstop after) next) -> returned = Vint (Int.neg Int.one).
Proof.
  intros SIZE LARGE STOP RUN.
  eapply gateway_constant_path_actual; [|exact RUN].
  destruct canonical; [rewrite (proj2 actual_bootstrap_validation_fragments) |
    rewrite (proj1 actual_bootstrap_validation_fragments)].
  all: (eapply gateway_bootstrap_oversize_script;
    [reflexivity |exact STOP |exact SIZE |exact LARGE]).
Qed.
