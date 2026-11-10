(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Actual C fcntl operands precede their
   selected kernel row, including when the SDK has not yet returned. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import AST Values Memory Integers Globalenvs Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewayNativeImport
  GatewayNativeRows GatewayNativeWords GatewayFcntlExecution.
Import ListNotations.
Local Close Scope lean_scope.
Module ND := GatewayNativeImport.

(* A per-operation ABI observer binds the exact three C arguments and row.
   It provides no source profile, alias guarantee, SDK result or future ACK. *)
Record gateway_pending_fcntl_runtime {World}
    (pending : list Values.val -> mem -> World -> World -> nat -> ND.LeanCage_Host_NativeCode_CallRow -> Prop) : Prop := {
  gateway_pending_fcntl_operands : forall arguments memory world current selected row,
    pending arguments memory world current selected row ->
    exists descriptor command argument,
      arguments = [Vint descriptor; Vint command; Vint argument] /\
      gateway_native_row_operation row = ND.LeanCage_Host_NativeCode_Operation_fcntl
        (gateway_native_int descriptor) (gateway_native_int command) (gateway_native_int argument)
}.

Theorem gateway_actual_source_fcntl_row {World Event} (backend : gateway_backend World Event)
    pending (primitive : gateway_pending_fcntl_runtime pending)
    value function environment temporaries before initial events arguments continuation memory world
    current selected row :
  Genv.find_funct (Clight.globalenv prog) value = Some (Ctypes.Internal function) ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State function (fn_body function) Kstop environment temporaries before) initial) events
    (gateway_live (Callstate (gateway_spawn_signature gateway_fcntl_api) arguments continuation memory) world) ->
  pending arguments memory world current selected row ->
  exists descriptor argument,
    gateway_native_row_operation row = ND.LeanCage_Host_NativeCode_Operation_fcntl
      (gateway_native_int descriptor) (Nat_of_nat 3) (gateway_native_int argument) \/
    gateway_native_row_operation row = ND.LeanCage_Host_NativeCode_Operation_fcntl
      (gateway_native_int descriptor) (Nat_of_nat 4) (gateway_native_int argument) \/
    gateway_native_row_operation row = ND.LeanCage_Host_NativeCode_Operation_fcntl
      (gateway_native_int descriptor) (Nat_of_nat 1030) (gateway_native_int argument).
Proof.
  intros DEFINITION SOURCE OBSERVED.
  destruct (@gateway_pending_fcntl_operands World pending primitive arguments memory world current selected row OBSERVED)
    as (descriptor & command & argument & ARGUMENTS & ROW).
  destruct (gateway_actual_function_fcntl_prefix backend value function environment temporaries before initial
    events arguments continuation memory world DEFINITION SOURCE) as (first & actual & last & VALUES & COMMAND).
  rewrite ARGUMENTS in VALUES; inversion VALUES; subst actual.
  exists descriptor, argument.
  destruct COMMAND as [ONE | [TWO | THREE]]; subst command.
  - left; rewrite ROW, gateway_native_repr_int; [reflexivity |change (0 <= 3 <= 2147483647)%Z; lia].
  - right; left; rewrite ROW, gateway_native_repr_int; [reflexivity |change (0 <= 4 <= 2147483647)%Z; lia].
  - right; right; rewrite ROW, gateway_native_repr_int; [reflexivity |change (0 <= 1030 <= 2147483647)%Z; lia].
Qed.
