(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Native operation data comes from the same actual C arguments and bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayNativeImport GatewayNativeWords GatewaySpawnABI GatewayRuntimeABI.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Local Opaque Nat_of_nat Z.to_nat Nat.pow.
Module ND := GatewayNativeImport.

Definition gateway_native_empty_bytes : ND.List_inst1 Lean.Nat := ND.List_nil_inst1 _.
Definition gateway_native_close_code (descriptor : int) :=
  ND.LeanCage_Host_NativeCode_Operation_vfs
    (ND.LeanCage_Host_NativeCode_VfsOperation_adapted
      (ND.LeanCage_Host_NativeCode_Request_mk (Nat_of_nat 3) (gateway_native_int descriptor)
        (Nat_of_nat 0) (Nat_of_nat 0) gateway_native_empty_bytes gateway_native_empty_bytes)).
Definition gateway_native_send_code descriptor bytes extent flags :=
  ND.LeanCage_Host_NativeCode_Operation_send (gateway_native_int descriptor)
    (gateway_native_bytes bytes) (gateway_native_word extent) (gateway_native_int flags).
Definition gateway_native_receive_code descriptor extent flags :=
  ND.LeanCage_Host_NativeCode_Operation_receive (gateway_native_int descriptor)
    (gateway_native_word extent) (gateway_native_int flags).

(* This is an operand relation only. Actual output/errno/product observations,
   ownership, source occurrence and physical process identity are separate. *)
Inductive gateway_native_call_operands (memory : mem) :
    Ctypes.fundef Clight.function -> list Values.val -> ND.LeanCage_Host_NativeCode_Operation -> Prop :=
| gateway_native_socketpair_operands : forall domain socket_type protocol output,
    gateway_native_call_operands memory (gateway_spawn_signature gateway_socketpair_api)
      [Vint domain; Vint socket_type; Vint protocol; output]
      (ND.LeanCage_Host_NativeCode_Operation_socketPair (gateway_native_int domain)
        (gateway_native_int socket_type) (gateway_native_int protocol))
| gateway_native_fcntl_operands : forall descriptor command argument,
    gateway_native_call_operands memory (gateway_spawn_signature gateway_fcntl_api)
      [Vint descriptor; Vint command; Vint argument]
      (ND.LeanCage_Host_NativeCode_Operation_fcntl (gateway_native_int descriptor)
        (gateway_native_int command) (gateway_native_int argument))
| gateway_native_close_operands : forall descriptor,
    gateway_native_call_operands memory (gateway_spawn_signature gateway_close_api) [Vint descriptor]
      (gateway_native_close_code descriptor)
| gateway_native_send_operands : forall descriptor object offset extent flags bytes,
    Mem.loadbytes memory object (Ptrofs.unsigned offset) (Int64.unsigned extent) = Some (inj_bytes bytes) ->
    gateway_native_call_operands memory gateway_send_definition
      [Vint descriptor; Vptr object offset; Vlong extent; Vint flags]
      (gateway_native_send_code descriptor bytes extent flags)
| gateway_native_receive_operands : forall descriptor output extent flags,
    gateway_native_call_operands memory gateway_receive_definition
      [Vint descriptor; output; Vlong extent; Vint flags]
      (gateway_native_receive_code descriptor extent flags).

Theorem gateway_native_loaded_send_extent memory object offset extent bytes :
  Mem.loadbytes memory object (Ptrofs.unsigned offset) (Int64.unsigned extent) = Some (inj_bytes bytes) ->
  Z.of_nat (length bytes) = Int64.unsigned extent.
Proof.
  intro LOAD; pose proof (Mem.loadbytes_length _ _ _ _ _ LOAD) as LENGTH.
  unfold inj_bytes in LENGTH; rewrite length_map in LENGTH.
  rewrite LENGTH, Z2Nat.id; [reflexivity |exact (proj1 (Int64.unsigned_range extent))].
Qed.

Theorem gateway_native_inj_bytes_unique first second : inj_bytes first = inj_bytes second -> first = second.
Proof.
  revert second; induction first as [|byte rest IH]; intros [|other tail] SAME;
    cbn [inj_bytes] in SAME; try discriminate; [reflexivity |].
  injection SAME as HEAD TAIL; f_equal; [congruence |apply IH; exact TAIL].
Qed.

Theorem gateway_native_call_operands_unique memory definition arguments first second :
  gateway_native_call_operands memory definition arguments first ->
  gateway_native_call_operands memory definition arguments second -> first = second.
Proof.
  intros FIRST SECOND; inversion FIRST; subst; inversion SECOND; subst;
    try reflexivity; try discriminate.
  match goal with
  | ONE : Mem.loadbytes _ _ _ _ = Some (inj_bytes ?one),
    TWO : Mem.loadbytes _ _ _ _ = Some (inj_bytes ?another) |- _ =>
    assert (SAME : one = another) by (apply gateway_native_inj_bytes_unique; congruence);
    subst; reflexivity
  end.
Qed.
