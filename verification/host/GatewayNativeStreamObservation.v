(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: One native stream sample and its kernel row carry the same bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayStreamInterface
  GatewayThreadRuntime GatewayNativeImport GatewayNativeWords GatewayNativeRows GatewayNativeCallOperands.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Definition gateway_native_row_product (row : ND.LeanCage_Host_NativeCode_CallRow) :=
  match row with ND.LeanCage_Host_NativeCode_CallRow_mk _ _ _ _ _ _ product => product end.

Definition gateway_native_stream_product row constructor bytes : Prop :=
  gateway_native_row_product row = constructor (gateway_native_bytes bytes) \/
    (bytes = [] /\ gateway_native_row_product row = ND.LeanCage_Host_NativeCode_Product_none).

Theorem gateway_native_nonempty_stream_product row constructor bytes :
  gateway_native_stream_product row constructor bytes -> bytes <> [] ->
  gateway_native_row_product row = constructor (gateway_native_bytes bytes).
Proof. intros [COMMITTED |[EMPTY NONE]] NONEMPTY; [exact COMMITTED |contradiction]. Qed.

(* This is the representation of ONE actual send/recv effect, including a
   committed effect whose caller is lost. It supplies neither source control,
   descriptor ownership, a response, a queue, nor a later acknowledgement. *)
Record gateway_native_stream_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (rows : World -> Event -> option (nat * ND.LeanCage_Host_NativeCode_CallRow)) : Prop := {
  gateway_native_receive_product : forall descriptor output extent flags before world result after next event
      selected row requested returned bytes,
    gateway_runtime_operation backend gateway_receive_definition
      [Vint descriptor; output; Vlong extent; Vint flags] before world result after next event ->
    rows world event = Some (selected, row) ->
    io event = Some (gateway_native_receive descriptor requested returned bytes) ->
    gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_received bytes;
  gateway_native_send_product : forall descriptor input extent flags before world result after next event
      selected row requested returned bytes,
    gateway_runtime_operation backend gateway_send_definition
      [Vint descriptor; input; Vlong extent; Vint flags] before world result after next event ->
    rows world event = Some (selected, row) ->
    io event = Some (gateway_native_send descriptor requested returned bytes) ->
    gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_sent bytes
}.

Theorem gateway_actual_receive_native_row {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno process position builders genuine actions attributes rows
    (thread : gateway_thread_runtime backend io native stable discipline thread_errno)
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_native_stream_runtime backend io rows)
    saved before world descriptor object offset amount result after next event :
  discipline (Some saved) before world -> native world object ->
  0 < amount <= 65536 -> gateway_native_pointer before object offset amount Writable ->
  gateway_runtime_operation backend gateway_receive_definition
    [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint Int.zero]
    before world result after next event ->
  exists selected row count bytes,
    rows world event = Some (selected, row) /\
    gateway_native_row_process row = Nat_of_nat (process world) /\
    gateway_native_row_operation row = gateway_native_receive_code descriptor (Int64.repr amount) Int.zero /\
    (position world <= selected < position next)%nat /\
    gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_received bytes /\
    result = Vlong (Int64.repr count) /\ -1 <= count <= amount /\
    Z.of_nat (length bytes) = Z.max 0 count /\
    Mem.loadbytes after object (Ptrofs.unsigned offset) (Z.max 0 count) = Some (inj_bytes bytes) /\
    io event = Some (gateway_native_receive descriptor amount count bytes) /\
    discipline (Some saved) after next /\ gateway_access_retained native stable before world next /\
    gateway_native_permissions before after object offset amount /\
    gateway_native_frame native stable (gateway_native_region object offset (Z.max 0 count)) world before after.
Proof.
  intros SIDE PRIVATE AMOUNT POINTER OPERATION.
  assert (INPUTS : gateway_native_operation_inputs builders genuine actions attributes before world
    gateway_receive_definition
    [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint Int.zero]
    (gateway_native_receive_code descriptor (Int64.repr amount) Int.zero)).
  { apply gateway_native_direct_inputs; apply gateway_native_receive_operands. }
  destruct (gateway_native_operation_row _ _ _ _ _ _ _ _ recording _ _ _ _ _ _ _ _ _
    INPUTS OPERATION) as (selected & row & ROW & PROCESS & CODE & ORDER).
  destruct (gateway_receive_operation _ _ _ _ _ _ thread saved before world descriptor object offset
    amount result after next event SIDE PRIVATE AMOUNT POINTER OPERATION)
    as (count & bytes & RANGE & RESULT & COUNT & BYTES & IO & AFTER & ACCESS & PERMISSIONS & FRAME).
  exists selected, row, count, bytes.
  assert (PRODUCT : gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_received bytes).
  { eapply gateway_native_receive_product; eassumption. }
  repeat first [assumption | split].
Qed.

Theorem gateway_actual_send_native_row {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno process position builders genuine actions attributes rows
    (thread : gateway_thread_runtime backend io native stable discipline thread_errno)
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_native_stream_runtime backend io rows)
    mode before world descriptor object offset amount result after next event payload :
  discipline mode before world ->
  (native world object \/ forall query,
    Ptrofs.unsigned offset <= query < Ptrofs.unsigned offset + amount -> stable world object query) ->
  0 < amount <= 65536 -> gateway_native_pointer before object offset amount Readable ->
  Mem.loadbytes before object (Ptrofs.unsigned offset) amount = Some (inj_bytes payload) ->
  gateway_runtime_operation backend gateway_send_definition
    [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint (Int.repr 16384)]
    before world result after next event ->
  exists selected row count bytes,
    rows world event = Some (selected, row) /\
    gateway_native_row_process row = Nat_of_nat (process world) /\
    gateway_native_row_operation row =
      gateway_native_send_code descriptor payload (Int64.repr amount) (Int.repr 16384) /\
    (position world <= selected < position next)%nat /\
    gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_sent bytes /\
    result = Vlong (Int64.repr count) /\ -1 <= count <= amount /\
    Z.of_nat (length bytes) = Z.max 0 count /\
    Mem.loadbytes before object (Ptrofs.unsigned offset) (Z.max 0 count) = Some (inj_bytes bytes) /\
    io event = Some (gateway_native_send descriptor amount count bytes) /\
    discipline mode after next /\ gateway_access_retained native stable before world next /\
    gateway_native_frame native stable gateway_native_no_output world before after.
Proof.
  intros SIDE PRIVATE AMOUNT POINTER PAYLOAD OPERATION.
  assert (ENCODING : Int64.unsigned (Int64.repr amount) = amount).
  { apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615; lia. }
  assert (INPUTS : gateway_native_operation_inputs builders genuine actions attributes before world
    gateway_send_definition
    [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint (Int.repr 16384)]
    (gateway_native_send_code descriptor payload (Int64.repr amount) (Int.repr 16384))).
  { apply gateway_native_direct_inputs; apply gateway_native_send_operands; rewrite ENCODING; exact PAYLOAD. }
  destruct (gateway_native_operation_row _ _ _ _ _ _ _ _ recording _ _ _ _ _ _ _ _ _
    INPUTS OPERATION) as (selected & row & ROW & PROCESS & CODE & ORDER).
  destruct (gateway_send_operation _ _ _ _ _ _ thread mode before world descriptor object offset
    amount result after next event SIDE PRIVATE AMOUNT POINTER OPERATION)
    as (count & bytes & RANGE & RESULT & COUNT & BYTES & IO & AFTER & ACCESS & FRAME).
  exists selected, row, count, bytes.
  assert (PRODUCT : gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_sent bytes).
  { eapply gateway_native_send_product; eassumption. }
  repeat first [assumption | split].
Qed.
