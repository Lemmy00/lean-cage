(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Cleanup operands name the same full physical native row. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime
  GatewayExchangeABI GatewayReapABI GatewayNativeImport GatewayNativeWords GatewayNativeRows.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Local Opaque Nat_of_nat.
Module ND := GatewayNativeImport.

Definition gateway_native_signal_code group:=ND.LeanCage_Host_NativeCode_Operation_signal
  (gateway_native_int group)(Nat_of_nat 9).
Definition gateway_native_wait_code child options:=ND.LeanCage_Host_NativeCode_Operation_waitPid
  (gateway_native_int child)(gateway_native_int options).
Definition gateway_native_shutdown_code descriptor:=ND.LeanCage_Host_NativeCode_Operation_shutdown
  (gateway_native_int descriptor)(Nat_of_nat 1).
Definition gateway_native_clock_code:=ND.LeanCage_Host_NativeCode_Operation_clock(Nat_of_nat 1).
Definition gateway_native_poll_code descriptor requested timeout:=ND.LeanCage_Host_NativeCode_Operation_poll
  (ND.List_cons_inst1 _
    (ND.LeanCage_Host_NativeCode_PollEntry_mk(gateway_native_int descriptor)(gateway_native_int requested))
    (ND.List_nil_inst1 _))(gateway_native_int timeout).

(* The output spans remain exact actual C locations. Their contents are not
   read before initialization; status/sample values and physical committed
   products are separate observations, supplied at their actual primitive. *)
Inductive gateway_native_reap_operands(memory:mem):
    Ctypes.fundef Clight.function->list Values.val->ND.LeanCage_Host_NativeCode_Operation->Prop:=
|gateway_native_signal_operands:forall group,
    gateway_native_reap_operands memory gateway_kill_definition[Vint group;Vint(Int.repr 9)](gateway_native_signal_code group)
|gateway_native_wait_operands:forall child options object offset,
    gateway_native_pointer memory object offset 4 Writable->
    gateway_native_reap_operands memory gateway_waitpid_definition[Vint child;Vptr object offset;Vint options]
      (gateway_native_wait_code child options)
|gateway_native_shutdown_operands:forall descriptor,
    gateway_native_reap_operands memory gateway_shutdown_definition[Vint descriptor;Vint Int.one](gateway_native_shutdown_code descriptor)
|gateway_native_clock_operands:forall object offset,
    gateway_native_pointer memory object offset 16 Writable->
    gateway_native_reap_operands memory gateway_clock_gettime_definition[Vint Int.one;Vptr object offset]gateway_native_clock_code
|gateway_native_poll_operands:forall object offset descriptor requested timeout,
    gateway_native_pointer memory object offset 8 Writable->
    Mem.loadv Mint32 memory(Vptr object offset)=Some(Vint descriptor)->
    Mem.loadv Mint16signed memory(Vptr object(Ptrofs.add offset(Ptrofs.repr 4)))=Some(Vint requested)->
    gateway_native_reap_operands memory gateway_poll_definition[Vptr object offset;Vlong Int64.one;Vint timeout]
      (gateway_native_poll_code descriptor requested timeout).

Theorem gateway_native_reap_operands_unique memory definition arguments first second:
  gateway_native_reap_operands memory definition arguments first->
  gateway_native_reap_operands memory definition arguments second->first=second.
Proof.
  intros FIRST SECOND;inversion FIRST;subst;inversion SECOND;subst;try reflexivity;try discriminate.
  match goal with
  | ONE:Mem.loadv Mint32 _ _=Some(Vint ?one),TWO:Mem.loadv Mint32 _ _=Some(Vint ?two),
    FLAGS1:Mem.loadv Mint16signed _ _=Some(Vint ?flags1),FLAGS2:Mem.loadv Mint16signed _ _=Some(Vint ?flags2)|-_=>
    assert(one=two)by congruence;assert(flags1=flags2)by congruence;subst;reflexivity
  end.
Qed.

(* This extends the existing observer for these individual SDK operations only.
   The full row retains actual credentials, reference tables/CWD, optional reply
   and committed product. No normal reply, future return or reap is required. *)
Record gateway_native_reap_row_runtime {World Event}(backend:gateway_backend World Event)
    (process position:World->nat)(rows:World->Event->option(nat*ND.LeanCage_Host_NativeCode_CallRow))
    (pending:Ctypes.fundef Clight.function->list Values.val->mem->World->World->nat->ND.LeanCage_Host_NativeCode_CallRow->Prop):Prop:={
  gateway_native_reap_returned_row:forall definition arguments code before world result after next observed,
    gateway_native_reap_operands before definition arguments code->
    gateway_runtime_operation backend definition arguments before world result after next observed->
    exists selected row,rows world observed=Some(selected,row) /\
      gateway_native_row_process row=Nat_of_nat(process world) /\gateway_native_row_operation row=code /\
      (position world<=selected<position next)%nat;
  gateway_native_reap_pending_row:forall definition arguments code before entry current selected row,
    gateway_native_reap_operands before definition arguments code->pending definition arguments before entry current selected row->
    gateway_native_row_process row=Nat_of_nat(process entry) /\gateway_native_row_operation row=code /\
      (position entry<=selected<position current)%nat
}.

Theorem gateway_actual_reap_native_row {World Event}(backend:gateway_backend World Event)process position rows pending
    (runtime:gateway_native_reap_row_runtime backend process position rows pending)
    definition arguments code before world result after next observed:
  gateway_native_reap_operands before definition arguments code->
  gateway_runtime_operation backend definition arguments before world result after next observed->
  exists selected row,rows world observed=Some(selected,row) /\
    gateway_native_row_process row=Nat_of_nat(process world) /\gateway_native_row_operation row=code /\
    (position world<=selected<position next)%nat.
Proof. intros INPUT OPERATION;eapply gateway_native_reap_returned_row;eassumption. Qed.

Theorem gateway_actual_pending_reap_native_row {World Event}(backend:gateway_backend World Event)process position rows pending
    (runtime:gateway_native_reap_row_runtime backend process position rows pending)
    definition arguments code before entry current selected row:
  gateway_native_reap_operands before definition arguments code->pending definition arguments before entry current selected row->
  gateway_native_row_process row=Nat_of_nat(process entry) /\gateway_native_row_operation row=code /\
    (position entry<=selected<position current)%nat.
Proof. intros INPUT OPERATION;eapply gateway_native_reap_pending_row;eassumption. Qed.
