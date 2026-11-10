(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Thread ownership changes at individual actual runtime APIs. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_native_region (object : block) (offset : ptrofs) (count : Z)
    (block : block) (position : Z) : Prop :=
  block = object /\ Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + count.

(* A future unallocated block can be unreachable from the runtime. Conservation
   only applies to a real live native block or an actual readable retained cell. *)
Definition gateway_access_retained {World}
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    before world next : Prop :=
  (forall block, Mem.valid_block before block -> native_private world block -> native_private next block) /\
  (forall block position, Mem.perm before block position Cur Readable ->
    stable_readonly world block position -> stable_readonly next block position).

Definition gateway_native_frame {World}
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (output : block -> Z -> Prop) world before after : Prop :=
  Mem.unchanged_on (fun block position =>
    (native_private world block \/ stable_readonly world block position) /\ ~ output block position) before after.

Definition gateway_native_no_output (_ : block) (_ : Z) : Prop := False.

Definition gateway_native_pointer before object offset amount permission : Prop :=
  0 <= amount /\ Ptrofs.unsigned offset + amount <= Ptrofs.modulus /\
  Mem.valid_block before object /\
  Mem.range_perm before object (Ptrofs.unsigned offset) (Ptrofs.unsigned offset + amount) Cur permission.

Definition gateway_native_permissions before after object offset amount : Prop :=
  forall position kind permission,
    Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + amount ->
    (Mem.perm before object position kind permission <-> Mem.perm after object position kind permission).

(* None means this thread holds its interpreter/GIL. Some saved means the exact
   PyThreadState token returned by its actual SaveThread call is detached. The
   predicate describes thread/runtime roots, not application buffers or results. *)
Record gateway_thread_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int) : Prop := {
  gateway_thread_ambient : forall mode before world after next,
    discipline mode before world -> gateway_interference backend before world after next ->
    discipline mode after next /\ gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after;

  gateway_thread_fresh_native : forall mode before world object,
    discipline mode before world -> ~ Mem.valid_block before object -> native_private world object;

  gateway_thread_native_stable : forall mode before world object position,
    discipline mode before world -> native_private world object -> stable_readonly world object position;

  gateway_thread_native_alloc : forall mode before world after object low high,
    discipline mode before world -> Mem.alloc before low high = (after, object) ->
    discipline mode after world;

  gateway_thread_native_free : forall mode before world after object low high,
    discipline mode before world -> native_private world object ->
    Mem.free before object low high = Some after -> discipline mode after world;

  gateway_thread_native_store : forall mode before world after object offset chunk value,
    discipline mode before world -> native_private world object ->
    Mem.store chunk before object offset value = Some after -> discipline mode after world;

  gateway_save_thread_operation : forall before world result after next observed,
    discipline None before world ->
    gateway_runtime_operation backend gateway_save_thread_definition []
      before world result after next observed ->
    (exists object offset, result = Vptr object offset) /\
    discipline (Some result) after next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    io observed = None;

  gateway_restore_thread_operation : forall saved before world result after next observed,
    discipline (Some saved) before world ->
    gateway_runtime_operation backend gateway_restore_thread_definition [saved]
      before world result after next observed ->
    discipline None after next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    io observed = None;

  gateway_errno_location_operation : forall mode before world result after next observed,
    discipline mode before world ->
    gateway_runtime_operation backend gateway_errno_location_definition []
      before world result after next observed ->
    exists object offset,
      result = Vptr object offset /\
      gateway_native_pointer after object offset 4 Writable /\
      Mem.loadv Mint32 after (Vptr object offset) = Some (Vint (thread_errno next)) /\
      ~ native_private next object /\
      (forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + 4 ->
        ~ stable_readonly next object position) /\
      discipline mode after next /\
      gateway_access_retained native_private stable_readonly before world next /\
      gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
      io observed = None;

  gateway_clock_operation : forall before world object offset result after next observed,
    discipline None before world -> native_private world object ->
    gateway_native_pointer before object offset 16 Writable ->
    gateway_runtime_operation backend gateway_clock_gettime_definition
      [Vint Int.one; Vptr object offset] before world result after next observed ->
    exists status,
      result = Vint status /\
      (status = Int.zero -> exists seconds nanoseconds,
        0 <= Int64.signed seconds /\ 0 <= Int64.signed nanoseconds < 1000000000 /\
        Mem.loadv Mint64 after (Vptr object offset) = Some (Vlong seconds) /\
        Mem.loadv Mint64 after (Vptr object (Ptrofs.add offset (Ptrofs.repr 8))) = Some (Vlong nanoseconds)) /\
      discipline None after next /\
      gateway_access_retained native_private stable_readonly before world next /\
      gateway_native_permissions before after object offset 16 /\
      gateway_native_frame native_private stable_readonly (gateway_native_region object offset 16)
        world before after /\ io observed = None;

  gateway_poll_operation : forall saved before world object offset result after next observed,
    discipline (Some saved) before world -> native_private world object ->
    gateway_native_pointer before object offset 8 Writable ->
    gateway_runtime_operation backend gateway_poll_definition
      [Vptr object offset; Vlong Int64.one; Vint (Int.repr 100)]
      before world result after next observed ->
    exists status,
      result = Vint status /\ discipline (Some saved) after next /\
      gateway_access_retained native_private stable_readonly before world next /\
      gateway_native_permissions before after object offset 8 /\
      gateway_native_frame native_private stable_readonly
        (gateway_native_region object (Ptrofs.add offset (Ptrofs.repr 6)) 2) world before after /\
      io observed = None;

  gateway_send_operation : forall mode before world descriptor object offset amount result after next observed,
    discipline mode before world ->
    (native_private world object \/ forall position,
      Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + amount ->
      stable_readonly world object position) ->
    0 < amount <= 65536 -> gateway_native_pointer before object offset amount Readable ->
    gateway_runtime_operation backend gateway_send_definition
      [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint (Int.repr 16384)]
      before world result after next observed ->
    exists count bytes,
      -1 <= count <= amount /\ result = Vlong (Int64.repr count) /\
      Z.of_nat (length bytes) = Z.max 0 count /\
      Mem.loadbytes before object (Ptrofs.unsigned offset) (Z.max 0 count) = Some (inj_bytes bytes) /\
      io observed = Some (gateway_native_send descriptor amount count bytes) /\
      discipline mode after next /\ gateway_access_retained native_private stable_readonly before world next /\
      gateway_native_frame native_private stable_readonly gateway_native_no_output world before after;

  gateway_receive_operation : forall saved before world descriptor object offset amount result after next observed,
    discipline (Some saved) before world -> native_private world object ->
    0 < amount <= 65536 -> gateway_native_pointer before object offset amount Writable ->
    gateway_runtime_operation backend gateway_receive_definition
      [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint Int.zero]
      before world result after next observed ->
    exists count bytes,
      -1 <= count <= amount /\ result = Vlong (Int64.repr count) /\
      Z.of_nat (length bytes) = Z.max 0 count /\
      Mem.loadbytes after object (Ptrofs.unsigned offset) (Z.max 0 count) = Some (inj_bytes bytes) /\
      io observed = Some (gateway_native_receive descriptor amount count bytes) /\
      discipline (Some saved) after next /\ gateway_access_retained native_private stable_readonly before world next /\
      gateway_native_permissions before after object offset amount /\
      gateway_native_frame native_private stable_readonly
        (gateway_native_region object offset (Z.max 0 count)) world before after;

  gateway_check_signals_operation : forall before world result after next observed,
    discipline None before world ->
    gateway_runtime_operation backend gateway_check_signals_definition []
      before world result after next observed ->
    exists status,
      result = Vint status /\
      (status = Int.zero -> discipline None after next /\
        gateway_access_retained native_private stable_readonly before world next /\
        gateway_native_frame native_private stable_readonly gateway_native_no_output world before after) /\
      io observed = None;

  gateway_volatile_int_load : forall mode before world pointer result after next observed,
    discipline mode before world ->
    gateway_builtin backend (EF_vload Mint32) [Ctypesdefs.tptr (Ctypesdefs.tvolatile Ctypesdefs.tint)] [pointer]
      before world result after next observed ->
    (exists value, result = Vint value) /\ discipline mode after next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    io observed = None
}.

(* §AR-host-boundary.interfaces: No API frame implicitly freezes mutable runtime TLS or refcounts. *)
Lemma gateway_native_frame_restrict {World} native_private stable_readonly output world before after
    (readonly : block -> Z -> Prop) :
  @gateway_native_frame World native_private stable_readonly output world before after ->
  (forall block position, readonly block position ->
    native_private world block \/ stable_readonly world block position) ->
  (forall block position, readonly block position -> ~ output block position) ->
  Mem.unchanged_on readonly before after.
Proof.
  intros FRAME PROTECTED DISJOINT.
  eapply Mem.unchanged_on_implies; [exact FRAME |].
  intros block position READ; split; [apply PROTECTED | apply DISJOINT]; exact READ.
Qed.
