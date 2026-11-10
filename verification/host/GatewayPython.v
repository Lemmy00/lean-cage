(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Individual CPython operations expose bytes, references and errors. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource.
Import ListNotations.
Open Scope Z_scope.

Record python_bytes := {
  python_bytes_block : block;
  python_bytes_offset : Z;
  python_bytes_contents : list Byte.int
}.

Definition python_bytes_pointer bytes :=
  Vptr (python_bytes_block bytes) (Ptrofs.repr (python_bytes_offset bytes)).

Definition python_bytes_loaded m bytes :=
  0 <= python_bytes_offset bytes /\
  python_bytes_offset bytes + Z.of_nat(List.length(python_bytes_contents bytes)) + 1 <= Ptrofs.modulus /\
  Mem.range_perm m (python_bytes_block bytes) (python_bytes_offset bytes)
    (python_bytes_offset bytes + Z.of_nat(List.length(python_bytes_contents bytes)) + 1) Cur Readable /\
  Mem.loadbytes m (python_bytes_block bytes) (python_bytes_offset bytes)
    (Z.of_nat(List.length(python_bytes_contents bytes))) = Some(inj_bytes(python_bytes_contents bytes)).

Inductive python_value :=
| python_byte_value (bytes:python_bytes)
| python_other_value.

Inductive python_error_kind :=
| python_type_error | python_value_error | python_os_error | python_timeout_error
| python_memory_error | python_interrupt | python_runtime_error.

Record python_error := {
  python_error_type : python_error_kind;
  python_error_message : list Byte.int
}.

(* Counts represent logical strong references, including immortal runtime values.
   They are not a claim that immortal objects increment the physical ob_refcnt. *)
Record python_world := {
  python_values : Values.val -> option python_value;
  python_strong : Values.val -> nat;
  python_native_strong : Values.val -> nat;
  python_runtime_owned : block -> Prop;
  python_gil : bool;
  python_pending : option python_error
}.

Definition python_world_valid world m :=
  (forall object, (python_native_strong world object <= python_strong world object)%nat) /\
  (forall object bytes, python_values world object = Some(python_byte_value bytes) ->
    (0 < python_strong world object)%nat -> python_bytes_loaded m bytes) /\
  (forall object, python_runtime_owned world object -> Mem.valid_block m object) /\
  (forall object value, python_values world object=Some value ->
    (0<python_strong world object)%nat ->
    (exists block offset,object=Vptr block offset /\ python_runtime_owned world block) /\
    match value with
    |python_byte_value bytes=>python_runtime_owned world(python_bytes_block bytes)
    |python_other_value=>True
    end).

Definition python_live world object :=
  (0 < python_strong world object)%nat /\ exists value, python_values world object = Some value.

(* Native stack fields do not belong to the runtime's heap/TLS. Each API preserves them
   unless they are one of that API's explicit writable output parameters. *)
Definition python_private_frame world before after :=
  Mem.unchanged_on (fun object _ => ~python_runtime_owned world object) before after.

Definition python_bytes_definition : Ctypes.fundef Clight.function := External
  (EF_external "PyBytes_AsStringAndSize"%string
    (mksignature [Xptr;Xptr;Xptr] Xint cc_default))
  [tptr(Tstruct __object noattr);tptr(tptr tschar);tptr tlong] tint cc_default.

Definition python_incref_definition : Ctypes.fundef Clight.function := External
  (EF_external "Py_IncRef"%string (mksignature [Xptr] Xvoid cc_default))
  [tptr(Tstruct __object noattr)] tvoid cc_default.

(* This is one actual API operation, not a host-field or caller extraction assumption.
   Its two output writes are explicit. Incorrect types return an exception; loss
   and blocked prefixes belong to the machine and never synthesize a return. *)
Inductive python_bytes_return world object data_cell size_cell before :
    int -> mem -> python_world -> Prop :=
| python_bytes_succeeded : forall bytes middle after,
    python_gil world = true -> python_pending world = None ->
    python_live world object ->
    python_values world object = Some(python_byte_value bytes) ->
    python_bytes_loaded before bytes ->
    Z.of_nat(List.length(python_bytes_contents bytes)) <= Int64.max_signed ->
    Mem.storev Mptr before data_cell (python_bytes_pointer bytes) = Some middle ->
    Mem.storev Mint64 middle size_cell
      (Vlong(Int64.repr(Z.of_nat(List.length(python_bytes_contents bytes))))) = Some after ->
    python_bytes_return world object data_cell size_cell before Int.zero after world
| python_bytes_failed : forall after next error,
    python_gil world = true -> python_pending world = None ->
    python_live world object ->
    (forall bytes, python_values world object <> Some(python_byte_value bytes)) ->
    (python_error_type error = python_type_error \/ python_error_type error = python_memory_error) ->
    python_pending next = Some error -> python_gil next = true ->
    python_private_frame world before after -> python_world_valid next after ->
    python_bytes_return world object data_cell size_cell before (Int.neg Int.one) after next.

Record python_incref_return world object before next after := {
  python_incref_gil : python_gil world = true;
  python_incref_live : python_live world object;
  python_incref_object : exists block offset, object = Vptr block offset /\
    Mem.unchanged_on (fun other _ => other <> block) before after;
  python_incref_values : python_values next = python_values world;
  python_incref_count : python_strong next object = S(python_strong world object);
  python_incref_native : python_native_strong next object = S(python_native_strong world object);
  python_incref_others : forall other, other <> object ->
    python_strong next other = python_strong world other /\
    python_native_strong next other = python_native_strong world other;
  python_incref_heap : python_runtime_owned next = python_runtime_owned world;
  python_incref_permissions : forall block offset kind permission,
    Mem.perm before block offset kind permission <-> Mem.perm after block offset kind permission;
  python_incref_next_gil : python_gil next = true;
  python_incref_pending : python_pending next = python_pending world;
  python_incref_next_valid : python_world_valid next after
}.

Theorem python_bytes_success_actual_values world object data size before value after next :
  python_bytes_return world object data size before value after next -> value = Int.zero ->
  exists bytes middle,
    next = world /\ python_values world object = Some(python_byte_value bytes) /\
    Mem.storev Mptr before data (python_bytes_pointer bytes) = Some middle /\
    Mem.storev Mint64 middle size
      (Vlong(Int64.repr(Z.of_nat(List.length(python_bytes_contents bytes))))) = Some after.
Proof.
  intros CALL ZERO;inversion CALL;subst.
  - exists bytes,middle;auto.
  - assert(BAD:Int.neg Int.one=Int.zero)by congruence.
    apply(f_equal Int.unsigned)in BAD.
    change(4294967295=0)in BAD;discriminate.
Qed.

Theorem python_incref_supplies_native_reference world object before next after :
  python_incref_return world object before next after ->
  (0 < python_native_strong next object)%nat /\
  (0 < python_strong next object)%nat.
Proof. intros CALL;destruct CALL;split;lia. Qed.

Theorem python_bytes_success_loads world object data size before value after next :
  data <> size ->
  python_bytes_return world object (Vptr data Ptrofs.zero)(Vptr size Ptrofs.zero)
    before value after next -> value = Int.zero ->
  exists bytes,
    next = world /\ python_values world object = Some(python_byte_value bytes) /\
    Mem.load Mptr after data 0 = Some(python_bytes_pointer bytes) /\
    Mem.load Mint64 after size 0 =
      Some(Vlong(Int64.repr(Z.of_nat(List.length(python_bytes_contents bytes))))).
Proof.
  intros DISTINCT CALL ZERO.
  destruct(python_bytes_success_actual_values _ _ _ _ _ _ _ _ CALL ZERO)
    as[bytes[middle[NEXT[BYTES[DATA SIZE]]]]].
  change(Mem.store Mptr before data 0(python_bytes_pointer bytes)=Some middle)in DATA.
  change(Mem.store Mint64 middle size 0
    (Vlong(Int64.repr(Z.of_nat(List.length(python_bytes_contents bytes)))))=Some after)in SIZE.
  exists bytes;split;[exact NEXT|]. split;[exact BYTES|].
  split.
  - rewrite(Mem.load_store_other _ _ _ _ _ _ SIZE Mptr data 0)by auto.
    pose proof(Mem.load_store_same _ _ _ _ _ _ DATA)as LOAD.
    exact LOAD.
  - exact(Mem.load_store_same _ _ _ _ _ _ SIZE).
Qed.
