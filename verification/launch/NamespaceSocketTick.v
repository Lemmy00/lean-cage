(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Each C socket operation keeps its actual shared source occurrence. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessJournal.
From EntryNamespace Require Import NamespaceObjects NamespaceSocket NamespaceHandles NamespacePhysical NamespaceChannel.
Import ListNotations.
Local Close Scope lean_scope.

Fixpoint source_socket_values(bytes:list Byte.int):ProcessImport.List_inst1 Lean.Nat:=match bytes with
  |[]=>ProcessImport.List_nil_inst1 Lean.Nat
  |byte::rest=>ProcessImport.List_cons_inst1 Lean.Nat(Nat_of_nat(Z.to_nat(Byte.unsigned byte)))
    (source_socket_values rest)end.

Theorem source_socket_values_valid bytes:physical_bytes_valid(source_socket_values bytes)=true.
Proof.
  induction bytes as[|byte rest IH];[reflexivity|].
  cbn[source_socket_values physical_bytes_valid];rewrite nat2Natid,IH,andb_true_r.
  apply Nat.leb_le;pose proof(Byte.unsigned_range byte)as RANGE.
  change(0<=Byte.unsigned byte<256)%Z in RANGE;lia.
Qed.

Theorem source_socket_values_exact bytes:physical_bytes(source_socket_values bytes)=bytes.
Proof.
  induction bytes as[|byte rest IH];[reflexivity|].
  cbn[source_socket_values physical_bytes];rewrite nat2Natid,Z2Nat.id by(pose proof(Byte.unsigned_range byte);lia).
  rewrite Byte.repr_unsigned,IH;reflexivity.
Qed.

(* Reuse the shared indexed source-write recording, so this projection adds
   no independent socket transcript or operation-origin assumption. *)
Definition SourceSocketTick(runs:list CallerSourceRun)(tick:LeanCage_Entry_CallerPhysical_Tick):Prop:=
  exists actor fd bytes lost,SourceWrite runs tick actor fd bytes lost.

Theorem source_socket_tick_resolves runs tick:
  SourceSocketTick runs tick ->exists run program ordinal event io,
    nth_error runs program=Some run /\nth_error(source_events run)ordinal=Some event /\
    namespace_socket_io event=Some io /\IO.operation(source_socket_request io)=IO.writing /\
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      (ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference
        (LeanCage_Entry_CallerPhysical_SourceReference_mk(Nat_of_nat program)(Nat_of_nat ordinal))) /\
    ProcessImport.socket tick=
      (LeanCage_Entry_CallerPhysical_SocketObservation_wrote(source_actor run)
        (native_descriptor_number(IO.descriptor(source_socket_request io)))
        (source_socket_values(source_socket_bytes io))(physical_flag(source_socket_lost io))).
Proof.
  intros[actor[fd[bytes[lost SOURCE]]]].
  destruct SOURCE as[run program ordinal event io PROGRAM EVENT IO WRITING ACTOR FD BYTES LOST SOCKET REFERENCE].
  subst actor fd bytes lost.
  exists run,program,ordinal,event,io;repeat split;try assumption.
Qed.

Lemma source_descriptor_roundtrip descriptor actual:
  physical_descriptor(native_descriptor_number descriptor)=Some actual ->actual=descriptor.
Proof.
  unfold physical_descriptor,native_descriptor_number;rewrite nat2Natid,Z2Nat.id by
    (pose proof(Int.unsigned_range descriptor);lia).
  destruct(Z.leb(Int.unsigned descriptor)Int.max_signed);[|discriminate].
  intro SAME;inversion SAME;apply Int.repr_unsigned.
Qed.

Lemma physical_select_write_fields tables actor channel number values lost sender fd bytes acknowledgement:
  physical_select tables actor channel number(fun descriptor=>channel_sent actor descriptor values lost)=
    channel_sent sender fd bytes acknowledgement ->
  sender=actor /\bytes=values /\acknowledgement=lost /\physical_descriptor number=Some fd.
Proof.
  unfold physical_select.
  destruct(physical_descriptor number)as[actual|]eqn:FD;[|discriminate].
  destruct(tables actor actual)as[binding|];[|discriminate].
  destruct(descriptor_object binding)as[ordinary|actual_channel side];[discriminate|].
  destruct(Nat.eqb actual_channel channel);[|discriminate].
  intro SAME;inversion SAME;subst;auto.
Qed.

Theorem actual_sent_tick_has_source_write runs tick channel parent fd bytes lost:
  SourceSocketTick runs tick ->
  physical_tick_projection channel tick=(physical_tick_table tick,channel_sent parent fd bytes lost) ->
  exists run program ordinal event io,
    nth_error runs program=Some run /\nth_error(source_events run)ordinal=Some event /\
    namespace_socket_io event=Some io /\IO.operation(source_socket_request io)=IO.writing /\
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference
        (LeanCage_Entry_CallerPhysical_SourceReference_mk(Nat_of_nat program)(Nat_of_nat ordinal)) /\
    parent=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run)) /\
    fd=IO.descriptor(source_socket_request io) /\bytes=source_socket_bytes io /\lost=source_socket_lost io.
Proof.
  intros SOURCE PROJECT.
  destruct(source_socket_tick_resolves _ _ SOURCE)
    as[run[program[ordinal[event[io[PROGRAM[EVENT[IO[WRITING[REFERENCE SOCKET]]]]]]]]]].
  unfold physical_tick_projection in PROJECT;rewrite SOCKET,source_socket_values_valid in PROJECT.
  cbn beta iota zeta in PROJECT;injection PROJECT as SAME.
  destruct(physical_select_write_fields _ _ _ _ _ _ _ _ _ _ SAME)as[PARENT[BYTES[LOST FD]]].
  rewrite source_socket_values_exact in BYTES.
  assert(ACK:lost=source_socket_lost io).
  { rewrite LOST;destruct(source_socket_lost io);reflexivity. }
  pose proof(source_descriptor_roundtrip _ _ FD)as DESCRIPTOR.
  exists run,program,ordinal,event,io;repeat split;assumption.
Qed.

Theorem actual_journal_write_is_source_socket runs tick actor fd bytes lost:
  SourceWrite runs tick actor fd bytes lost ->SourceSocketTick runs tick.
Proof. intro SOURCE;exists actor,fd,bytes,lost;exact SOURCE. Qed.
