(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: A useful formatter outcome inhabits the precise primitive contract. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Clight.
Require Import Machine ErrorNumber.
From EntryNative Require Import NativeHandoffMachine.
From LeanCageMainNumber Require Import NumberMemory.
Import ListNotations.
Open Scope Z_scope.

Theorem handoff_format_bytes_witness cell before output offset error bytes :
  entry_format_owned before output offset ->
  initialized_errno cell before error -> output <> tls_block cell ->
  1 <= Z.of_nat (length bytes) <= 31 -> Forall (fun byte=>byte<>Byte.zero) bytes ->
  exists after,
    Mem.storebytes before output (Ptrofs.unsigned offset) (map Byte (bytes++[Byte.zero])) = Some after /\
    number_input after output offset bytes /\ initialized_errno cell after error /\
    entry_format_result cell before output offset (Int.repr (Z.of_nat (length bytes))) after.
Proof.
  intros [BOUND OWN] ERRNO SEPARATE SIZE NONZERO.
  assert (LENGTH:Z.of_nat (length (map Byte (bytes++[Byte.zero])))=Z.of_nat(length bytes)+1).
  { rewrite length_map,length_app; cbn; lia. }
  destruct (Mem.range_perm_storebytes before output (Ptrofs.unsigned offset)
    (map Byte (bytes++[Byte.zero]))) as [after STORE].
  { red; intros position RANGE; apply OWN; rewrite LENGTH in RANGE; lia. }
  assert (INPUT:number_input after output offset bytes).
  { unfold number_input; split.
    - rewrite length_app; cbn; lia.
    - split; [exact NONZERO|].
      pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ STORE) as READ.
      rewrite length_map in READ; exact READ. }
  assert (ERRNO_AFTER:initialized_errno cell after error).
  { destruct ERRNO as [LOW [HIGH [ACCESS LOAD]]]; split; [exact LOW|].
    split; [exact HIGH|]. split.
    - eapply Mem.storebytes_valid_access_1; eassumption.
    - rewrite (Mem.load_storebytes_other _ _ _ _ _ STORE); [exact LOAD|left; congruence]. }
  exists after; split; [exact STORE|]. split; [exact INPUT|]. split; [exact ERRNO_AFTER|].
  constructor.
  - eapply Mem.storebytes_unchanged_on; [exact STORE|].
    intros position RANGE [[DIFFERENT|[LOW|HIGH]] TLS]; try contradiction;
      rewrite LENGTH in RANGE; lia.
  - intros object position kind permission; split;
      [eapply Mem.perm_storebytes_2|eapply Mem.perm_storebytes_1]; eassumption.
  - exists error; exact ERRNO_AFTER.
  - intros RETURNED; exists bytes; split; [|exact INPUT].
    rewrite Int.signed_repr; [reflexivity|].
    change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
Qed.

Theorem handoff_format_useful_step ge cell before output offset error bytes value k :
  entry_format_owned before output offset ->
  initialized_errno cell before error -> output <> tls_block cell ->
  1 <= Z.of_nat (length bytes) <= 31 -> Forall (fun byte=>byte<>Byte.zero) bytes ->
  exists after,
    number_input after output offset bytes /\ initialized_errno cell after error /\
    entry_handoff_step ge cell
      (live (Callstate entry_decimal_definition [Vptr output offset;Vlong value] k before))
      (entry_formatted output offset value (Int.repr (Z.of_nat (length bytes))))
      (live (Returnstate (Vint (Int.repr (Z.of_nat (length bytes)))) k after)).
Proof.
  intros OWN ERRNO SEPARATE SIZE NONZERO.
  destruct (handoff_format_bytes_witness _ _ _ _ _ _ OWN ERRNO SEPARATE SIZE NONZERO)
    as [after [STORE [INPUT [PRESERVED RESULT]]]].
  exists after; split; [exact INPUT|]. split; [exact PRESERVED|].
  apply entry_format_step; assumption.
Qed.
