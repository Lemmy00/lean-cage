(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.input: Derive the receiver's first loop state from independent allocations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll LocalAccess ResultLayout
  ProcessEffects SenderSource DecoderControl SenderReportMemory FreshMemory ReceiverSource ReceiverAllocation
  ReceiverReadSource ReceiverReadMemory.
Import ListNotations.
Open Scope Z_scope.

Definition receiver_slots_owned base b m :=
  NoDup(map fst(receiver_objects b)) /\
  Forall(fun obj=>~Mem.valid_block base(fst obj) /\
    Mem.range_perm m (fst obj) 0 (snd obj) Cur Freeable)(receiver_objects b).
Lemma receiver_slot : forall base b m local size,
  receiver_slots_owned base b m -> In(local,size)(receiver_objects b) ->
  ~Mem.valid_block base local /\ Mem.range_perm m local 0 size Cur Freeable.
Proof. intros base b m local size [_ OWN] IN;rewrite Forall_forall in OWN;exact(OWN _ IN). Qed.

Lemma receiver_slots_store : forall base b m chunk local ofs value after,
  receiver_slots_owned base b m -> Mem.store chunk m local ofs value=Some after ->
  receiver_slots_owned base b after.
Proof.
  intros base b m chunk local ofs value after [DISTINCT OWN] STORE;split;[exact DISTINCT|].
  rewrite Forall_forall in *;intros [object size] IN;destruct(OWN _ IN)as[FRESH PERMS].
  split;[exact FRESH|]. intros pos RANGE;eapply Mem.perm_store_1;[exact STORE|apply PERMS;exact RANGE].
Qed.

Theorem receiver_initial_storage : forall cell base fd,
  tls_ready cell base -> exists b allocated initialized,
  receiver_allocations base b allocated /\
  Mem.store Mint32 allocated (rb_pipe b) 0 (Vint fd)=Some initialized /\
  old_memory base allocated /\ old_memory base initialized /\
  receiver_slots_owned base b initialized /\
  Mem.load Mint32 initialized (rb_pipe b) 0=Some(Vint fd) /\
  receiver_buffer cell b initialized [].
Proof.
  intros cell base fd TLS.
  destruct(receiver_allocation_exists base)as[b[allocated ALLOC]].
  destruct(receiver_allocation_ownership _ _ _ ALLOC)as[OLD [DISTINCT SLOTS]].
  assert(OWN : receiver_slots_owned base b allocated)by(split;assumption).
  assert(PIPE : ~Mem.valid_block base(rb_pipe b) /\
    Mem.range_perm allocated (rb_pipe b) 0 4 Cur Freeable).
  { eapply receiver_slot;[exact OWN|unfold receiver_objects;cbn;tauto]. }
  assert(ACCESS : Mem.valid_access allocated Mint32(rb_pipe b)0 Writable).
  { split;[|exists 0;reflexivity]. intros pos RANGE;eapply Mem.perm_implies;
      [apply(proj2 PIPE);exact RANGE|constructor]. }
  destruct(Mem.valid_access_store _ _ _ _ (Vint fd)ACCESS)as[initialized STORE].
  assert(OLD' : old_memory base initialized).
  { eapply Mem.unchanged_on_trans;[exact OLD|]. eapply Mem.store_unchanged_on;[exact STORE|].
    intros pos RANGE VALID;exact(proj1 PIPE VALID). }
  pose proof(receiver_slots_store _ _ _ _ _ _ _ _ OWN STORE)as SLOTS'.
  assert(BUFFER : ~Mem.valid_block base(rb_bytes b) /\
    Mem.range_perm initialized (rb_bytes b) 0 9 Cur Freeable).
  { eapply receiver_slot;[exact SLOTS'|unfold receiver_objects;cbn;tauto]. }
  exists b,allocated,initialized;split;[exact ALLOC|]. split;[exact STORE|].
  split;[exact OLD|]. split;[exact OLD'|]. split;[exact SLOTS'|]. split.
  - erewrite Mem.load_store_same by exact STORE;reflexivity.
  - split;[cbn;lia|]. split;[eapply old_memory_tls;eassumption|].
    split;[eapply fresh_tls_separate;[exact TLS|exact(proj1 BUFFER)]|].
    split;[exact(proj2 BUFFER)|]. apply Mem.loadbytes_empty;change(0<=0);lia.
Qed.

Ltac receiver_prepare_route := eapply store_next;
  [assumption|apply unchanged_store_edge;WriteAll.structural|].
Theorem receiver_preparation_source : forall (P : mem -> Prop) base b allocated initialized
  output ofs fd bad entered done status k,
  receiver_allocations base b allocated ->
  Mem.store Mint32 allocated (rb_pipe b) 0 (Vint fd)=Some initialized ->
  P base -> P allocated -> P initialized ->
  exists count,store_path result_ge P
    (receiver_initial output ofs fd bad entered done status k base) count
    (receiver_loop_state b
      (PTree.set _used (Vlong Int64.zero) (receiver_temps output ofs fd bad entered done status)) k initialized).
Proof.
  intros P base b allocated initialized output ofs fd bad entered done status k ALLOC STORE PB PA PI.
  eexists;eapply store_next;[exact PB|eapply receiver_entry_source;exact ALLOC|].
  rewrite receiver_source_body. receiver_prepare_route.
  unfold receiver_init_fd,first_statement.
  eapply store_next;[exact PA| |].
  - eapply assignment_source_edge;[receiver_location|
      unfold receiver_temps;receiver_expression|reflexivity|].
    apply assign_loc_value with(chunk:=Mint32);[reflexivity|exact STORE].
  - receiver_prepare_route. receiver_prepare_route.
    unfold receiver_init_used,first_statement;cbn [statement_drop].
    eapply store_next;[exact PI|apply unchanged_store_edge;eapply edge_set;decoder_control_expression|].
    receiver_prepare_route. receiver_prepare_route. apply store_done;exact PI.
Qed.
