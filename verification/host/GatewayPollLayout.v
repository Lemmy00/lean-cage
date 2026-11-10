(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Poll arguments use the actual SDK local layout and cells. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Errors Ctypes Ctypesdefs Cop Clight.
Require Import Machine LocalAccess StoreSteps CallAccess.
From HostGateway Require Import GatewaySource GatewayReadySource.
Import ListNotations.
Open Scope Z_scope.

Definition poll_member_layout (ge : Clight.genv) member delta : Prop :=
  exists composite, (genv_cenv ge) ! _pollfd = Some composite /\
    field_offset (genv_cenv ge) member (co_members composite) = OK (delta, Full).

Definition actual_poll_members := [Member_plain _fd tint; Member_plain _events tshort; Member_plain _revents tshort].

Theorem actual_poll_layout :
  poll_member_layout (Clight.globalenv prog) _fd 0 /\
  poll_member_layout (Clight.globalenv prog) _events 4 /\
  poll_member_layout (Clight.globalenv prog) _revents 6.
Proof.
  assert (MEMBERS : option_map co_members ((prog_comp_env prog) ! _pollfd) = Some actual_poll_members) by
    (vm_compute; reflexivity).
  destruct ((prog_comp_env prog) ! _pollfd) as [composite |] eqn:LOOK; [|discriminate].
  cbn in MEMBERS; injection MEMBERS as MEMBERS.
  unfold poll_member_layout; repeat split.
  all: exists composite; split; [exact LOOK | rewrite MEMBERS; reflexivity].
Qed.

Definition poll_member member ty := Efield (Evar _item ready_item_type) member ty.

Lemma actual_poll_member_location ge item temporaries memory member ty delta :
  poll_member_layout ge member delta ->
  location_value ge (ready_environment item) temporaries memory (poll_member member ty) item (Ptrofs.repr delta).
Proof.
  intros [composite [LAYOUT MEMBER]].
  unfold poll_member.
  rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  eapply struct_location_value with (id := _pollfd) (co := composite) (att := noattr) (delta := delta).
  - apply location_read_value with (b := item) (ofs := Ptrofs.zero).
    + apply local_location_value; apply PTree.gss.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - exact LAYOUT.
  - exact MEMBER.
Qed.

Lemma actual_poll_member_store ge item temporaries before member ty delta chunk expression value converted after continuation :
  poll_member_layout ge member delta -> access_mode ty = By_value chunk ->
  expression_value ge (ready_environment item) temporaries before expression value ->
  sem_cast value (typeof expression) ty before = Some converted ->
  Mem.storev chunk before (Vptr item (Ptrofs.repr delta)) converted = Some after ->
  store_edge ge
    (State f_host_ready (Sassign (poll_member member ty) expression) continuation (ready_environment item) temporaries before)
    (State f_host_ready Sskip continuation (ready_environment item) temporaries after).
Proof.
  intros LAYOUT ACCESS VALUE CAST STORE.
  eapply assignment_source_edge with (b := item) (ofs := Ptrofs.repr delta) (v := value) (w := converted).
  - apply actual_poll_member_location; exact LAYOUT.
  - exact VALUE.
  - exact CAST.
  - eapply assign_loc_value; [exact ACCESS | exact STORE].
Qed.
