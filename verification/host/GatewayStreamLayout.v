(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The real compiler environment supplies every stream cell offset. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Errors Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource.
Import ListNotations.
Open Scope Z_scope.

Definition stream_member_layout(ge:Clight.genv)member delta :Prop:=
  exists composite,(genv_cenv ge)!_host_stream=Some composite /\
    field_offset(genv_cenv ge)member(co_members composite)=OK(delta,Full).

Definition actual_stream_members :=
  [Member_plain _descriptor tint;Member_plain _control tint;
   Member_plain _cancellation_sent tint;Member_plain _cli tint;
   Member_plain _cancellation(tptr(Tstruct __9088 noattr));
   Member_plain _remaining tulong;Member_plain _nodes tulong;Member_plain _deadline tdouble].

Lemma actual_stream_members_from_source :
  option_map co_members((prog_comp_env prog)!_host_stream)=Some actual_stream_members.
Proof. vm_compute;reflexivity. Qed.

Theorem actual_stream_layout :
  stream_member_layout(Clight.globalenv prog)_descriptor 0 /\
  stream_member_layout(Clight.globalenv prog)_control 4 /\
  stream_member_layout(Clight.globalenv prog)_cancellation_sent 8 /\
  stream_member_layout(Clight.globalenv prog)_cli 12 /\
  stream_member_layout(Clight.globalenv prog)_cancellation 16 /\
  stream_member_layout(Clight.globalenv prog)_remaining 24 /\
  stream_member_layout(Clight.globalenv prog)_nodes 32 /\
  stream_member_layout(Clight.globalenv prog)_deadline 40.
Proof.
  pose proof actual_stream_members_from_source as MEMBERS.
  destruct((prog_comp_env prog)!_host_stream)as[composite|]eqn:LOOK;[|discriminate].
  cbn in MEMBERS;injection MEMBERS as MEMBERS.
  unfold stream_member_layout;repeat split.
  all:exists composite;split;[exact LOOK|rewrite MEMBERS;reflexivity].
Qed.
