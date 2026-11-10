(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The source compiler environment fixes the actual native field ABI. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Errors
  Ctypes Ctypesdefs Cop Clight.
From HostGateway Require Import GatewaySource GatewayFieldStores.
Import ListNotations.
Open Scope Z_scope.

Definition actual_field_members :=
  [Member_plain _kind tuint;Member_plain _size tulong;Member_plain _data(tptr tschar);
   Member_plain _root(tptr(Tstruct __object noattr));Member_plain _scalar(tarray tuchar 8)].

Lemma actual_field_members_from_source :
  option_map co_members((prog_comp_env prog)!_host_field)=Some actual_field_members.
Proof. vm_compute;reflexivity. Qed.

Theorem actual_field_layout :
  field_member_layout(Clight.globalenv prog)_kind 0 /\
  field_member_layout(Clight.globalenv prog)_size 8 /\
  field_member_layout(Clight.globalenv prog)_data 16 /\
  field_member_layout(Clight.globalenv prog)_root 24.
Proof.
  pose proof actual_field_members_from_source as MEMBERS.
  destruct((prog_comp_env prog)!_host_field)as[composite|]eqn:LOOK;[|discriminate].
  cbn in MEMBERS;injection MEMBERS as MEMBERS.
  split.
  - exists composite;split;[exact LOOK|rewrite MEMBERS;reflexivity].
  - split.
    + exists composite;split;[exact LOOK|rewrite MEMBERS;reflexivity].
    + split.
      * exists composite;split;[exact LOOK|rewrite MEMBERS;reflexivity].
      * exists composite;split;[exact LOOK|rewrite MEMBERS;reflexivity].
Qed.
