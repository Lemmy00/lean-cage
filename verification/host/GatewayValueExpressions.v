(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Dispatch loads use the value call's actual local word cells. *)
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import LocalAccess.
From HostGateway Require Import GatewaySource GatewayValueEntry.

Lemma gateway_value_tag_expression ge slots temporaries memory tag :
  Mem.loadv Mint64 memory(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong tag) ->
  expression_value ge(gateway_value_environment slots)temporaries memory(Evar _tag tulong)(Vlong tag).
Proof.
  intro LOAD;apply location_read_value with(b:=gateway_value_tag_slot slots)(ofs:=Ptrofs.zero).
  - apply local_location_value;unfold gateway_value_environment;rewrite PTree.gso by discriminate;apply PTree.gss.
  - apply deref_loc_value with(chunk:=Mint64);[reflexivity|exact LOAD].
Qed.
