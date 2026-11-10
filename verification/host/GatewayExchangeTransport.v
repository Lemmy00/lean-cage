(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Retain the actual send, response, EOF and cleanup source phases. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayHeaderTransfer GatewayFailurePaths GatewayNullReset.
Import ListNotations.

Fixpoint exchange_transport_after(count:nat):statement:=match count with
  O=>header_transfer_after|S prior=>match exchange_transport_after prior with Ssequence _ rest=>rest|_=>Sskip end end.
Definition exchange_transport_at count:=match exchange_transport_after count with Ssequence first _=>first|_=>Sskip end.
Definition exchange_shutdown_phase:=exchange_transport_at 1.
Definition exchange_response_phase:=exchange_transport_at 2.
Definition exchange_status_phase:=exchange_transport_at 3.
Definition exchange_response_checks:=exchange_transport_at 4.
Definition exchange_result_phase:=exchange_transport_at 5.
Definition exchange_trailing_phase:=exchange_transport_at 6.
Definition exchange_eof_phase:=exchange_transport_at 7.
Definition exchange_cleanup_phase:=exchange_transport_after 8.
Definition exchange_shutdown_select:=match exchange_shutdown_phase with Ssequence first _=>first|_=>Sskip end.
Definition exchange_shutdown_test:=match exchange_shutdown_phase with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_result_select:=match exchange_result_phase with Ssequence first _=>first|_=>Sskip end.
Definition exchange_result_bind:=match exchange_result_phase with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_trailing_select:=match exchange_trailing_phase with Ssequence first _=>first|_=>Sskip end.
Definition exchange_trailing_test:=match exchange_trailing_phase with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_result_null:=Ecast gateway_null_expression(tptr tvoid).

Theorem actual_exchange_transport_null_shapes:
  exchange_status_phase=Sset _status(Ecast(Econst_int Int.zero tint)tulong) /\
  exchange_result_bind=Sset _result(Etempvar _t'43(tptr tvoid)) /\
  exchange_eof_phase=match exchange_eof_phase with Sifthenelse _ first _=>
    Sifthenelse(Etempvar _result(tptr(Tstruct __object noattr)))first Sskip|_=>Sskip end /\
  gateway_must_reset_temp _result exchange_cleanup_phase.
Proof. repeat split;try reflexivity;vm_compute;intuition eauto. Qed.

Lemma exchange_transport_tail index:
  (index<14)%nat->exchange_transport_after index=Ssequence(exchange_transport_at index)(exchange_transport_after(S index)).
Proof.
  intro INDEX;do 14(destruct index as[|index];[reflexivity|]);lia.
Qed.
