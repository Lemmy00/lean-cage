(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful original return uses the same decoded status zero. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayFailurePaths GatewayNullReset GatewayIgnoredFailure GatewayResponseReturn GatewayTrailingError
  GatewayExchangeTransport GatewayCleanupSource.
Import ListNotations.

Definition cleanup_status_phase:=exchange_cleanup_after 5.
Definition cleanup_status_body:=match cleanup_status_phase with Ssequence first _=>first|_=>Sskip end.
Definition cleanup_final_return:=match cleanup_status_phase with Ssequence _ rest=>rest|_=>Sskip end.
Definition cleanup_status_select:=match cleanup_status_body with Ssequence first _=>first|_=>Sskip end.
Definition cleanup_status_test:=match cleanup_status_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition cleanup_status_error:=match cleanup_status_test with Sifthenelse _ first _=>first|_=>Sskip end.
Definition cleanup_status_flag word:=if Int64.eq word Int64.zero then Int.zero else Int.one.
Definition cleanup_status_temps word(temporaries:temp_env):=PTree.set _t'54(Vint(cleanup_status_flag word))temporaries.

Theorem actual_cleanup_status_error {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  gateway_failure_result backend ge(State f_host_exchange cleanup_status_error
    (Kseq cleanup_final_return Kstop)environment temporaries memory).
Proof.
  unfold cleanup_status_error.
  repeat response_denied_route.
  trailing_error_ignore.
  repeat response_denied_route.
  trailing_error_ignore.
  repeat response_denied_route.
  response_denied_set_as Vnullptr.
  eapply gateway_failure_edge with(target:=State f_host_exchange cleanup_final_return Kstop environment(PTree.set _result Vnullptr temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  intros before world events value after next RUN.
  eapply gateway_actual_reset_null with(protected:=_result);[|exact RUN].
  left;split;[repeat eexists;reflexivity|]. split;[apply PTree.gss|]. split;[reflexivity|].
  left;cbn;unfold GatewayTempNull.gateway_temp_pointer;repeat eexists;reflexivity.
Qed.

Theorem actual_cleanup_status_select {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory word object offset:
  temporaries!_result=Some(Vptr object offset)->temporaries!_status=Some(Vlong word)->
  (forall before world,property before world->Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)=true)->
  gateway_memory_prefix backend ge
    (State f_host_exchange cleanup_status_test(Kseq cleanup_final_return Kstop)environment(cleanup_status_temps word temporaries)memory)property property
    (State f_host_exchange cleanup_status_phase Kstop environment temporaries memory).
Proof.
  intros RESULT STATUS POINTER.
  eapply gateway_memory_same with(following:=State f_host_exchange cleanup_status_body(Kseq cleanup_final_return Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange cleanup_status_select
    (Kseq cleanup_status_test(Kseq cleanup_final_return Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange(Sset _t'54(Ecast(Etempvar _status tulong)tbool))
    (Kseq cleanup_status_test(Kseq cleanup_final_return Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_if_edge with(v:=Vptr object offset)(b:=true).
    + apply old_expression_value,value_temp;exact RESULT.
    + change((if Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)then Some true else None)=Some true).
      rewrite(POINTER before world READY);reflexivity.
  - eapply gateway_memory_same with(following:=State f_host_exchange Sskip
      (Kseq cleanup_status_test(Kseq cleanup_final_return Kstop))environment(cleanup_status_temps word temporaries)memory);
      [exact CLOSED|cbn;tauto| |].
    + intros before world READY;apply certified_set_edge,old_expression_value;eapply value_cast with(v:=Vlong word);
        [apply value_temp;exact STATUS|reflexivity].
    + eapply gateway_memory_same with(following:=State f_host_exchange cleanup_status_test(Kseq cleanup_final_return Kstop)
        environment(cleanup_status_temps word temporaries)memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
