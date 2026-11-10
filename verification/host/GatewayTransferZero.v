(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Empty absent fields need no fabricated live data or stream object. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayOperations GatewayFrames GatewayReadonly GatewayTransferSource GatewayTransferLoop.
Import ListNotations.

Definition transfer_direction_parameters stream data amount direction:=
  PTree.set _sending(Vint direction)(PTree.set _size(Vlong(Int64.repr amount))
    (PTree.set _data data(PTree.set _stream stream(create_undef_temps(fn_temps f_host_transfer))))).
Definition transfer_direction_loop_values stream data amount direction:=
  PTree.set _cursor data(transfer_direction_parameters stream data amount direction).

Lemma actual_transfer_direction_entry ge stream data amount direction memory:
  function_entry2 ge f_host_transfer[stream;data;Vlong(Int64.repr amount);Vint direction]memory
    empty_env(transfer_direction_parameters stream data amount direction)memory.
Proof.
  constructor.
  - apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros a b LEFT RIGHT.
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst a;
      repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst b;discriminate.
  - constructor.
  - reflexivity.
Qed.

Theorem actual_zero_transfer_direction_path ge stream data direction memory:
  gateway_pure_path ge
    (Callstate(Internal f_host_transfer)[stream;data;Vlong Int64.zero;Vint direction]Kstop memory)(Vint Int.zero).
Proof.
  eapply gateway_pure_next with(next:=State f_host_transfer(fn_body f_host_transfer)Kstop empty_env
    (transfer_direction_parameters stream data 0 direction)memory);
    [cbn;tauto|intros;apply function_entry_source_edge,actual_transfer_direction_entry|].
  eapply gateway_pure_next with(next:=State f_host_transfer(Sset _cursor(Etempvar _data(tptr tvoid)))
    (Kseq transfer_tail Kstop)empty_env(transfer_direction_parameters stream data 0 direction)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_pure_next with(next:=State f_host_transfer Sskip(Kseq transfer_tail Kstop)empty_env
    (transfer_direction_loop_values stream data 0 direction)memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value,value_temp;reflexivity|].
  eapply gateway_pure_next with(next:=State f_host_transfer transfer_tail Kstop empty_env
    (transfer_direction_loop_values stream data 0 direction)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_pure_next with(next:=State f_host_transfer transfer_loop transfer_loop_cont empty_env
    (transfer_direction_loop_values stream data 0 direction)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  apply actual_zero_transfer_loop_path;reflexivity.
Qed.

Theorem gateway_actual_empty_transfer {World Event}(backend:gateway_backend World Event)ge
    (side:mem->World->Prop)(ambient:gateway_runtime_discipline backend side)
    stream data direction before world events returned after next:
  side before world->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_transfer)[stream;data;Vlong Int64.zero;Vint direction]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=Vint Int.zero /\side after next /\Forall gateway_quiet_event events.
Proof.
  intros READY RUN.
  exact(gateway_pure_path_ready_return backend ge side ambient _ _ world events returned after next
    (actual_zero_transfer_direction_path ge stream data direction before)READY RUN).
Qed.
