(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual SDK status values are stored before the next guarded edit. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySDKEditSource GatewayExchangeSetup
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayLaunchPaths.
Import ListNotations.

Theorem actual_sdk_edit_return_path {World Event}(backend:gateway_backend World Event)
    target property(CLOSED:gateway_ambient_closed backend property)edit environment temporaries memory status data_right control_right:
  gateway_launch_path backend target property
    (State f_host_exchange(sdk_edit_after edit)Kstop environment
      (sdk_edit_return_temps edit status data_right control_right temporaries)memory)->
  gateway_launch_path backend target property
    (Returnstate(Vint status)
      (sdk_edit_cont edit environment(sdk_edit_loaded_temps edit data_right control_right temporaries))memory).
Proof.
  intro REST.
  set(returned:=PTree.set(sdk_edit_destination edit)(Vint status)
    (sdk_edit_loaded_temps edit data_right control_right temporaries)).
  eapply gateway_launch_same with(following:=State f_host_exchange Sskip
    (Kseq(sdk_edit_bind edit)(Kseq(sdk_edit_after edit)Kstop))environment returned memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_launch_same with(following:=State f_host_exchange(sdk_edit_bind edit)
    (Kseq(sdk_edit_after edit)Kstop)environment returned memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_launch_same with(following:=State f_host_exchange Sskip(Kseq(sdk_edit_after edit)Kstop)environment
    (sdk_edit_return_temps edit status data_right control_right temporaries)memory);
    [exact CLOSED|cbn;destruct edit;tauto|exact I| |].
  - intros before world READY;destruct edit;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss.
  - eapply gateway_launch_same with(following:=State f_host_exchange(sdk_edit_after edit)Kstop environment
      (sdk_edit_return_temps edit status data_right control_right temporaries)memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|exact REST].
Qed.

Theorem actual_sdk_edit_nonzero_skip {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)edit environment temporaries memory word:
  edit<>gateway_edit_group->temporaries!_setup=Some(Vint word)->Int.eq word Int.zero=false->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange(sdk_edit_after edit)Kstop environment temporaries memory)property property
    (State f_host_exchange(sdk_edit_start edit)Kstop environment temporaries memory).
Proof.
  intros GUARDED SETUP NONZERO.
  eapply gateway_memory_same with(following:=State f_host_exchange(sdk_edit_statement edit)
    (Kseq(sdk_edit_after edit)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;destruct edit;tauto|intros;destruct edit;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq(sdk_edit_after edit)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;destruct edit;tauto| |].
  - intros before world READY;destruct edit;[contradiction|..].
    all:apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;eapply value_unary with(v:=Vint word);
        [apply value_temp;exact SETUP|]|reflexivity].
    all:change(option_map(fun truth=>Val.of_bool(negb truth))(Some(negb(Int.eq word Int.zero)))=Some(Vint Int.zero));
      rewrite NONZERO;reflexivity.
  - eapply gateway_memory_same with(following:=State f_host_exchange(sdk_edit_after edit)Kstop environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
