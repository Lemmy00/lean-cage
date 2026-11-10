(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual boolean caller returns the same owned constructor pointer. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueBoolean
  GatewayReturns GatewayFrames.
Import ListNotations.

Definition gateway_object_pointer_value value :Prop:=
  value=Vnullptr \/exists object offset,value=Vptr object offset.

Lemma gateway_value_boolean_pointer_return_path ge flag slots arguments initial memory returned :
  gateway_object_pointer_value returned ->gateway_constant_path ge returned
    (Returnstate returned(gateway_value_boolean_cont flag slots arguments initial)memory).
Proof.
  intro POINTER.
  eapply gateway_constant_next with(next:=State f_host_value Sskip
    (Kseq gateway_value_boolean_return(Kseq gateway_value_after_boolean Kstop))(gateway_value_environment slots)
    (PTree.set _t'3 returned(gateway_value_boolean_parameters flag arguments initial))memory).
  - cbn;tauto.
  - intros;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_constant_next with(next:=State f_host_value gateway_value_boolean_return
      (Kseq gateway_value_after_boolean Kstop)(gateway_value_environment slots)
      (PTree.set _t'3 returned(gateway_value_boolean_parameters flag arguments initial))memory).
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_constant_at_return with(value:=returned).
      * reflexivity.
      * intros;apply old_expression_value,value_temp;apply PTree.gss.
      * intros;destruct POINTER as[NULL|[object[offset PTR]]];subst returned;reflexivity.
Qed.

Theorem gateway_value_boolean_returned {World Event}(backend:gateway_backend World Event)ge flag slots arguments initial
    before world events returned value after next :
  gateway_object_pointer_value returned ->
  gateway_steps backend ge(gateway_live(Returnstate returned(gateway_value_boolean_cont flag slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->value=returned.
Proof.
  intros POINTER RUN;eapply gateway_constant_path_actual;
    [exact(gateway_value_boolean_pointer_return_path ge flag slots arguments initial before returned POINTER)|exact RUN].
Qed.
