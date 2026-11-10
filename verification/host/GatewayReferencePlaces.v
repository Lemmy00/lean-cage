(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The actual call stack distinguishes live source owners. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Maps Values Memory Clight.
From HostGateway Require Import GatewayReferenceLedger.
Import ListNotations.

Fixpoint gateway_reference_depth(continuation:Clight.cont):nat:=
  match continuation with
  |Kstop=>0
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>gateway_reference_depth rest
  |Kcall _ _ _ _ rest=>S(gateway_reference_depth rest)
  end.

Fixpoint gateway_reference_saved_temporary continuation invocation identifier:option Values.val:=
  match continuation with
  |Kstop=>None
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>
    gateway_reference_saved_temporary rest invocation identifier
  |Kcall _ _ _ temporaries rest=>
    if Nat.eq_dec invocation(gateway_reference_depth rest) then temporaries!identifier
    else gateway_reference_saved_temporary rest invocation identifier
  end.

Definition gateway_reference_place_value(ge:Clight.genv)(source:Clight.state)
    (place:gateway_reference_place)(pointer:Values.val):Prop:=
  let memory:=match source with State _ _ _ _ _ m|Callstate _ _ _ m|Returnstate _ _ m=>m end in
  match place with
  |gateway_reference_temporary invocation identifier=>
    match source with
    |State _ _ continuation _ temporaries _=>
      (if Nat.eq_dec invocation(gateway_reference_depth continuation)then temporaries!identifier
       else gateway_reference_saved_temporary continuation invocation identifier)=Some pointer
    |Callstate _ _ continuation _|Returnstate _ continuation _=>
      gateway_reference_saved_temporary continuation invocation identifier=Some pointer
    end
  |gateway_reference_cell object offset=>Mem.load AST.Mptr memory object offset=Some pointer
  |gateway_reference_global identifier=>exists object,
    Globalenvs.Genv.find_symbol ge identifier=Some object /\Mem.load AST.Mptr memory object 0=Some pointer
  |gateway_reference_argument invocation index=>match source with
    |Callstate _ arguments continuation _=>invocation=gateway_reference_depth continuation /\
      nth_error arguments index=Some pointer
    |_=>False end
  |gateway_reference_result invocation=>match source with
    |Returnstate value continuation _=>invocation=gateway_reference_depth continuation /\pointer=value
    |_=>False end
  end.

Definition gateway_reference_source_bound ge source ledger:Prop:=
  forall entry,In entry(gateway_reference_entries ledger)->
    gateway_reference_place_value ge source(gateway_reference_owner entry)(gateway_reference_pointer entry).

Lemma gateway_reference_result_binding ge value continuation memory:
  gateway_reference_place_value ge(Returnstate value continuation memory)
    (gateway_reference_result(gateway_reference_depth continuation))value.
Proof. split;reflexivity. Qed.

Lemma gateway_reference_temporary_binding ge function body continuation environment temporaries memory identifier pointer:
  temporaries!identifier=Some pointer->
  gateway_reference_place_value ge(State function body continuation environment temporaries memory)
    (gateway_reference_temporary(gateway_reference_depth continuation)identifier)pointer.
Proof.
  intro VALUE;unfold gateway_reference_place_value.
  destruct(Nat.eq_dec(gateway_reference_depth continuation)(gateway_reference_depth continuation));
    [exact VALUE|contradiction].
Qed.

Lemma gateway_reference_global_binding(ge:Clight.genv)source identifier object pointer:
  Globalenvs.Genv.find_symbol ge identifier=Some object->
  Mem.load AST.Mptr(match source with State _ _ _ _ _ m|Callstate _ _ _ m|Returnstate _ _ m=>m end)
    object 0=Some pointer->gateway_reference_place_value ge source(gateway_reference_global identifier)pointer.
Proof. intros SYMBOL VALUE;exists object;auto. Qed.
