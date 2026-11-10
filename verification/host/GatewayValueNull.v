(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A zero tag reaches the actual singleton reference call and returns its source address. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayPure GatewayValueEntry GatewayValueTag
  GatewayObjectAddresses GatewaySourcePaths GatewayFramedRuntime GatewayReturns.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_value_null_test:=match gateway_value_after_tag with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_after_null:=match gateway_value_after_tag with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_null_load:=match gateway_value_null_test with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_null_guard:=match gateway_value_null_test with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_null_branch:=match gateway_value_null_guard with Sifthenelse _ first _=>first|_=>Sskip end.
Definition gateway_value_none_call:=match gateway_value_null_branch with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_none_return:=match gateway_value_null_branch with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_none_expression:=Eaddrof(Evar __Py_NoneStruct(Tstruct __object noattr))(tptr(Tstruct __object noattr)).
Definition gateway_value_after_word_parameters arguments initial:=
  PTree.set _t'2(Vint Int.zero)(gateway_value_debited_parameters arguments initial).
Definition gateway_value_none_parameters arguments initial:=
  PTree.set _t'93(Vlong Int64.zero)(gateway_value_after_word_parameters arguments initial).
Definition gateway_value_none_cont slots arguments initial:=
  Kcall None f_host_value(gateway_value_environment slots)(gateway_value_none_parameters arguments initial)
    (Kseq gateway_value_none_return(Kseq gateway_value_after_null Kstop)).

Theorem gateway_value_zero_tag_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots arguments initial memory none_symbol reference_symbol definition :
  gateway_ambient_closed backend property ->
  (forall memory world,property memory world->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong Int64.zero)) ->
  Genv.find_symbol ge __Py_NoneStruct=Some none_symbol ->Genv.find_symbol ge _Py_IncRef=Some reference_symbol ->
  Genv.find_funct_ptr ge reference_symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default ->
  gateway_source_path backend ge definition[Vptr none_symbol Ptrofs.zero](gateway_value_none_cont slots arguments initial)
    property(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)memory)property.
Proof.
  intros CLOSED LOADED NONE_SYMBOL REFERENCE_SYMBOL FUNCTION TYPE.
  eapply gateway_source_same with(target:=State f_host_value Sskip
    (Kseq gateway_value_tag_guard(Kseq gateway_value_after_tag Kstop))(gateway_value_environment slots)
    (gateway_value_after_word_parameters arguments initial)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_source_same with(target:=State f_host_value gateway_value_tag_guard
    (Kseq gateway_value_after_tag Kstop)(gateway_value_environment slots)
    (gateway_value_after_word_parameters arguments initial)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_value Sskip(Kseq gateway_value_after_tag Kstop)
    (gateway_value_environment slots)(gateway_value_after_word_parameters arguments initial)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(b:=false);[apply old_expression_value,value_temp;apply PTree.gss|reflexivity].
  - eapply gateway_source_same with(target:=State f_host_value gateway_value_after_tag Kstop
      (gateway_value_environment slots)(gateway_value_after_word_parameters arguments initial)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    change gateway_value_after_tag with(Ssequence gateway_value_null_test gateway_value_after_null).
    eapply gateway_source_same with(target:=State f_host_value gateway_value_null_test(Kseq gateway_value_after_null Kstop)
      (gateway_value_environment slots)(gateway_value_after_word_parameters arguments initial)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    change gateway_value_null_test with(Ssequence gateway_value_null_load gateway_value_null_guard).
    eapply gateway_source_same with(target:=State f_host_value gateway_value_null_load
      (Kseq gateway_value_null_guard(Kseq gateway_value_after_null Kstop))
      (gateway_value_environment slots)(gateway_value_after_word_parameters arguments initial)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_source_same with(target:=State f_host_value Sskip
      (Kseq gateway_value_null_guard(Kseq gateway_value_after_null Kstop))
      (gateway_value_environment slots)(gateway_value_none_parameters arguments initial)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros current world GOOD;apply certified_set_edge.
      apply location_read_value with(b:=gateway_value_tag_slot slots)(ofs:=Ptrofs.zero).
      * apply local_location_value;unfold gateway_value_environment;rewrite PTree.gso by discriminate;apply PTree.gss.
      * apply deref_loc_value with(chunk:=Mint64);[reflexivity|apply LOADED with(world:=world);exact GOOD].
    + eapply gateway_source_same with(target:=State f_host_value gateway_value_null_guard
        (Kseq gateway_value_after_null Kstop)(gateway_value_environment slots)(gateway_value_none_parameters arguments initial)memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
      eapply gateway_source_same with(target:=State f_host_value gateway_value_null_branch
        (Kseq gateway_value_after_null Kstop)(gateway_value_environment slots)(gateway_value_none_parameters arguments initial)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros;eapply certified_if_edge with(b:=true).
        -- apply old_expression_value;eapply value_unary;[apply value_temp;apply PTree.gss|reflexivity].
        -- reflexivity.
      * change gateway_value_null_branch with(Ssequence gateway_value_none_call gateway_value_none_return).
        eapply gateway_source_same with(target:=State f_host_value gateway_value_none_call
          (Kseq gateway_value_none_return(Kseq gateway_value_after_null Kstop))
          (gateway_value_environment slots)(gateway_value_none_parameters arguments initial)memory);
          [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
        eapply gateway_source_same with(target:=Callstate definition[Vptr none_symbol Ptrofs.zero]
          (gateway_value_none_cont slots arguments initial)memory).
        -- exact CLOSED.
        -- cbn;tauto.
        -- intros;eapply certified_call_edge with(vf:=Vptr reference_symbol Ptrofs.zero).
           ++ reflexivity.
           ++ apply old_expression_value;eapply value_function;[reflexivity|exact REFERENCE_SYMBOL|reflexivity].
           ++ apply cons_argument_values with(v:=Vptr none_symbol Ptrofs.zero).
              ** apply gateway_global_address_expression;[reflexivity|exact NONE_SYMBOL].
              ** reflexivity.
              ** apply no_argument_values.
           ++ change(Genv.find_funct_ptr ge reference_symbol=Some definition);exact FUNCTION.
           ++ exact TYPE.
        -- apply gateway_source_reached;auto.
Qed.

Lemma gateway_value_none_return_path(ge:Clight.genv)slots arguments initial memory returned none_symbol :
  Genv.find_symbol ge __Py_NoneStruct=Some none_symbol ->
  gateway_constant_path ge(Vptr none_symbol Ptrofs.zero)
    (Returnstate returned(gateway_value_none_cont slots arguments initial)memory).
Proof.
  intro SYMBOL.
  eapply gateway_constant_next with(next:=State f_host_value Sskip
    (Kseq gateway_value_none_return(Kseq gateway_value_after_null Kstop))(gateway_value_environment slots)
    (gateway_value_none_parameters arguments initial)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_constant_next with(next:=State f_host_value gateway_value_none_return
    (Kseq gateway_value_after_null Kstop)(gateway_value_environment slots)(gateway_value_none_parameters arguments initial)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_constant_at_return with(value:=Vptr none_symbol Ptrofs.zero).
  - reflexivity.
  - intros;apply gateway_global_address_expression;[reflexivity|exact SYMBOL].
  - intros;reflexivity.
Qed.

Theorem gateway_value_none_returned {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)slots arguments initial
    before world events returned value after next none_symbol :
  Genv.find_symbol ge __Py_NoneStruct=Some none_symbol ->
  gateway_steps backend ge(gateway_live(Returnstate returned(gateway_value_none_cont slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->value=Vptr none_symbol Ptrofs.zero.
Proof. intros SYMBOL RUN;eapply gateway_constant_path_actual;[apply gateway_value_none_return_path;exact SYMBOL|exact RUN]. Qed.
