(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Container counts use the real four-byte word call after tag dispatch. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayValueEntry GatewayValueNull
  GatewayValueDispatch GatewayValueBoolean GatewayValueAfterBoolean GatewayValueExpressions GatewayScalarLength
  GatewayStreamWord GatewaySourceEvaluation GatewaySourcePaths GatewayFramedRuntime GatewayPrefix.
Import ListNotations.

Inductive gateway_container_case:=gateway_container_array|gateway_container_object.
Definition gateway_container_code container :Z:=
  match container with gateway_container_array=>7|gateway_container_object=>8 end.
Definition gateway_value_container_test:=match gateway_value_after_scalar with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_after_container:=match gateway_value_after_scalar with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_container_guard:=match gateway_value_container_test with Ssequence _ guard=>guard|_=>Sskip end.
Definition gateway_value_container_branch:=match gateway_value_container_guard with Sifthenelse _ first _=>first|_=>Sskip end.
Definition gateway_value_container_size_test:=match gateway_value_container_branch with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_container_after_size:=match gateway_value_container_branch with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_container_size_guard:=match gateway_value_container_size_test with Ssequence _ guard=>guard|_=>Sskip end.
Definition gateway_value_container_size_cont slots parameters:=
  Kcall(Some _t'27)f_host_value(gateway_value_environment slots)parameters
    (Kseq gateway_value_container_size_guard(Kseq gateway_value_container_after_size(Kseq gateway_value_after_container Kstop))).
Definition gateway_value_container_size_arguments slots arguments :gateway_word_arguments:={|
  word_stream:=gateway_value_stream arguments;word_width:=Int.repr 4;
  word_output:=Vptr(gateway_value_size_slot slots)Ptrofs.zero|}.

Ltac gateway_container_finish_length ge closed stream symbol symbol_binding function_binding arguments slots memory :=
  lazymatch goal with
  |-gateway_source_path _ _ ?definition ?values ?continuation _ _ _=>
    eapply gateway_source_same with(target:=Callstate definition values continuation memory)
  end;
    [exact closed|cbn;tauto|
      intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero);
        [reflexivity|
          apply old_expression_value;eapply value_function;[reflexivity|exact symbol_binding|reflexivity]|
          apply cons_argument_values with(v:=gateway_value_stream arguments);
            [gateway_source_expression ltac:(fail)|
              cbn[gateway_value_container_size_arguments word_stream];rewrite stream;reflexivity|
              eapply cons_argument_values;
                [gateway_source_expression ltac:(fail)|reflexivity|
                  apply cons_argument_values with(v:=Vptr(gateway_value_size_slot slots)Ptrofs.zero);
                    [apply local_address_expression;unfold gateway_value_environment;apply PTree.gss|
                      reflexivity|apply no_argument_values]]]|
          change(Genv.find_funct_ptr ge symbol=Some(Internal f_host_word));exact function_binding|reflexivity]|
      apply gateway_source_reached;auto].

Theorem gateway_container_length_owned_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:Memory.mem->World->Prop)container slots arguments initial memory symbol stream_block stream_offset :
  gateway_ambient_closed backend property ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  (forall memory world,property memory world->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr(gateway_container_code container)))) ->
  Genv.find_symbol ge _host_word=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_word) ->
  exists parameters,gateway_source_path backend ge(Internal f_host_word)
    (gateway_word_values(gateway_value_container_size_arguments slots arguments))
    (gateway_value_container_size_cont slots parameters)property
    (State f_host_value gateway_value_after_boolean Kstop(gateway_value_environment slots)
      (gateway_value_nonboolean_parameters arguments initial(Int64.repr(gateway_container_code container)))memory)property /\
    parameters!_stream=Some(gateway_value_stream arguments) /\parameters!_depth=Some(Vint(gateway_value_depth arguments)).
Proof.
  intros CLOSED STREAM LOADED SYMBOL FUNCTION;destruct container;eexists.
  all:split;
    [gateway_source_to_call CLOSED ltac:(apply gateway_value_tag_expression;eapply LOADED;eassumption);
      gateway_container_finish_length ge CLOSED STREAM symbol SYMBOL FUNCTION arguments slots memory|
      split;reflexivity].
Qed.
