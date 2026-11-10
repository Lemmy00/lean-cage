(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual integer loop guards and source advances delimit each
   bounded chunk, retaining all operand temporaries and the same native memory. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumber GatewayNumberIntegerStructure GatewayNumberIntegerCalls
  GatewayNumberConstruction GatewaySourcePaths GatewaySourceSegments GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayUnaryExpressions
  GatewayValueReturns GatewayFramedRuntime GatewayIntegerScan GatewayJsonNumberSource.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_number_integer_loop_enter {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters index size memory:
  gateway_ambient_closed backend property->0<=index<size->size<=65536->
  parameters!_index=Some(Vlong(Int64.repr index))->parameters!_size=Some(Vlong(Int64.repr size))->
  gateway_source_segment backend ge property
    (State f_host_json_number number_integer_loop number_integer_loop_cont empty_env parameters memory)
    (State f_host_json_number gateway_number_chunk_loop number_integer_chunk_cont empty_env
      (PTree.set _offset(Vlong Int64.zero)(PTree.set _chunk(Vlong Int64.zero)parameters))memory)property.
Proof.
  intros CLOSED INDEX SIZE POSITION LIMIT.
  eapply gateway_segment_same with(next:=State f_host_json_number number_integer_loop_body number_integer_work_cont empty_env parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  eapply gateway_segment_same with(next:=State f_host_json_number(json_number_first number_integer_loop_body)
    (Kseq number_integer_work number_integer_work_cont)empty_env parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_segment_same with(next:=State f_host_json_number Sskip(Kseq number_integer_work number_integer_work_cont)empty_env parameters memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(v:=Vint Int.one)(b:=true).
    + eapply binary_expression_value;[apply old_expression_value,value_temp;exact POSITION|apply old_expression_value,value_temp;exact LIMIT|].
      change(Some(Val.of_bool(Int64.ltu(Int64.repr index)(Int64.repr size)))=Some(Vint Int.one)).
      unfold Int64.ltu;rewrite!Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
      rewrite zlt_true by lia;reflexivity.
    + reflexivity.
  - gateway_segment_dynamic CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
Qed.

Theorem gateway_number_integer_loop_exit {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters size memory:
  gateway_ambient_closed backend property->parameters!_index=Some(Vlong size)->parameters!_size=Some(Vlong size)->
  gateway_source_segment backend ge property
    (State f_host_json_number number_integer_loop number_integer_loop_cont empty_env parameters memory)
    (State f_host_json_number Sskip number_integer_loop_cont empty_env parameters memory)property.
Proof.
  intros CLOSED POSITION LIMIT.
  eapply gateway_segment_same with(next:=State f_host_json_number number_integer_loop_body number_integer_work_cont empty_env parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  eapply gateway_segment_same with(next:=State f_host_json_number(json_number_first number_integer_loop_body)
    (Kseq number_integer_work number_integer_work_cont)empty_env parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_segment_same with(next:=State f_host_json_number Sbreak(Kseq number_integer_work number_integer_work_cont)empty_env parameters memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + eapply binary_expression_value;[apply old_expression_value,value_temp;exact POSITION|apply old_expression_value,value_temp;exact LIMIT|].
      change(Some(Val.of_bool(Int64.ltu size size))=Some(Vint Int.zero));unfold Int64.ltu;rewrite zlt_false by lia;reflexivity.
    + reflexivity.
  - eapply gateway_segment_same with(next:=State f_host_json_number Sbreak number_integer_work_cont empty_env parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_break_seq|].
    eapply gateway_segment_same with(next:=State f_host_json_number Sskip number_integer_loop_cont empty_env parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_break_loop1|apply gateway_segment_here].
Qed.

Theorem gateway_number_chunk_part_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters chunk memory symbol definition:
  gateway_ambient_closed backend property->parameters!_chunk=Some(Vlong chunk)->
  Genv.find_symbol ge _PyLong_FromUnsignedLong=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tulong](tptr(Tstruct __object noattr))cc_default->
  gateway_source_path backend ge definition[Vlong chunk](number_integer_part_cont parameters)property
    (State f_host_json_number Sskip number_integer_chunk_cont empty_env parameters memory)property.
Proof.
  intros CLOSED CHUNK SYMBOL FUNCTION TYPE.
  change number_integer_chunk_cont with(Kseq number_integer_after_chunk number_integer_work_cont).
  gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
  number_sdk_reached CLOSED symbol _PyLong_FromUnsignedLong SYMBOL FUNCTION TYPE
    ltac:(fun _=>apply cons_argument_values with(v:=Vlong chunk);
      [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values]).
Qed.

Theorem gateway_number_integer_advance_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters value offset index width ignored memory:
  gateway_ambient_closed backend property->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory value(Ptrofs.unsigned offset)=true)->
  parameters!_value__1=Some(Vptr value offset)->parameters!_index=Some(Vlong(Int64.repr index))->
  parameters!_width=Some(Vlong(Int64.repr width))->
  gateway_source_segment backend ge property
    (Returnstate ignored(number_integer_release_part_cont parameters)memory)
    (State f_host_json_number number_integer_loop number_integer_loop_cont empty_env
      (PTree.set _width(Vlong(Int64.repr 9))(PTree.set _index(Vlong(Int64.repr(index+width)))parameters))memory)property.
Proof.
  intros CLOSED VALID VALUE POSITION WIDTH.
  set(advanced:=PTree.set _width(Vlong(Int64.repr 9))(PTree.set _index(Vlong(Int64.repr(index+width)))parameters)).
  assert(PREFIX:gateway_source_segment backend ge property
    (Returnstate ignored(number_integer_release_part_cont parameters)memory)
    (State f_host_json_number Sskip number_integer_work_cont empty_env advanced memory)property).
  { gateway_segment_dynamic CLOSED ltac:(fun _=>number_nonnull_expression property value offset VALID)
      ltac:(fun _=>first[apply gateway_number_long_add|reflexivity]). }
  eapply gateway_integer_segments_append;[exact PREFIX|].
  eapply gateway_segment_same with(next:=State f_host_json_number Sskip
    (Kloop2 number_integer_loop_body Sskip number_integer_loop_cont)empty_env advanced memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop1|].
  eapply gateway_segment_same with(next:=State f_host_json_number number_integer_loop number_integer_loop_cont empty_env advanced memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|apply gateway_segment_here].
Qed.
