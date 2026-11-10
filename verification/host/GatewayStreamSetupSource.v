(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Stream initialization follows the actual source members and scalar values. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers Floats AST Values Memory Memdata Events Errors Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayPostSpawnSource GatewayHeaderInitialization GatewayStreamInterface GatewayStreamLayout
  GatewayStreamInitialization GatewayPrefix.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_initial_stream data_left control_left cli cancellation began:gateway_stream_values:=
  {|stream_descriptor:=Int.repr data_left;stream_control:=Int.repr control_left;stream_cancel_sent:=Int.zero;stream_cli:=cli;
    stream_cancellation:=cancellation;stream_remaining:=Int64.zero;stream_nodes:=Int64.repr 1048576;
    stream_deadline:=Float.add began(Float.of_bits(Int64.repr 4660794605770375168))|}.
Definition stream_setup_member index:=nth index
  [_descriptor;_control;_cancellation_sent;_cli;_cancellation;_remaining;_nodes;_deadline]_descriptor.
Definition stream_setup_type index:=nth index
  [tint;tint;tint;tint;tptr(Tstruct __9088 noattr);tulong;tulong;tdouble]tint.
Definition stream_setup_at index:=postspawn_at(5+index).
Definition stream_setup_assignment index:=match index with O|S O=>match stream_setup_at index with Ssequence _ rest=>rest|_=>Sskip end|
  _=>stream_setup_at index end.
Definition stream_setup_expression index:=match stream_setup_assignment index with Sassign _ expression=>expression|
  _=>Econst_int Int.zero tint end.
Definition stream_setup_temps data_left control_left index temporaries:=match index with O=>temporaries|
  S O=>PTree.set _t'74(Vint(Int.repr data_left))temporaries|
  _=>PTree.set _t'73(Vint(Int.repr control_left))(PTree.set _t'74(Vint(Int.repr data_left))temporaries)end.

Theorem actual_stream_setup_source index:
  (index<8)%nat->stream_setup_assignment index=Sassign
    (Efield(Evar _stream(Tstruct _host_stream noattr))(stream_setup_member index)(stream_setup_type index))
    (stream_setup_expression index).
Proof. intro BOUND;do 8(destruct index as[|index];[reflexivity|]);lia. Qed.
Theorem actual_stream_setup_header_tail:postspawn_after 13=header_source_start.
Proof. reflexivity. Qed.

Lemma stream_setup_member_layout stream index:
  (index<8)%nat->stream_member_layout(Clight.globalenv prog)(stream_setup_member index)
    (stream_initial_offset(stream_initial_cell stream index)).
Proof.
  intro BOUND;destruct actual_stream_layout as[A[B[C[D[E[F[G H]]]]]]].
  do 8(destruct index as[|index];[assumption|]);lia.
Qed.

Lemma stream_setup_location ge environment temporaries memory object index stream:
  environment!_stream=Some(object,Tstruct _host_stream noattr)->
  stream_member_layout ge(stream_setup_member index)(stream_initial_offset(stream_initial_cell stream index))->
  location_value ge environment temporaries memory
    (Efield(Evar _stream(Tstruct _host_stream noattr))(stream_setup_member index)(stream_setup_type index))object
    (Ptrofs.repr(stream_initial_offset(stream_initial_cell stream index))).
Proof.
  intros STREAM[composite[LAYOUT MEMBER]].
  rewrite<-(Ptrofs.add_zero_l(Ptrofs.repr(stream_initial_offset(stream_initial_cell stream index))))at 1.
  eapply struct_location_value with(id:=_host_stream)(co:=composite)(att:=noattr).
  - eapply location_read_value;[apply local_location_value;exact STREAM|apply deref_loc_copy;reflexivity].
  - reflexivity.
  - exact LAYOUT.
  - exact MEMBER.
Qed.

Definition stream_setup_raw_value values(index:nat):=match index with
  |5%nat=>Vint Int.zero|6%nat=>Vint(Int.repr 1048576)|_=>stream_initial_value(stream_initial_cell values index)end.

Lemma stream_setup_float_value ge environment temporaries memory value:
  expression_value ge environment temporaries memory(Econst_float value tdouble)(Vfloat value).
Proof.
  split;[constructor|]. intros other VALUE;inversion VALUE;subst;try reflexivity.
  match goal with LOAD:eval_lvalue _ _ _ _(Econst_float _ _)_ _ _|-_=>inversion LOAD end.
Qed.

Lemma stream_setup_expression_value ge environment temporaries memory data_left control_left cli cancellation began index:
  (index<8)%nat->((exists object offset,cancellation=Vptr object offset)\/(exists word,cancellation=Vlong word))->
  ((index=0)%nat->temporaries!_t'74=Some(Vint(Int.repr data_left)))->
  ((index=1)%nat->temporaries!_t'73=Some(Vint(Int.repr control_left)))->
  temporaries!_cli=Some(Vint cli)->temporaries!_cancellation=Some cancellation->temporaries!_began=Some(Vfloat began)->
  expression_value ge environment temporaries memory(stream_setup_expression index)
    (stream_setup_raw_value(gateway_initial_stream data_left control_left cli cancellation began)index) /\
  sem_cast(stream_setup_raw_value(gateway_initial_stream data_left control_left cli cancellation began)index)
    (typeof(stream_setup_expression index))(stream_setup_type index)memory=
    Some(stream_initial_value(stream_initial_cell(gateway_initial_stream data_left control_left cli cancellation began)index)).
Proof.
  intros BOUND POINTER DATA CONTROL CLI CANCELLATION BEGAN.
  destruct index as[|[|[|[|[|[|[|[|index]]]]]]]];try lia.
  all:split;try solve[apply old_expression_value;first[apply value_temp;first[assumption|apply DATA;reflexivity|apply CONTROL;reflexivity]|constructor]].
  all:try reflexivity.
  - destruct POINTER as[[object[offset POINTER]]|[word POINTER]];rewrite POINTER;reflexivity.
  - eapply binary_expression_value with(v:=Vfloat began)(w:=Vfloat(Float.of_bits(Int64.repr 4660794605770375168)));
      [apply old_expression_value,value_temp;exact BEGAN|apply stream_setup_float_value|reflexivity].
Qed.
