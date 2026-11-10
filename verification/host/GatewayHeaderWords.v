(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual packet word stores use coupled runtime ownership. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps WriteBytes Writers WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayWordsMemory
  GatewayWords GatewayHeaderRuntime GatewayThreadRuntime GatewayFramedRuntime GatewayRuntimeTrace GatewayReadonly.
Import ListNotations.
Open Scope Z_scope.

Section HeaderWords.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.

Ltac gateway_header_same target :=
  let memory:=fresh "header_memory" in let world:=fresh "header_world" in let ready:=fresh "header_ready" in
  eapply gateway_runtime_same with(next:=target);
    [eapply gateway_header_stage_ambient;exact runtime
    |cbn;tauto|intros memory world ready;cbn[gateway_replace_memory]|].

Ltac gateway_header_route :=
  lazymatch goal with
  | |-gateway_runtime_path _ _ _ (State ?f(Ssequence ?a ?b)?k ?e ?le ?m)_ _=>
    gateway_header_same(State f a(Kseq b k)e le m);[apply unchanged_store_edge,edge_seq|]
  | |-gateway_runtime_path _ _ _ (State ?f Sskip(Kseq ?a ?k)?e ?le ?m)_ _=>
    gateway_header_same(State f a k e le m);[apply unchanged_store_edge,edge_skip_seq|]
  | |-gateway_runtime_path _ _ _ (State ?f(Sloop ?a ?b)?k ?e ?le ?m)_ _=>
    gateway_header_same(State f a(Kloop1 a b k)e le m);[apply unchanged_store_edge,edge_loop|]
  | |-gateway_runtime_path _ _ _ (State ?f Sskip(Kloop1 ?a ?b ?k)?e ?le ?m)_ _=>
    gateway_header_same(State f b(Kloop2 a b k)e le m);[apply unchanged_store_edge,edge_skip_loop1|]
  | |-gateway_runtime_path _ _ _ (State ?f Sskip(Kloop2 ?a ?b ?k)?e ?le ?m)_ _=>
    gateway_header_same(State f(Sloop a b)k e le m);[apply unchanged_store_edge,edge_skip_loop2|]
  | |-gateway_runtime_path _ _ _ (State ?f Sbreak(Kseq ?a ?k)?e ?le ?m)_ _=>
    gateway_header_same(State f Sbreak k e le m);[apply unchanged_store_edge,edge_break_seq|]
  | |-gateway_runtime_path _ _ _ (State ?f Sbreak(Kloop1 ?a ?b ?k)?e ?le ?m)_ _=>
    gateway_header_same(State f Sskip k e le m);[apply unchanged_store_edge,edge_break_loop1|]
  end.

Ltac gateway_header_set_as result :=
  lazymatch goal with
  | |-gateway_runtime_path _ _ _ (State ?f(Sset ?id ?expression)?k ?e ?le ?m)_ _=>
    gateway_header_same(State f Sskip k e(PTree.set id result le)m);
      [apply unchanged_store_edge;eapply edge_set;WriteAll.expression|]
  end.

Ltac gateway_header_set :=
  lazymatch goal with
  | |-gateway_runtime_path _ _ _ (State _ (Sset _ (Econst_int ?value _))_ _ _ _)_ _=>
    gateway_header_set_as(Vint value)
  | |-gateway_runtime_path _ _ _
      (State _ (Sset _ (Ebinop Oadd(Etempvar ?identifier _)(Econst_int ?delta _)_))_ _ ?le _)_ _=>
    let found:=eval vm_compute in(PTree.get identifier le)in
    lazymatch found with Some(Vint ?value)=>gateway_header_set_as(Vint(Int.add value delta))end
  end.

Ltac gateway_header_branch choice :=
  lazymatch goal with
  | |-gateway_runtime_path _ _ _ (State ?f(Sifthenelse ?test ?yes ?no)?k ?e ?le ?m)_ _=>
    gateway_header_same(State f(if choice then yes else no)k e le m);
      [apply unchanged_store_edge;eapply edge_if with(b:=choice);[WriteAll.expression|reflexivity]|]
  end.

Ltac gateway_header_assign value :=
  lazymatch goal with
  | |-gateway_runtime_path ?backend ?ge
      (gateway_header_stage ?native ?stable ?disc ?mode ?block ?held ?readonly ?original ?origin ?offset ?width ?written)
      (State ?f(Sassign(Ederef ?pointer tuchar)?expression)?k ?e ?le ?m)?returned ?post=>
    eapply gateway_runtime_next with(next:=State f Sskip k e le m)
      (middle:=gateway_header_stage native stable disc mode block held readonly original origin offset width(written++[value]));
    [eapply gateway_header_stage_ambient;exact runtime|cbn;tauto
    |intros available current READY;
     destruct(gateway_header_stage_store backend io native stable disc thread_errno runtime mode block held readonly original origin
       offset width written available current value ltac:(assumption) READY ltac:(cbn;lia)
       ltac:(unfold put32_byte,put64_byte;try rewrite Int.zero_ext_idem by lia;reflexivity))as[after[STORE POST]];
     exists after;split;[cbn[gateway_replace_memory]|exact POST];
     eapply byte_assignment;
       [WriteAll.expression|WriteAll.expression
       |cbn[typeof tuchar sem_cast classify_cast cast_int_int];rewrite Int.zero_ext_idem by lia;reflexivity
       |match goal with |-context[Ptrofs.mul ?a ?b]=>
          let idx:=eval vm_compute in(Ptrofs.unsigned(Ptrofs.mul a b))in
          change(Ptrofs.mul a b)with(Ptrofs.repr idx);
          eapply pointer_byte_store with(index:=idx);[lia|lia|]end;
        match goal with |-Mem.store Mint8unsigned ?memory0 ?block0 ?position _=Some ?after0=>
          replace position with(offset+Z.of_nat(length written))by reflexivity;exact STORE end]
    |]
  end.

Ltac gateway_header_iteration value :=
  gateway_header_route;gateway_header_route;gateway_header_branch true;gateway_header_route;
  gateway_header_assign value;gateway_header_route;gateway_header_set;gateway_header_route.

Ltac gateway_header_end :=
  gateway_header_route;gateway_header_route;gateway_header_branch false;gateway_header_route;gateway_header_route;
  lazymatch goal with
  | |-gateway_runtime_path _ _ _ (State ?f Sskip Kstop empty_env ?le ?m)_ _=>
    gateway_header_same(Returnstate Vundef Kstop m);[apply void_return_edge;exact I|]
  end;
  apply gateway_runtime_return;[eapply gateway_header_stage_ambient;exact runtime|];
  intros available current READY;exact READY.

Theorem gateway_put32_runtime_path mode block ofs value held readonly original origin memory :
  Ptrofs.unsigned ofs+4<=Ptrofs.modulus ->
  (forall position,Ptrofs.unsigned ofs<=position<Ptrofs.unsigned ofs+4->~readonly block position) ->
  gateway_runtime_path backend ge
    (gateway_header_stage native_private stable_readonly discipline mode block held readonly original origin(Ptrofs.unsigned ofs)4 [])
    (writer_initial f_host_put32 block ofs(Vint value)Kstop memory)Vundef
    (gateway_header_stage native_private stable_readonly discipline mode block held readonly original origin(Ptrofs.unsigned ofs)4
      (put32_values value)).
Proof.
  intros BOUND DISJOINT.
  gateway_header_same(State f_host_put32(fn_body f_host_put32)Kstop empty_env
    (PTree.set _value(Vint value)(PTree.set _p(Vptr block ofs)(create_undef_temps(fn_temps f_host_put32))))memory).
  { apply unchanged_store_edge,gateway_writer_entry;auto. }
  unfold f_host_put32;cbn[fn_body].
  gateway_header_route;gateway_header_set;gateway_header_route.
  gateway_header_iteration(put32_byte value 0).
  gateway_header_iteration(put32_byte value 1).
  gateway_header_iteration(put32_byte value 2).
  gateway_header_iteration(put32_byte value 3).
  gateway_header_end.
Qed.

Theorem gateway_put64_runtime_path mode block ofs value held readonly original origin memory :
  Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  (forall position,Ptrofs.unsigned ofs<=position<Ptrofs.unsigned ofs+8->~readonly block position) ->
  gateway_runtime_path backend ge
    (gateway_header_stage native_private stable_readonly discipline mode block held readonly original origin(Ptrofs.unsigned ofs)8 [])
    (writer_initial f_host_put64 block ofs(Vlong value)Kstop memory)Vundef
    (gateway_header_stage native_private stable_readonly discipline mode block held readonly original origin(Ptrofs.unsigned ofs)8
      (put64_values value)).
Proof.
  intros BOUND DISJOINT.
  gateway_header_same(State f_host_put64(fn_body f_host_put64)Kstop empty_env
    (PTree.set _value(Vlong value)(PTree.set _p(Vptr block ofs)(create_undef_temps(fn_temps f_host_put64))))memory).
  { apply unchanged_store_edge,gateway_writer_entry;auto. }
  unfold f_host_put64;cbn[fn_body].
  gateway_header_route;gateway_header_set;gateway_header_route.
  gateway_header_iteration(put64_byte value 0).
  gateway_header_iteration(put64_byte value 1).
  gateway_header_iteration(put64_byte value 2).
  gateway_header_iteration(put64_byte value 3).
  gateway_header_iteration(put64_byte value 4).
  gateway_header_iteration(put64_byte value 5).
  gateway_header_iteration(put64_byte value 6).
  gateway_header_iteration(put64_byte value 7).
  gateway_header_end.
Qed.

End HeaderWords.
