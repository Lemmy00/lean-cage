(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual native word loops preserve their exact owned byte regions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps WriteBytes Writers WriteAll.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayFrames GatewayWordsMemory GatewayWordData GatewayWordsMath GatewayWordFamily.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Lemma gateway_writer_entry : forall ge f b ofs x k m,
  f = f_host_put32 \/ f = f_host_put64 ->
  edge ge (writer_initial f b ofs x k m)
    (State f (fn_body f) k empty_env
      (PTree.set _value x (PTree.set _p (Vptr b ofs) (create_undef_temps (fn_temps f)))) m).
Proof.
  intros ge f b ofs x k m WRITER. destruct WRITER; subst f;
    split; [exact I| |exact I|]; split.
  1,3: apply step_internal_function; constructor;
    [constructor|repeat constructor; simpl; intuition discriminate|
     unfold list_disjoint, var_names; simpl; intros a c [A|[A|A]] [C|C];
       try contradiction; subst; discriminate|constructor|reflexivity].
  all: split; [reflexivity|]; intros t other STEP; inversion STEP; subst;
    match goal with H : function_entry2 _ _ _ _ _ _ _ |- _ => inversion H; subst end;
    match goal with H : alloc_variables _ _ _ _ _ _ |- _ => inversion H; subst end;
    match goal with H : bind_parameter_temps _ _ _ = _ |- _ => cbn in H; inversion H; subst end;
    auto.
Qed.

Theorem gateway_put32_source_path : forall ge m b ofs x k final,
  is_call_cont k -> Ptrofs.unsigned ofs + 4 <= Ptrofs.modulus ->
  byte_writes m b (Ptrofs.unsigned ofs) (put32_values x) final ->
  store_path ge (writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x))
    (writer_initial f_host_put32 b ofs (Vint x) k m) 42 (Returnstate Vundef k final).
Proof.
  intros ge m b ofs x k final K BOUND WRITES.
  assert (P0 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) m)
    by apply writer_prefix_initial.
  unfold put32_values in WRITES; simpl map in WRITES.
  inversion WRITES as [|? ? ? ? ? m1 ? S1 T1]; subst. clear WRITES.
  inversion T1 as [|? ? ? ? ? m2 ? S2 T2]; subst. clear T1.
  inversion T2 as [|? ? ? ? ? m3 ? S3 T3]; subst. clear T2.
  inversion T3 as [|? ? ? ? ? m4 ? S4 T4]; subst. clear T3.
  inversion T4; subst. clear T4.
  assert (P1 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) m1).
  { exists [put32_byte x 0], [put32_byte x 1; put32_byte x 2; put32_byte x 3]. split; [reflexivity|].
    econstructor; [eassumption|]. constructor. }
  assert (P2 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) m2).
  { exists [put32_byte x 0; put32_byte x 1], [put32_byte x 2; put32_byte x 3]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P3 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) m3).
  { exists [put32_byte x 0; put32_byte x 1; put32_byte x 2], [put32_byte x 3]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P4 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) final).
  { exists [put32_byte x 0; put32_byte x 1; put32_byte x 2; put32_byte x 3], []. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  store_unchanged; [apply gateway_writer_entry; auto|].
  unfold f_host_put32; simpl fn_body. route_store; set_store; route_store.
  do 4 writer_iteration. writer_end.
Qed.

Theorem gateway_put64_source_path : forall ge m b ofs x k final,
  is_call_cont k -> Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus ->
  byte_writes m b (Ptrofs.unsigned ofs) (put64_values x) final ->
  store_path ge (writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x))
    (writer_initial f_host_put64 b ofs (Vlong x) k m) 74 (Returnstate Vundef k final).
Proof.
  intros ge m b ofs x k final K BOUND WRITES.
  assert (P0 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m)
    by apply writer_prefix_initial.
  unfold put64_values in WRITES; simpl map in WRITES.
  inversion WRITES as [|? ? ? ? ? m1 ? S1 T1]; subst. clear WRITES.
  inversion T1 as [|? ? ? ? ? m2 ? S2 T2]; subst. clear T1.
  inversion T2 as [|? ? ? ? ? m3 ? S3 T3]; subst. clear T2.
  inversion T3 as [|? ? ? ? ? m4 ? S4 T4]; subst. clear T3.
  inversion T4 as [|? ? ? ? ? m5 ? S5 T5]; subst. clear T4.
  inversion T5 as [|? ? ? ? ? m6 ? S6 T6]; subst. clear T5.
  inversion T6 as [|? ? ? ? ? m7 ? S7 T7]; subst. clear T6.
  inversion T7 as [|? ? ? ? ? m8 ? S8 T8]; subst. clear T7.
  inversion T8; subst. clear T8.
  assert (P1 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m1).
  { exists [put64_byte x 0], [put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. constructor. }
  assert (P2 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m2).
  { exists [put64_byte x 0; put64_byte x 1], [put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P3 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m3).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2], [put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P4 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m4).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3], [put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P5 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m5).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4], [put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P6 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m6).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5], [put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P7 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m7).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6], [put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P8 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) final).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7], []. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  store_unchanged; [apply gateway_writer_entry; auto|].
  unfold f_host_put64; simpl fn_body. route_store; set_store; route_store.
  do 8 writer_iteration. writer_end.
Qed.

Ltac gateway_same target :=
  let memory:=fresh "frame_memory" in let ready:=fresh "frame_ready" in
  eapply gateway_framed_same with(next:=target);
    [first[apply gateway_family_closed|apply gateway_bytes_ready_closed|apply gateway_read_ready_closed;assumption]
    |cbn;tauto|intros memory ready;cbn[gateway_replace_memory]|].

Ltac gateway_route :=
  lazymatch goal with
  | |-gateway_framed_path _ _ _ (State ?f(Ssequence ?a ?b)?k ?e ?le ?m)_ _=>
    gateway_same(State f a(Kseq b k)e le m);[apply unchanged_store_edge,edge_seq|]
  | |-gateway_framed_path _ _ _ (State ?f Sskip(Kseq ?a ?k)?e ?le ?m)_ _=>
    gateway_same(State f a k e le m);[apply unchanged_store_edge,edge_skip_seq|]
  | |-gateway_framed_path _ _ _ (State ?f(Sloop ?a ?b)?k ?e ?le ?m)_ _=>
    gateway_same(State f a(Kloop1 a b k)e le m);[apply unchanged_store_edge,edge_loop|]
  | |-gateway_framed_path _ _ _ (State ?f Sskip(Kloop1 ?a ?b ?k)?e ?le ?m)_ _=>
    gateway_same(State f b(Kloop2 a b k)e le m);[apply unchanged_store_edge,edge_skip_loop1|]
  | |-gateway_framed_path _ _ _ (State ?f Sskip(Kloop2 ?a ?b ?k)?e ?le ?m)_ _=>
    gateway_same(State f(Sloop a b)k e le m);[apply unchanged_store_edge,edge_skip_loop2|]
  | |-gateway_framed_path _ _ _ (State ?f Sbreak(Kseq ?a ?k)?e ?le ?m)_ _=>
    gateway_same(State f Sbreak k e le m);[apply unchanged_store_edge,edge_break_seq|]
  | |-gateway_framed_path _ _ _ (State ?f Sbreak(Kloop1 ?a ?b ?k)?e ?le ?m)_ _=>
    gateway_same(State f Sskip k e le m);[apply unchanged_store_edge,edge_break_loop1|]
  end.

Ltac gateway_set_as result :=
  lazymatch goal with
  | |-gateway_framed_path _ _ _ (State ?f(Sset ?id ?expression)?k ?e ?le ?m)_ _=>
    gateway_same(State f Sskip k e(PTree.set id result le)m);
      [apply unchanged_store_edge;eapply edge_set;WriteAll.expression|]
  end.

Ltac gateway_set :=
  lazymatch goal with
  | |-gateway_framed_path _ _ _ (State _ (Sset _ (Econst_int ?value _))_ _ _ _)_ _=>
    gateway_set_as(Vint value)
  | |-gateway_framed_path _ _ _
      (State _ (Sset _ (Ebinop Oadd(Etempvar ?identifier _)(Econst_int ?delta _)_))_ _ ?le _)_ _=>
    let found:=eval vm_compute in(PTree.get identifier le)in
    lazymatch found with Some(Vint ?value)=>gateway_set_as(Vint(Int.add value delta))end
  end.

Ltac gateway_branch choice :=
  lazymatch goal with
  | |-gateway_framed_path _ _ _ (State ?f(Sifthenelse ?test ?yes ?no)?k ?e ?le ?m)_ _=>
    gateway_same(State f(if choice then yes else no)k e le m);
      [apply unchanged_store_edge;eapply edge_if with(b:=choice);[WriteAll.expression|reflexivity]|]
  end.

Ltac gateway_assign value :=
  lazymatch goal with
  | |-gateway_framed_path ?ge ?protected (gateway_family_ready ?family ?written)
      (State ?f(Sassign(Ederef ?pointer tuchar)?expression)?k ?e ?le ?m)?returned ?post=>
    lazymatch type of family with gateway_write_family ?block ?offset ?width _=>
    eapply gateway_framed_next with(next:=State f Sskip k e le m)
      (middle:=gateway_family_ready family(written++[value]));
      [apply gateway_family_closed|cbn;tauto
      |intros memory READY;
       destruct(gateway_family_store family written memory value READY ltac:(cbn;lia)
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
    end
  end.

Ltac gateway_writer_iteration value :=
  gateway_route;gateway_route;gateway_branch true;gateway_route;gateway_assign value;
  gateway_route;gateway_set;gateway_route.

Ltac gateway_writer_end :=
  gateway_route;gateway_route;gateway_branch false;gateway_route;gateway_route;
  lazymatch goal with
  | |-gateway_framed_path _ _ _ (State ?f Sskip Kstop empty_env ?le ?m)_ _=>
    gateway_same(Returnstate Vundef Kstop m);[apply void_return_edge;exact I|]
  end;
  apply gateway_framed_return;[apply gateway_family_closed|];
  intros memory READY;exact READY.

(* §FS-host-boundary.caller: The writer invariant is built from source, not supplied as a callee result. *)
Theorem gateway_put32_family ge b ofs x m protected
    (family:gateway_write_family b(Ptrofs.unsigned ofs)4 protected) :
  Ptrofs.unsigned ofs+4<=Ptrofs.modulus ->
  gateway_framed_path ge protected(gateway_family_ready family [])
    (writer_initial f_host_put32 b ofs(Vint x)Kstop m)Vundef
    (gateway_family_ready family(put32_values x)).
Proof.
  intro BOUND.
  gateway_same(State f_host_put32(fn_body f_host_put32)Kstop empty_env
    (PTree.set _value(Vint x)(PTree.set _p(Vptr b ofs)(create_undef_temps(fn_temps f_host_put32))))m).
  { apply unchanged_store_edge,gateway_writer_entry;auto. }
  unfold f_host_put32;cbn[fn_body].
  gateway_route;gateway_set;gateway_route.
  gateway_writer_iteration(put32_byte x 0).
  gateway_writer_iteration(put32_byte x 1).
  gateway_writer_iteration(put32_byte x 2).
  gateway_writer_iteration(put32_byte x 3).
  gateway_writer_end.
Qed.

Theorem gateway_put64_family ge b ofs x m protected
    (family:gateway_write_family b(Ptrofs.unsigned ofs)8 protected) :
  Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  gateway_framed_path ge protected(gateway_family_ready family [])
    (writer_initial f_host_put64 b ofs(Vlong x)Kstop m)Vundef
    (gateway_family_ready family(put64_values x)).
Proof.
  intro BOUND.
  gateway_same(State f_host_put64(fn_body f_host_put64)Kstop empty_env
    (PTree.set _value(Vlong x)(PTree.set _p(Vptr b ofs)(create_undef_temps(fn_temps f_host_put64))))m).
  { apply unchanged_store_edge,gateway_writer_entry;auto. }
  unfold f_host_put64;cbn[fn_body].
  gateway_route;gateway_set;gateway_route.
  gateway_writer_iteration(put64_byte x 0).
  gateway_writer_iteration(put64_byte x 1).
  gateway_writer_iteration(put64_byte x 2).
  gateway_writer_iteration(put64_byte x 3).
  gateway_writer_iteration(put64_byte x 4).
  gateway_writer_iteration(put64_byte x 5).
  gateway_writer_iteration(put64_byte x 6).
  gateway_writer_iteration(put64_byte x 7).
  gateway_writer_end.
Qed.

Theorem gateway_put32_framed ge b ofs x m :
  Ptrofs.unsigned ofs+4<=Ptrofs.modulus ->
  gateway_framed_path ge(gateway_byte_region b(Ptrofs.unsigned ofs)4)
    (gateway_bytes_ready b(Ptrofs.unsigned ofs)4 [])
    (writer_initial f_host_put32 b ofs(Vint x)Kstop m)Vundef
    (fun after=>Mem.loadbytes after b(Ptrofs.unsigned ofs)4=Some(map byte_encoding(put32_values x))).
Proof.
  intro BOUND.
  eapply gateway_framed_post.
  - exact(gateway_put32_family ge b ofs x m _(gateway_simple_family b(Ptrofs.unsigned ofs)4)BOUND).
  - intros after READY;exact(gateway_bytes_complete b(Ptrofs.unsigned ofs)4(put32_values x)after READY ltac:(reflexivity)).
Qed.

Theorem gateway_put64_framed ge b ofs x m :
  Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  gateway_framed_path ge(gateway_byte_region b(Ptrofs.unsigned ofs)8)
    (gateway_bytes_ready b(Ptrofs.unsigned ofs)8 [])
    (writer_initial f_host_put64 b ofs(Vlong x)Kstop m)Vundef
    (fun after=>Mem.loadbytes after b(Ptrofs.unsigned ofs)8=Some(map byte_encoding(put64_values x))).
Proof.
  intro BOUND.
  eapply gateway_framed_post.
  - exact(gateway_put64_family ge b ofs x m _(gateway_simple_family b(Ptrofs.unsigned ofs)8)BOUND).
  - intros after READY;exact(gateway_bytes_complete b(Ptrofs.unsigned ofs)8(put64_values x)after READY ltac:(reflexivity)).
Qed.

(* §FS-host-boundary.caller: Ambient effects outside the owned word remain in the actual execution. *)
Theorem gateway_put32_actual {World Event}(backend:gateway_backend World Event)ge active
    b ofs value before world events returned after final_world :
  gateway_private_contract backend(gateway_byte_region b(Ptrofs.unsigned ofs)4)active ->
  active world -> Ptrofs.unsigned ofs+4<=Ptrofs.modulus ->
  Mem.range_perm before b(Ptrofs.unsigned ofs)(Ptrofs.unsigned ofs+4)Cur Writable ->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put32 b ofs(Vint value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  returned=Vundef /\
  Mem.loadbytes after b(Ptrofs.unsigned ofs)4=Some(map byte_encoding(put32_values value)) /\
  active final_world.
Proof.
  intros LAW ACTIVE BOUND OWN RUN.
  eapply(gateway_framed_return_exact backend ge(gateway_byte_region b(Ptrofs.unsigned ofs)4)active LAW
    (gateway_bytes_ready b(Ptrofs.unsigned ofs)4 [])
    (writer_initial f_host_put32 b ofs(Vint value)Kstop before)Vundef
    (fun memory=>Mem.loadbytes memory b(Ptrofs.unsigned ofs)4=Some(map byte_encoding(put32_values value)))
    before world events returned after final_world).
  - exact ACTIVE.
  - apply gateway_bytes_initial;exact OWN.
  - apply gateway_put32_framed;exact BOUND.
  - exact RUN.
Qed.

Theorem gateway_put64_actual {World Event}(backend:gateway_backend World Event)ge active
    b ofs value before world events returned after final_world :
  gateway_private_contract backend(gateway_byte_region b(Ptrofs.unsigned ofs)8)active ->
  active world -> Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  Mem.range_perm before b(Ptrofs.unsigned ofs)(Ptrofs.unsigned ofs+8)Cur Writable ->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put64 b ofs(Vlong value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  returned=Vundef /\
  Mem.loadbytes after b(Ptrofs.unsigned ofs)8=Some(map byte_encoding(put64_values value)) /\
  active final_world.
Proof.
  intros LAW ACTIVE BOUND OWN RUN.
  eapply(gateway_framed_return_exact backend ge(gateway_byte_region b(Ptrofs.unsigned ofs)8)active LAW
    (gateway_bytes_ready b(Ptrofs.unsigned ofs)8 [])
    (writer_initial f_host_put64 b ofs(Vlong value)Kstop before)Vundef
    (fun memory=>Mem.loadbytes memory b(Ptrofs.unsigned ofs)8=Some(map byte_encoding(put64_values value)))
    before world events returned after final_world).
  - exact ACTIVE.
  - apply gateway_bytes_initial;exact OWN.
  - apply gateway_put64_framed;exact BOUND.
  - exact RUN.
Qed.


(* §FS-host-boundary.caller: Later word writes preserve the earlier disjoint header fields. *)
Theorem gateway_put32_actual_readonly {World Event}(backend:gateway_backend World Event)ge active
    b ofs value read_only before world events returned after final_world :
  gateway_private_contract backend
    (gateway_join_region(gateway_byte_region b(Ptrofs.unsigned ofs)4)read_only)active ->
  active world -> Ptrofs.unsigned ofs+4<=Ptrofs.modulus ->
  gateway_disjoint_readonly b(Ptrofs.unsigned ofs)4 read_only ->
  Mem.range_perm before b(Ptrofs.unsigned ofs)(Ptrofs.unsigned ofs+4)Cur Writable ->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put32 b ofs(Vint value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  returned=Vundef /\
    Mem.loadbytes after b(Ptrofs.unsigned ofs)4=Some(map byte_encoding(put32_values value)) /\
    Mem.unchanged_on read_only before after /\ active final_world.
Proof.
  intros LAW ACTIVE BOUND DISJOINT OWN RUN.
  set(family:=gateway_readonly_family b(Ptrofs.unsigned ofs)4 read_only before DISJOINT).
  pose proof(gateway_framed_return_exact backend ge
    (gateway_join_region(gateway_byte_region b(Ptrofs.unsigned ofs)4)read_only)active LAW
    (gateway_family_ready family [])(writer_initial f_host_put32 b ofs(Vint value)Kstop before)
    Vundef(gateway_family_ready family(put32_values value))before world events returned after final_world
    ACTIVE(gateway_extended_initial b(Ptrofs.unsigned ofs)4 read_only before OWN)
    (gateway_put32_family ge b ofs value before _ family BOUND)RUN)as[VALUE[[READY FRAME]NEXT]].
  split;[exact VALUE|]. split.
  - exact(gateway_bytes_complete b(Ptrofs.unsigned ofs)4(put32_values value)after READY ltac:(reflexivity)).
  - exact(conj FRAME NEXT).
Qed.

(* §FS-host-boundary.caller: Later word writes preserve the earlier disjoint header fields. *)
Theorem gateway_put64_actual_readonly {World Event}(backend:gateway_backend World Event)ge active
    b ofs value read_only before world events returned after final_world :
  gateway_private_contract backend
    (gateway_join_region(gateway_byte_region b(Ptrofs.unsigned ofs)8)read_only)active ->
  active world -> Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  gateway_disjoint_readonly b(Ptrofs.unsigned ofs)8 read_only ->
  Mem.range_perm before b(Ptrofs.unsigned ofs)(Ptrofs.unsigned ofs+8)Cur Writable ->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put64 b ofs(Vlong value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  returned=Vundef /\
    Mem.loadbytes after b(Ptrofs.unsigned ofs)8=Some(map byte_encoding(put64_values value)) /\
    Mem.unchanged_on read_only before after /\ active final_world.
Proof.
  intros LAW ACTIVE BOUND DISJOINT OWN RUN.
  set(family:=gateway_readonly_family b(Ptrofs.unsigned ofs)8 read_only before DISJOINT).
  pose proof(gateway_framed_return_exact backend ge
    (gateway_join_region(gateway_byte_region b(Ptrofs.unsigned ofs)8)read_only)active LAW
    (gateway_family_ready family [])(writer_initial f_host_put64 b ofs(Vlong value)Kstop before)
    Vundef(gateway_family_ready family(put64_values value))before world events returned after final_world
    ACTIVE(gateway_extended_initial b(Ptrofs.unsigned ofs)8 read_only before OWN)
    (gateway_put64_family ge b ofs value before _ family BOUND)RUN)as[VALUE[[READY FRAME]NEXT]].
  split;[exact VALUE|]. split.
  - exact(gateway_bytes_complete b(Ptrofs.unsigned ofs)8(put64_values value)after READY ltac:(reflexivity)).
  - exact(conj FRAME NEXT).
Qed.
