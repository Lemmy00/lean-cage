(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual unsigned reader uses initialized owned bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayWordsMemory GatewayWords GatewayWordsMath GatewayWordData.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_get_initial b ofs width k memory :=
  Callstate(Internal f_host_get64)[Vptr b ofs;Vint(Int.repr(Z.of_nat width))]k memory.

Definition gateway_get_parameters b ofs width :=
  PTree.set _width(Vint(Int.repr(Z.of_nat width)))
    (PTree.set _p(Vptr b ofs)(create_undef_temps(fn_temps f_host_get64))).

Lemma gateway_reader_entry ge b ofs width k memory :
  edge ge(gateway_get_initial b ofs width k memory)
    (State f_host_get64(fn_body f_host_get64)k empty_env(gateway_get_parameters b ofs width)memory).
Proof.
  split;[exact I|];split.
  - apply step_internal_function;constructor.
    + repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
    + repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
    + unfold list_disjoint,var_names;cbn;intros first second LEFT RIGHT;
        repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst first;
        repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst second;discriminate.
    + constructor.
    + reflexivity.
  - split;[reflexivity|]. intros trace other STEP;inversion STEP;subst.
    match goal with ENTRY:function_entry2 _ _ _ _ _ _ _|-_=>inversion ENTRY;subst end.
    match goal with ALLOC:alloc_variables _ _ _ _ _ _|-_=>inversion ALLOC;subst end.
    match goal with BIND:bind_parameter_temps _ _ _=_|-_=>cbn in BIND;inversion BIND;subst end.
    auto.
Qed.

Ltac gateway_lookup_only identifier temporaries :=
  lazymatch temporaries with
  | PTree.set ?key ?value ?rest=>
    let wanted:=eval vm_compute in identifier in
    let actual:=eval vm_compute in key in
    lazymatch actual with wanted=>constr:(Some value)|_=>gateway_lookup_only identifier rest end
  end.

Ltac gateway_reader_load :=
  lazymatch goal with
  | |-gateway_framed_path _ _ (gateway_read_ready ?block ?ofs ?bytes)
      (State ?f(Sset ?identifier(Ederef ?pointer ?ty))?k ?environment ?temporaries ?memory)_ _=>
    let index_word:=gateway_lookup_only _index temporaries in
    lazymatch index_word with Some(Vint ?word)=>
      let offset:=eval vm_compute in(Int.unsigned word)in
      let ordinal:=eval vm_compute in(Z.to_nat offset)in
      let selected:=eval cbn[nth_error]in(nth_error bytes ordinal)in
      lazymatch selected with Some ?byte=>
        gateway_same(State f Sskip k environment(PTree.set identifier(Vint byte)temporaries)memory);
          [apply unchanged_store_edge;eapply edge_set;eapply value_load;
            [WriteAll.expression|reflexivity
            |match goal with|-context[Ptrofs.mul ?a ?b]=>
               let product:=eval vm_compute in(Ptrofs.mul a b)in change(Ptrofs.mul a b)with product end;
             match goal with INPUT:gateway_read_ready _ _ _ _|-_=>
               exact(INPUT ordinal byte ltac:(reflexivity))end]|]
      end
    end
  end.

Ltac gateway_reader_or :=
  lazymatch goal with
  | |-gateway_framed_path _ _ _ (State _ (Sset _ _)_ _ ?temporaries _)_ _=>
    let prior:=gateway_lookup_only _value temporaries in
    let selected:=gateway_lookup_only _t'1 temporaries in
    let index_word:=gateway_lookup_only _index temporaries in
    lazymatch prior with Some(Vlong ?value)=>
      lazymatch selected with Some(Vint ?byte)=>
        lazymatch index_word with Some(Vint ?index)=>
          let ordinal:=eval vm_compute in(Int.unsigned index)in
          gateway_set_as(Vlong(Int64.or value
            (Int64.shl(Int64.repr(Int.unsigned byte))(Int64.repr(8*ordinal)))))
        end
      end
    end
  end.

Ltac gateway_reader_iteration :=
  gateway_route;gateway_route;gateway_branch true;gateway_route;gateway_route;
  gateway_reader_load;gateway_route;gateway_reader_or;
  gateway_route;gateway_set;gateway_route.

Ltac gateway_reader_repeat count :=
  lazymatch count with O=>idtac|S ?rest=>gateway_reader_iteration;gateway_reader_repeat rest end.

Ltac gateway_reader_script :=
  lazymatch goal with
  | |-gateway_framed_path ?ge _ _ (gateway_get_initial ?block ?ofs ?width Kstop ?memory)_ _=>
    gateway_same(State f_host_get64(fn_body f_host_get64)Kstop empty_env
      (gateway_get_parameters block ofs width)memory);
      [apply unchanged_store_edge,gateway_reader_entry|]
  end;
  unfold f_host_get64,gateway_get_parameters;cbn[fn_body];
  gateway_route;gateway_set_as(Vlong Int64.zero);gateway_route;gateway_route;gateway_route;gateway_set;gateway_route;
  lazymatch goal with|-gateway_framed_path _ _ (gateway_read_ready _ _ ?bytes)_ _ _=>
    let count:=eval cbn[length]in(length bytes)in gateway_reader_repeat count end;
  gateway_route;gateway_route;gateway_branch false;gateway_route;gateway_route;gateway_route;
  lazymatch goal with
  | |-gateway_framed_path _ _ _ (State ?f(Sreturn(Some ?expression))Kstop empty_env ?temporaries ?memory)?value _=>
    gateway_same(Returnstate value Kstop memory);
      [apply unchanged_store_edge;eapply edge_return;[WriteAll.expression|reflexivity]|]
  end;
  let final_memory:=fresh "returned_memory" in let ready:=fresh "returned_ready" in
  apply gateway_framed_return;[apply gateway_read_ready_closed;assumption|intros final_memory ready;exact ready].

(* §FS-host-boundary.caller: Width is derived from the actual initialized byte list, at most eight. *)
Theorem gateway_get64_framed ge block ofs bytes memory :
  (length bytes<=8)%nat -> Ptrofs.unsigned ofs+Z.of_nat(length bytes)<=Ptrofs.modulus ->
  gateway_framed_path ge(gateway_byte_region block(Ptrofs.unsigned ofs)(length bytes))
    (gateway_read_ready block ofs bytes)(gateway_get_initial block ofs(length bytes)Kstop memory)
    (Vlong(gateway_get_value bytes))(gateway_read_ready block ofs bytes).
Proof.
  intros SIZE BOUND.
  do 9(destruct bytes as[|? bytes];[solve[gateway_reader_script]|]).
  cbn[length]in SIZE;lia.
Qed.

Lemma gateway_read_ready_bounds block ofs bytes memory :
  gateway_read_ready block ofs bytes memory ->
  Forall(fun byte=>0<=Int.unsigned byte<256)bytes.
Proof.
  intro READY;apply Forall_forall;intros byte MEMBER.
  apply In_nth_error in MEMBER;destruct MEMBER as[index SELECTED].
  pose proof(READY index byte SELECTED)as LOAD;unfold Mem.loadv in LOAD.
  destruct(zle _ _);[|discriminate].
  pose proof(Mem.load_cast _ _ _ _ _ LOAD)as FORMAT.
  cbn[Val.zero_ext]in FORMAT.
  apply gateway_byte_unsigned;congruence.
Qed.

(* §FS-host-boundary.caller: The decoder result and byte preservation use the same actual run. *)
Theorem gateway_get64_actual {World Event}(backend:gateway_backend World Event)ge active
    block ofs bytes before world events returned after final_world :
  gateway_private_contract backend(gateway_byte_region block(Ptrofs.unsigned ofs)(length bytes))active ->
  active world -> (length bytes<=8)%nat ->
  Ptrofs.unsigned ofs+Z.of_nat(length bytes)<=Ptrofs.modulus -> gateway_read_ready block ofs bytes before ->
  gateway_steps backend ge(gateway_live(gateway_get_initial block ofs(length bytes)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  returned=Vlong(Int64.repr(Z.of_nat(gateway_natural_decode(gateway_int_bytes bytes)))) /\
    gateway_read_ready block ofs bytes after /\ active final_world.
Proof.
  intros LAW ACTIVE SIZE BOUND READY RUN.
  pose proof(gateway_framed_return_exact backend ge
    (gateway_byte_region block(Ptrofs.unsigned ofs)(length bytes))active LAW
    (gateway_read_ready block ofs bytes)(gateway_get_initial block ofs(length bytes)Kstop before)
    (Vlong(gateway_get_value bytes))(gateway_read_ready block ofs bytes)
    before world events returned after final_world ACTIVE READY
    (gateway_get64_framed ge block ofs bytes before SIZE BOUND)RUN)as[VALUE POST].
  split;[|exact POST].
  rewrite VALUE;f_equal.
  rewrite<-(Int64.repr_unsigned(gateway_get_value bytes)).
  rewrite gateway_get_value_numeric;[reflexivity|apply gateway_read_ready_bounds with(block:=block)(ofs:=ofs)(memory:=before);exact READY|exact SIZE].
Qed.
