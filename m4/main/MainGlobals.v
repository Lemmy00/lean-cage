(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Constructible complete-program initial memory and policy permissions. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From LeanCageMainNumber Require Import NumberMemory.
From LeanCageMain Require Import Main MainStructure MainMemory.
Import ListNotations.
Open Scope Z_scope.
Fixpoint initial_alignmentb ofs data := match data with
 | []=>true | x::rest=>Z.eqb(ofs mod Genv.init_data_alignment x)0 && initial_alignmentb(ofs+init_data_size x)rest end.
Lemma initial_alignment_sound ofs data : initial_alignmentb ofs data=true -> Genv.init_data_list_aligned ofs data.
Proof.
 revert ofs;induction data as[|x rest IH];intros ofs GOOD;[exact I|].
 apply andb_true_iff in GOOD;destruct GOOD as[HERE REST];split;[|apply IH;exact REST].
 apply Z.eqb_eq in HERE;apply Z.mod_divide;[destruct x;vm_compute;discriminate|exact HERE].
Qed.
Definition initial_symbolb (ge : Genv.t fundef type) data := match data with Init_addrof id _=>
 match Genv.find_symbol ge id with Some _=>true|None=>false end | _=>true end.
Lemma initial_symbol_sound (ge : Genv.t fundef type) id :
 (match Genv.find_symbol ge id with Some _=>true|None=>false end)=true ->
 exists b,Genv.find_symbol ge id=Some b.
Proof. destruct(Genv.find_symbol ge id)as[b|]eqn:FIND;intros GOOD;[exists b;reflexivity|discriminate]. Qed.
Definition initial_globalb ge (entry : ident*globdef fundef type) := match snd entry with
 | Gfun _=>true | Gvar v=>initial_alignmentb 0(gvar_init v)&&forallb(initial_symbolb ge)(gvar_init v) end.
Theorem checked_initializers_exist (p : Clight.program) :
 forallb(initial_globalb(Genv.globalenv p))(prog_defs p)=true -> exists m,Genv.init_mem p=Some m.
Proof.
 intros CHECKED;apply(Genv.init_mem_exists p);intros id v IN.
 rewrite forallb_forall in CHECKED;specialize(CHECKED(id,Gvar v)IN).
 unfold initial_globalb in CHECKED;cbn[snd]in CHECKED.
 apply andb_true_iff in CHECKED;destruct CHECKED as[ALIGN SYMBOLS];split;[apply initial_alignment_sound;exact ALIGN|].
 intros i ofs PRESENT;rewrite forallb_forall in SYMBOLS;specialize(SYMBOLS(Init_addrof i ofs)PRESENT).
 unfold initial_symbolb in SYMBOLS;exact(initial_symbol_sound(Genv.globalenv p)i SYMBOLS).
Qed.
Theorem native_initializers_checked : forallb(initial_globalb(Genv.globalenv Main.prog))(prog_defs Main.prog)=true.
Proof. vm_compute;reflexivity. Qed.
Theorem native_initial_memory_exists : exists m,Genv.init_mem Main.prog=Some m.
Proof. apply checked_initializers_exist;exact native_initializers_checked. Qed.
Theorem native_policy_permissions m : Genv.init_mem Main.prog=Some m ->
 Mem.range_perm m main_policy_block 0 96 Cur Writable /\ policy_writable m main_policy_block.
Proof.
 intros INIT.
 assert(VAR : Genv.find_var_info(Genv.globalenv Main.prog)main_policy_block=Some v_policy__1)by reflexivity.
 pose proof(proj1(Genv.init_mem_characterization Main.prog main_policy_block VAR INIT))as RANGE.
 change(Mem.range_perm m main_policy_block 0 96 Cur Writable)in RANGE.
 split;[exact RANGE|]. intros i INDEX;split.
 - rewrite Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
   change(8*i+8<=18446744073709551616);lia.
 - rewrite Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
   split;[red;intros pos BOUND;apply RANGE;change(8*i<=pos<8*i+8)in BOUND;lia|change(8|8*i);exists i;ring].
Qed.
