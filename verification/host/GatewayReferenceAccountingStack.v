(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A synthetic accounting stack retains pointer multiplicities;
   it supplies no claim about the application's real caller stack or source owners. *)
From Stdlib Require Import List PeanoNat Lia.
From compcert Require Import Maps Values Clight.
From HostGateway Require Import GatewaySource GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceNormalForm GatewayReferenceStackBound.
Import ListNotations.

Fixpoint gateway_accounting_stack(pointers:list Values.val):cont:=
  match pointers with
  |[]=>Kstop
  |pointer::rest=>Kcall None f_host_value empty_env(PTree.set _value pointer(PTree.empty Values.val))(gateway_accounting_stack rest)
  end.
Fixpoint gateway_accounting_entries(pointers:list Values.val):list gateway_owned_reference:=
  match pointers with
  |[]=>[]
  |pointer::rest=>gateway_reference_entry(length rest)(gateway_reference_temporary(length rest)_value)pointer::gateway_accounting_entries rest
  end.
Definition gateway_accounting_ledger pointers:gateway_reference_ledger:={|
  gateway_reference_next:=length pointers;gateway_reference_entries:=gateway_accounting_entries pointers|}.

Lemma gateway_accounting_depth pointers:gateway_reference_depth(gateway_accounting_stack pointers)=length pointers.
Proof. induction pointers;cbn;congruence. Qed.
Lemma gateway_accounting_pointers pointers:map gateway_reference_pointer(gateway_accounting_entries pointers)=pointers.
Proof. induction pointers;cbn;congruence. Qed.
Lemma gateway_accounting_entry_form pointers entry:
  In entry(gateway_accounting_entries pointers)->
  gateway_reference_owner entry=gateway_reference_temporary(gateway_reference_ticket entry)_value /\
  (gateway_reference_ticket entry<length pointers)%nat.
Proof.
  induction pointers as[|pointer rest IH];cbn;intros MEMBER;[contradiction|].
  destruct MEMBER as[SAME|MEMBER];[subst entry;cbn;auto|].
  destruct(IH MEMBER)as[OWNER BELOW];split;[exact OWNER|lia].
Qed.

Theorem gateway_accounting_formed pointers:gateway_reference_ledger_well_formed(gateway_accounting_ledger pointers).
Proof.
  induction pointers as[|pointer rest IH].
  - split;[constructor|split;constructor].
  - destruct IH as[TICKETS[OWNERS BOUNDS]].
    unfold gateway_reference_ledger_well_formed,gateway_accounting_ledger;cbn[gateway_reference_entries gateway_reference_next gateway_accounting_entries map
      gateway_reference_ticket gateway_reference_owner gateway_reference_entry].
    split.
    + constructor;[|exact TICKETS]. intro MEMBER;apply in_map_iff in MEMBER.
      destruct MEMBER as[entry[TICKET MEMBER]]. pose proof(proj2(gateway_accounting_entry_form rest entry MEMBER));lia.
    + split.
      * constructor;[|exact OWNERS]. intro MEMBER;apply in_map_iff in MEMBER.
        destruct MEMBER as[entry[OWNER MEMBER]].
        destruct(gateway_accounting_entry_form rest entry MEMBER)as[FORM BELOW]. rewrite FORM in OWNER;injection OWNER;intros;lia.
      * constructor;[cbn;lia|]. eapply Forall_impl;[|exact BOUNDS]. intros entry BELOW;cbn in BELOW|-*;lia.
Qed.

Theorem gateway_accounting_bound pointers:
  gateway_reference_stack_bound(gateway_accounting_stack pointers)(gateway_accounting_ledger pointers).
Proof.
  induction pointers as[|pointer rest IH];intros entry MEMBER;[inversion MEMBER|].
  change(In entry(gateway_reference_entry(length rest)(gateway_reference_temporary(length rest)_value)pointer::gateway_accounting_entries rest))in MEMBER.
  destruct MEMBER as[SAME|MEMBER].
  - subst entry;exists(length rest),_value;split;[reflexivity|].
    cbn[gateway_reference_saved_temporary gateway_accounting_stack gateway_reference_pointer gateway_reference_entry].
    rewrite gateway_accounting_depth;destruct(Nat.eq_dec(length rest)(length rest));[apply PTree.gss|contradiction].
  - destruct(IH entry MEMBER)as[invocation[identifier[OWNER SAVED]]].
    exists invocation,identifier;split;[exact OWNER|].
    cbn[gateway_reference_saved_temporary gateway_accounting_stack];rewrite gateway_accounting_depth.
    destruct(gateway_accounting_entry_form rest entry MEMBER)as[FORM BELOW].
    rewrite OWNER in FORM;injection FORM;intros;subst invocation.
    destruct(Nat.eq_dec(gateway_reference_ticket entry)(length rest));[lia|exact SAVED].
Qed.

Lemma gateway_accounting_count pointers pointer:
  gateway_reference_count(gateway_accounting_ledger pointers)pointer=count_occ Val.eq pointers pointer.
Proof. unfold gateway_reference_count,gateway_accounting_ledger;cbn;rewrite gateway_accounting_pointers;reflexivity. Qed.

Lemma gateway_accounting_call pointers:is_call_cont(gateway_accounting_stack pointers).
Proof. destruct pointers;exact I. Qed.
