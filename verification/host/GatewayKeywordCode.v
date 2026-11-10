(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Object selection describes public argument rules independently of layout. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_keyword_entry:=(option(list Z)*val)%type.

Fixpoint gateway_keyword_take(name:list Z)(entries:list gateway_keyword_entry):(option val*list gateway_keyword_entry)%type:=
  match entries with
  |[] =>(None,[])
  |(key,value)::rest=>
    if match key with Some text=>if list_eq_dec Z.eq_dec name text then true else false|None=>false end
    then(Some value,rest)
    else let(found,leftover):=gateway_keyword_take name rest in(found,(key,value)::leftover)
  end.

(* Missing optional outputs remain untouched. The application initializes their
   defaults before the call. Leftover, duplicate and nonstring keys are rejected. *)
Fixpoint gateway_keyword_slots(names:list(list Z))(required:nat)(positional:list val)
    (keywords:list gateway_keyword_entry):option(list(option val)):=
  match names with
  |[]=>match positional,keywords with [],[]=>Some[]|_,_=>None end
  |name::rest=>let(found,leftover):=gateway_keyword_take name keywords in
    match positional,found with
    |_::_,Some _=>None
    |value::others,None=>match gateway_keyword_slots rest(Nat.pred required)others leftover with
      |Some selected=>Some(Some value::selected)|None=>None end
    |[],Some value=>match gateway_keyword_slots rest(Nat.pred required)[]leftover with
      |Some selected=>Some(Some value::selected)|None=>None end
    |[],None=>if Nat.eqb required 0 then
      match gateway_keyword_slots rest 0[]leftover with
      |Some selected=>Some(None::selected)|None=>None end else None
    end
  end.

Record gateway_keyword_plan:={
  gateway_keyword_names:list(list Z);
  gateway_keyword_required:nat;
  gateway_keyword_only:bool;
  gateway_keyword_label:list Z
}.

Definition gateway_keyword_positional_max(plan:gateway_keyword_plan):nat:=
  if gateway_keyword_only plan then gateway_keyword_required plan else length(gateway_keyword_names plan).

Definition gateway_keyword_parse plan positional keywords:=
  if Nat.leb(length positional)(gateway_keyword_positional_max plan)
  then gateway_keyword_slots(gateway_keyword_names plan)(gateway_keyword_required plan)positional keywords else None.

Definition gateway_keyword_format(plan:gateway_keyword_plan):list Byte.int:=map Byte.repr
  (repeat 79(gateway_keyword_required plan)++
    (if Nat.ltb(gateway_keyword_required plan)(length(gateway_keyword_names plan))
      then[124]++(if gateway_keyword_only plan then[36]else[])++
        repeat 79(length(gateway_keyword_names plan)-gateway_keyword_required plan)else[])++
    [58]++gateway_keyword_label plan).

Definition gateway_keyword_plan_valid plan:Prop:=
  (gateway_keyword_required plan<=length(gateway_keyword_names plan)<=14)%nat /\
  NoDup(gateway_keyword_names plan) /\
  Forall(fun name=>name<>[] /\Forall(fun byte=>0<byte<128)name)(gateway_keyword_names plan) /\
  Forall(fun byte=>0<byte<128)(gateway_keyword_label plan).

Fixpoint gateway_keyword_names_at(memory:mem)(object:block)(offset:Z)(names:list(list Z)):Prop:=
  match names with
  |[]=>Mem.load Mptr memory object offset=Some Vnullptr
  |name::rest=>exists pointer,Mem.load Mptr memory object offset=Some pointer /\
    gateway_error_cstring memory pointer(map Byte.repr name) /\
    gateway_keyword_names_at memory object(offset+8)rest
  end.

Definition gateway_keyword_names_memory memory pointer names:Prop:=
  exists object offset,pointer=Vptr object offset /\
    Ptrofs.unsigned offset+8*Z.of_nat(S(length names))<=Ptrofs.modulus /\
    gateway_keyword_names_at memory object(Ptrofs.unsigned offset)names.

Inductive gateway_keyword_write:mem->list val->list(option val)->mem->Prop:=
|gateway_keyword_write_end:forall memory,gateway_keyword_write memory[][]memory
|gateway_keyword_write_omitted:forall before cell cells selected after,
  gateway_keyword_write before cells selected after->gateway_keyword_write before(cell::cells)(None::selected)after
|gateway_keyword_write_selected:forall before cell cells value selected middle after,
  Mem.storev Mptr before cell value=Some middle->gateway_keyword_write middle cells selected after->
  gateway_keyword_write before(cell::cells)(Some value::selected)after.

Definition gateway_keyword_output(memory:mem)(cell:val):Prop:=
  exists object offset,cell=Vptr object offset /\
    Ptrofs.unsigned offset+8<=Ptrofs.modulus /\Mem.valid_access memory Mptr object(Ptrofs.unsigned offset)Writable.

Definition gateway_keyword_output_region(cells:list val)object position:Prop:=
  exists offset,In(Vptr object offset)cells /\Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+8.

Lemma gateway_keyword_slots_length names required positional keywords selected:
  gateway_keyword_slots names required positional keywords=Some selected->length selected=length names.
Proof.
  revert required positional keywords selected;induction names as[|name rest IH];intros required positional keywords selected.
  - destruct positional,keywords;cbn;intro SAME;inversion SAME;reflexivity.
  - cbn;destruct(gateway_keyword_take name keywords)as[found leftover];destruct positional as[|value others];
      destruct found as[found|];try discriminate.
    + destruct(gateway_keyword_slots rest(Nat.pred required)[]leftover)eqn:REST;intro SAME;inversion SAME;subst.
      cbn;f_equal;eapply IH;exact REST.
    + destruct(Nat.eqb required 0);[|discriminate].
      destruct(gateway_keyword_slots rest 0[]leftover)eqn:REST;intro SAME;inversion SAME;subst.
      cbn;f_equal;eapply IH;exact REST.
    + destruct(gateway_keyword_slots rest(Nat.pred required)others leftover)eqn:REST;intro SAME;inversion SAME;subst.
      cbn;f_equal;eapply IH;exact REST.
Qed.

Theorem gateway_keyword_selected_length plan positional keywords selected:
  gateway_keyword_parse plan positional keywords=Some selected->length selected=length(gateway_keyword_names plan).
Proof. unfold gateway_keyword_parse;destruct Nat.leb;[apply gateway_keyword_slots_length|discriminate]. Qed.

Theorem gateway_keyword_only_rejects_extra_positionals plan positional keywords:
  gateway_keyword_only plan=true->(gateway_keyword_required plan<length positional)%nat->
  gateway_keyword_parse plan positional keywords=None.
Proof.
  intros ONLY COUNT;unfold gateway_keyword_parse,gateway_keyword_positional_max;rewrite ONLY.
  destruct(Nat.leb(length positional)(gateway_keyword_required plan))eqn:BOUND;[apply Nat.leb_le in BOUND;lia|reflexivity].
Qed.
