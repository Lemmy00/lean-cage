(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Type descriptors read actual relocated getset rows and names. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Record gateway_getset_entry:={
  gateway_getset_name:list Byte.int;
  gateway_getset_getter:Values.val;
  gateway_getset_setter:Values.val;
  gateway_getset_closure:Values.val
}.

Fixpoint gateway_getsets_memory memory table offset(entries:list gateway_getset_entry):Prop:=
  match entries with
  |[]=>Mem.load Mptr memory table offset=Some Vnullptr
  |entry::rest=>exists name,
    Mem.load Mptr memory table offset=Some name /\gateway_error_cstring memory name(gateway_getset_name entry) /\
    Mem.load Mptr memory table(offset+8)=Some(gateway_getset_getter entry) /\
    Mem.load Mptr memory table(offset+16)=Some(gateway_getset_setter entry) /\
    Mem.load Mptr memory table(offset+32)=Some(gateway_getset_closure entry) /\
    gateway_getsets_memory memory table(offset+40)rest
  end.

Record gateway_getset_source:={
  gateway_getset_name_symbol:ident;
  gateway_getset_source_name:list Byte.int;
  gateway_getset_getter_symbol:ident;
  gateway_getset_setter_symbol:option ident;
  gateway_getset_source_closure:Z
}.

Definition gateway_getset_pointer_initial pointer:=match pointer with
  |Some identifier=>Init_addrof identifier Ptrofs.zero|None=>Init_int64 Int64.zero end.

Fixpoint gateway_getset_initial_data sources:list init_data:=match sources with
  |[]=>[Init_int64 Int64.zero]
  |entry::rest=>[Init_addrof(gateway_getset_name_symbol entry)Ptrofs.zero;
    Init_addrof(gateway_getset_getter_symbol entry)Ptrofs.zero;
    gateway_getset_pointer_initial(gateway_getset_setter_symbol entry);
    Init_int64 Int64.zero;Init_int64(Int64.repr(gateway_getset_source_closure entry))]++gateway_getset_initial_data rest end.

Definition gateway_optional_pointer(ge:Clight.genv)identifier pointer:Prop:=
  match identifier with None=>pointer=Vnullptr|Some name=>exists object,
    Genv.find_symbol ge name=Some object /\pointer=Vptr object Ptrofs.zero end.

Definition gateway_getset_resolves(ge:Clight.genv)(source:gateway_getset_source)(entry:gateway_getset_entry):Prop:=
  gateway_getset_name entry=gateway_getset_source_name source /\
  (exists getter,Genv.find_symbol ge(gateway_getset_getter_symbol source)=Some getter /\
    gateway_getset_getter entry=Vptr getter Ptrofs.zero) /\
  gateway_optional_pointer ge(gateway_getset_setter_symbol source)(gateway_getset_setter entry) /\
  gateway_getset_closure entry=Vlong(Int64.repr(gateway_getset_source_closure source)).

Lemma gateway_resolved_getset_names ge sources entries:
  Forall2(gateway_getset_resolves ge)sources entries ->
  map gateway_getset_name entries=map gateway_getset_source_name sources.
Proof.
  intro MATCH;induction MATCH;[reflexivity|].
  cbn;destruct H as[NAME REST];rewrite NAME,IHMATCH;reflexivity.
Qed.

Lemma gateway_resolved_getset_at ge sources entries position source:
  Forall2(gateway_getset_resolves ge)sources entries ->nth_error sources position=Some source ->
  exists entry,nth_error entries position=Some entry /\gateway_getset_resolves ge source entry.
Proof.
  intro MATCH;revert position;induction MATCH;intros position LOOK;[destruct position;discriminate|].
  destruct position as[|position];cbn in LOOK|-*.
  - inversion LOOK;subst x;exists y;split;[reflexivity|exact H].
  - apply IHMATCH;exact LOOK.
Qed.

Lemma gateway_relocated_initial_prefix(ge:Clight.genv)memory table offset prefix suffix:
  Genv.load_store_init_data(Clight.genv_genv ge)memory table offset(prefix++suffix) ->
  Genv.load_store_init_data(Clight.genv_genv ge)memory table offset prefix.
Proof.
  revert offset;induction prefix as[|item rest IH];intros offset INITIAL;[exact I|].
  destruct item;cbn[Genv.load_store_init_data]in *.
  all:destruct INITIAL as[HEAD TAIL];split;[exact HEAD|eapply IH;exact TAIL].
Qed.

Theorem gateway_getsets_from_relocated_initializers(ge:Clight.genv)memory table offset sources :
  (forall entry name,In entry sources ->Genv.find_symbol ge(gateway_getset_name_symbol entry)=Some name ->
    gateway_error_cstring memory(Vptr name Ptrofs.zero)(gateway_getset_source_name entry)) ->
  Genv.load_store_init_data(Clight.genv_genv ge)memory table offset(gateway_getset_initial_data sources) ->
  exists entries,Forall2(gateway_getset_resolves ge)sources entries /\gateway_getsets_memory memory table offset entries.
Proof.
  revert offset;induction sources as[|source rest IH];intros offset NAMES INITIAL.
  - exists[];split;[constructor|]. exact(proj1 INITIAL).
  - cbn[gateway_getset_initial_data]in INITIAL.
    destruct(gateway_getset_setter_symbol source)as[setter|]eqn:SETTER_SYMBOL;
      cbn[gateway_getset_pointer_initial Genv.load_store_init_data size_chunk]in INITIAL.
    all:destruct INITIAL as[[name[NAME NAME_LOAD]][[getter[GETTER GETTER_LOAD]][SETTER[DOC[CLOSURE TAIL]]]]].
    all:change(size_chunk Mptr)with 8 in GETTER_LOAD,SETTER,CLOSURE,TAIL.
    all:replace(offset+8+8)with(offset+16)in SETTER by lia.
    all:replace(offset+8+8+8+8)with(offset+32)in CLOSURE by lia.
    all:replace(offset+8+8+8+8+8)with(offset+40)in TAIL by lia.
    all:destruct(IH(offset+40)ltac:(intros entry symbol MEMBER;apply NAMES;right;exact MEMBER)TAIL)
      as(entries &RESOLVES &MEMORY).
    + destruct SETTER as[set[SET SET_LOAD]].
      set(entry:={|gateway_getset_name:=gateway_getset_source_name source;gateway_getset_getter:=Vptr getter Ptrofs.zero;
        gateway_getset_setter:=Vptr set Ptrofs.zero;gateway_getset_closure:=Vlong(Int64.repr(gateway_getset_source_closure source))|}).
      exists(entry::entries);split.
      * constructor;[|exact RESOLVES]. unfold gateway_getset_resolves;cbn;split;[reflexivity|].
        split;[exists getter;split;[exact GETTER|reflexivity]|].
        split;[rewrite SETTER_SYMBOL;exists set;split;[exact SET|reflexivity]|reflexivity].
      * exists(Vptr name Ptrofs.zero);cbn;split;[exact NAME_LOAD|].
        split;[apply NAMES;[left;reflexivity|exact NAME]|]. split;[exact GETTER_LOAD|].
        split;[exact SET_LOAD|]. split;[exact CLOSURE|exact MEMORY].
    + set(entry:={|gateway_getset_name:=gateway_getset_source_name source;gateway_getset_getter:=Vptr getter Ptrofs.zero;
        gateway_getset_setter:=Vnullptr;gateway_getset_closure:=Vlong(Int64.repr(gateway_getset_source_closure source))|}).
      exists(entry::entries);split.
      * constructor;[|exact RESOLVES]. unfold gateway_getset_resolves;cbn;split;[reflexivity|].
        split;[exists getter;split;[exact GETTER|reflexivity]|].
        split;[rewrite SETTER_SYMBOL;reflexivity|reflexivity].
      * exists(Vptr name Ptrofs.zero);cbn;split;[exact NAME_LOAD|].
        split;[apply NAMES;[left;reflexivity|exact NAME]|]. split;[exact GETTER_LOAD|].
        split;[exact SETTER|]. split;[exact CLOSURE|exact MEMORY].
Qed.
