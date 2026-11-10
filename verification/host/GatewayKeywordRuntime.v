(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Fixed-signature tuple/dictionary operations expose individual effects. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayRuntime GatewayPython
  GatewayKeywordCode GatewayErrorRuntime GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_keyword_api:=gateway_tuple_size|gateway_tuple_item|gateway_dictionary_next|
  gateway_unicode_compare|gateway_error_occurred|gateway_type_subtype.
Definition gateway_keyword_ident api:ident:=match api with
  |gateway_tuple_size=>_PyTuple_Size|gateway_tuple_item=>_PyTuple_GetItem|gateway_dictionary_next=>_PyDict_Next
  |gateway_unicode_compare=>_PyUnicode_CompareWithASCIIString|gateway_error_occurred=>_PyErr_Occurred
  |gateway_type_subtype=>_PyType_IsSubtype end.
Definition gateway_keyword_definition api:option(Ctypes.fundef Clight.function):=
  match gateway_program_definition(gateway_keyword_ident api)global_definitions with
  |Some(Gfun(External external types result convention))=>Some(External external types result convention)
  |_=>None end.
Definition gateway_keyword_operation {World Event}(backend:gateway_backend World Event)api arguments
    before world result after next observed:Prop:=
  exists definition,gateway_keyword_definition api=Some definition /\
    gateway_runtime_operation backend definition arguments before world result after next observed.

Theorem actual_keyword_operation_signatures:
  gateway_keyword_definition gateway_tuple_size=Some(External
    (EF_external "PyTuple_Size"(mksignature[Xptr]Xlong cc_default))
    [tptr(Tstruct __object noattr)]tlong cc_default) /\
  gateway_keyword_definition gateway_tuple_item=Some(External
    (EF_external "PyTuple_GetItem"(mksignature[Xptr;Xlong]Xptr cc_default))
    [tptr(Tstruct __object noattr);tlong](tptr(Tstruct __object noattr))cc_default) /\
  gateway_keyword_definition gateway_dictionary_next=Some(External
    (EF_external "PyDict_Next"(mksignature[Xptr;Xptr;Xptr;Xptr]Xint cc_default))
    [tptr(Tstruct __object noattr);tptr tlong;tptr(tptr(Tstruct __object noattr));tptr(tptr(Tstruct __object noattr))]
    tint cc_default) /\
  gateway_keyword_definition gateway_unicode_compare=Some(External
    (EF_external "PyUnicode_CompareWithASCIIString"(mksignature[Xptr;Xptr]Xint cc_default))
    [tptr(Tstruct __object noattr);tptr tschar]tint cc_default) /\
  gateway_keyword_definition gateway_error_occurred=Some(External
    (EF_external "PyErr_Occurred"(mksignature[]Xptr cc_default))[]
    (tptr(Tstruct __object noattr))cc_default) /\
  gateway_keyword_definition gateway_type_subtype=Some(External
    (EF_external "PyType_IsSubtype"(mksignature[Xptr;Xptr]Xint cc_default))
    [tptr(Tstruct __typeobject noattr);tptr(Tstruct __typeobject noattr)]tint cc_default).
Proof. repeat split;reflexivity. Qed.

Definition gateway_keyword_address(memory:mem)(object:val):Prop:=
  exists block offset,object=Vptr block offset /\Mem.weak_valid_pointer memory block(Ptrofs.unsigned offset)=true.

Definition gateway_keyword_nonempty_address(memory:mem)(object:val):Prop:=
  exists block offset,object=Vptr block offset /\Mem.valid_pointer memory block(Ptrofs.unsigned offset)=true.

Lemma gateway_keyword_nonempty_is_address memory object:
  gateway_keyword_nonempty_address memory object->gateway_keyword_address memory object.
Proof.
  intros[block[offset[POINTER VALID]]];exists block,offset;split;[exact POINTER|].
  apply Mem.valid_pointer_implies;exact VALID.
Qed.

Record gateway_keyword_views(World:Type):={
  gateway_tuple_values:World->val->option(list val);
  gateway_dictionary_values:World->val->option(list(val*val));
  gateway_unicode_values:World->val->option(list Z);
  gateway_dictionary_cursor:World->val->int64->nat->Prop;
  gateway_object_class:World->val->val->Prop;
  gateway_real_type:World->val->Prop;
  gateway_unicode_class:val;
  gateway_class_subtype:World->val->val->bool;
  gateway_extension_payload:World->block->Z->Prop
}.

Definition gateway_keyword_views_retained {World}(python:World->python_world)(views:gateway_keyword_views World)world next:Prop:=
  (forall object values,python_live(python world)object->gateway_tuple_values _ views world object=Some values->
    gateway_tuple_values _ views next object=Some values) /\
  (forall object values,python_live(python world)object->gateway_dictionary_values _ views world object=Some values->
    gateway_dictionary_values _ views next object=Some values) /\
  (forall object values,python_live(python world)object->gateway_unicode_values _ views world object=Some values->
    gateway_unicode_values _ views next object=Some values) /\
  (forall object physical logical,python_live(python world)object->gateway_dictionary_cursor _ views world object physical logical->
    gateway_dictionary_cursor _ views next object physical logical) /\
  (forall object class,python_live(python world)object->gateway_object_class _ views world object class->
    gateway_object_class _ views next object class) /\
  (forall class,gateway_real_type _ views world class->gateway_real_type _ views next class) /\
  (forall first second,gateway_real_type _ views world first->gateway_real_type _ views world second->
    gateway_class_subtype _ views next first second=gateway_class_subtype _ views world first second) /\
  (forall object position,gateway_extension_payload _ views world object position->
    gateway_extension_payload _ views next object position).

(* These APIs do not invoke Python callbacks. Their native-output footprint is
   explicit; future runtime allocations and arbitrary outside memory stay broad. *)
Record gateway_keyword_post {World Event}(python:World->python_world)(views:gateway_keyword_views World)
    (io:Event->option gateway_native_io)(normal:mem->World->Prop)
    (output:block->Z->Prop)before world after next observed:Prop:={
  gateway_keyword_normal:normal after next;
  gateway_keyword_no_io:io observed=None;
  gateway_keyword_views_preserved:gateway_keyword_views_retained python views world next;
  gateway_keyword_native_counts:forall object,
    python_native_strong(python next)object=python_native_strong(python world)object;
  gateway_keyword_native_frame:Mem.unchanged_on(fun object position=>
    ~python_runtime_owned(python world)object /\~output object position)before after;
  gateway_keyword_extension_frame:Mem.unchanged_on(fun object position=>
    gateway_extension_payload _ views world object position /\~output object position)before after;
  gateway_keyword_native_permissions:forall object offset kind permission,
    Mem.valid_block before object->~python_runtime_owned(python world)object->
    (Mem.perm before object offset kind permission<->Mem.perm after object offset kind permission);
  gateway_keyword_classification:forall object,Mem.valid_block before object->
    (python_runtime_owned(python next)object<->python_runtime_owned(python world)object);
  gateway_keyword_borrowed:forall object,python_live(python world)object->gateway_keyword_address before object->
    python_live(python next)object /\gateway_keyword_address after object
}.

Definition gateway_keyword_no_output(_object:block)(_position:Z):Prop:=False.

Definition gateway_keyword_three_outputs(first second third:val):Prop:=
  exists first_block first_offset second_block second_offset third_block third_offset,
    first=Vptr first_block first_offset /\second=Vptr second_block second_offset /\third=Vptr third_block third_offset /\
    NoDup[first_block;second_block;third_block].

Record gateway_keyword_runtime {World Event}(backend:gateway_backend World Event)(python:World->python_world)
    (views:gateway_keyword_views World)(io:Event->option gateway_native_io)(normal:mem->World->Prop):Prop:={
  gateway_keyword_normal_python:forall memory world,normal memory world->
    python_gil(python world)=true /\python_pending(python world)=None /\python_world_valid(python world)memory;
  gateway_keyword_ambient:forall before world after next,
    normal before world->gateway_interference backend before world after next->
    normal after next /\gateway_keyword_views_retained python views world next /\
    Mem.unchanged_on(gateway_extension_payload _ views world)before after /\
    python_private_frame(python world)before after /\
    (forall object,python_live(python world)object->gateway_keyword_address before object->
      python_live(python next)object /\gateway_keyword_address after object);
  gateway_keyword_class_unique:forall world object first second,
    gateway_object_class _ views world object first->gateway_object_class _ views world object second->first=second;
  gateway_keyword_type_addresses:forall memory world class,
    normal memory world->gateway_real_type _ views world class->gateway_keyword_nonempty_address memory class;
  gateway_keyword_type_headers:forall memory world object block offset,
    normal memory world->python_live(python world)object->object=Vptr block offset->
    gateway_keyword_address memory object->
    exists class,Ptrofs.unsigned offset+16<=Ptrofs.modulus /\
      Mem.load Mptr memory block(Ptrofs.unsigned offset+8)=Some class /\
      gateway_object_class _ views world object class /\gateway_real_type _ views world class;
  gateway_keyword_unicode_type:forall memory world,
    normal memory world->gateway_real_type _ views world(gateway_unicode_class _ views);
  gateway_keyword_tuple_contents:forall memory world object values,
    normal memory world->gateway_tuple_values _ views world object=Some values->
    python_live(python world)object /\gateway_keyword_address memory object /\
      Forall(fun value=>python_live(python world)value /\gateway_keyword_address memory value)values;
  gateway_keyword_dictionary_contents:forall memory world object entries,
    normal memory world->gateway_dictionary_values _ views world object=Some entries->
    python_live(python world)object /\gateway_keyword_address memory object /\
      Forall(fun entry=>python_live(python world)(fst entry) /\gateway_keyword_address memory(fst entry) /\
        python_live(python world)(snd entry) /\gateway_keyword_address memory(snd entry))entries /\
      gateway_dictionary_cursor _ views world object Int64.zero 0;
  gateway_keyword_unicode_key:forall memory world object entries key value class,
    normal memory world->gateway_dictionary_values _ views world object=Some entries->In(key,value)entries->
    gateway_object_class _ views world key class->
    (class=gateway_unicode_class _ views \/gateway_class_subtype _ views world class(gateway_unicode_class _ views)=true)->
    exists text,gateway_unicode_values _ views world key=Some text;
  gateway_keyword_cursor_unique:forall world object physical first second,
    gateway_dictionary_cursor _ views world object physical first->
    gateway_dictionary_cursor _ views world object physical second->first=second;
  gateway_keyword_tuple_size:forall before world object values result after next observed,
    normal before world->gateway_tuple_values _ views world object=Some values->
    gateway_keyword_operation backend gateway_tuple_size[object]before world result after next observed->
    (Z.of_nat(length values)<=Int64.max_signed) /\result=Vlong(Int64.repr(Z.of_nat(length values))) /\
      gateway_keyword_post python views io normal gateway_keyword_no_output before world after next observed;
  gateway_keyword_tuple_item:forall before world object values index value result after next observed,
    normal before world->gateway_tuple_values _ views world object=Some values->nth_error values index=Some value->
    Z.of_nat index<=Int64.max_signed->
    gateway_keyword_operation backend gateway_tuple_item[object;Vlong(Int64.repr(Z.of_nat index))]
      before world result after next observed->result=value /\
      gateway_keyword_post python views io normal gateway_keyword_no_output before world after next observed;
  gateway_keyword_dictionary_next:forall before world object entries position key value physical logical
      result after next observed,
    normal before world->gateway_dictionary_values _ views world object=Some entries->
    gateway_dictionary_cursor _ views world object physical logical->
    Forall(gateway_keyword_output before)[position;key;value]->
    gateway_keyword_three_outputs position key value->
    (forall cell object offset,In cell[position;key;value]->cell=Vptr object offset->
      ~python_runtime_owned(python world)object)->
    Mem.loadv Mint64 before position=Some(Vlong physical)->
    gateway_keyword_operation backend gateway_dictionary_next[object;position;key;value]
      before world result after next observed->
    gateway_keyword_post python views io normal(gateway_keyword_output_region[position;key;value])
      before world after next observed /\
    ((result=Vint Int.zero /\logical=length entries) \/
      exists selected_key selected_value following,
        result=Vint Int.one /\nth_error entries logical=Some(selected_key,selected_value) /\
        Mem.loadv Mint64 after position=Some(Vlong following) /\
        Mem.loadv Mptr after key=Some selected_key /\Mem.loadv Mptr after value=Some selected_value /\
        gateway_dictionary_cursor _ views next object following(S logical));
  gateway_keyword_compare:forall before world object text pointer ascii result after next observed,
    normal before world->gateway_unicode_values _ views world object=Some text->
    gateway_error_cstring before pointer(map Byte.repr ascii)->Forall(fun byte=>0<byte<128)ascii->
    gateway_keyword_operation backend gateway_unicode_compare[object;pointer]
      before world result after next observed->exists compared,result=Vint compared /\
      (compared=Int.zero<->text=ascii) /\
      gateway_keyword_post python views io normal gateway_keyword_no_output before world after next observed;
  gateway_keyword_error_clear:forall before world result after next observed,
    normal before world->gateway_keyword_operation backend gateway_error_occurred[]
      before world result after next observed->result=Vnullptr /\
      gateway_keyword_post python views io normal gateway_keyword_no_output before world after next observed;
  gateway_keyword_subtype:forall before world first second result after next observed,
    normal before world->gateway_real_type _ views world first->gateway_real_type _ views world second->
    gateway_keyword_operation backend gateway_type_subtype[first;second]before world result after next observed->
    result=Vint(if gateway_class_subtype _ views world first second then Int.one else Int.zero) /\
      gateway_keyword_post python views io normal gateway_keyword_no_output before world after next observed
}.
