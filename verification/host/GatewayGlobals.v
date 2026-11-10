(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Native static bytes come from the actual loaded program. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayCancellationInputs GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_static_cstring(identifier:ident)(variable:globvar type)(bytes:list Byte.int):Prop:=
  (prog_defmap prog)!identifier=Some(Gvar variable) /\gvar_volatile variable=false /\~In Byte.zero bytes /\
  Z.of_nat(length bytes)+1<=Ptrofs.modulus /\init_data_list_size(gvar_init variable)=Z.of_nat(length bytes)+1 /\
  Genv.bytes_of_init_data_list(Clight.genv_genv(Clight.globalenv prog))(gvar_init variable)=
    inj_bytes(bytes++[Byte.zero]).

Lemma gateway_byte_initial_size bytes:
  init_data_list_size(map(fun byte=>Init_int8(Int.repr(Byte.unsigned byte)))bytes)=Z.of_nat(length bytes).
Proof.
  induction bytes as[|byte rest IH];[reflexivity|].
  change(1+init_data_list_size(map(fun value=>Init_int8(Int.repr(Byte.unsigned value)))rest)=Z.of_nat(S(length rest))).
  rewrite IH,Nat2Z.inj_succ;lia.
Qed.

Lemma gateway_byte_initial_contents(ge:Clight.genv)bytes:
  Genv.bytes_of_init_data_list ge(map(fun byte=>Init_int8(Int.repr(Byte.unsigned byte)))bytes)=inj_bytes bytes.
Proof.
  induction bytes as[|byte rest IH];[reflexivity|].
  change(inj_bytes(encode_int 1%nat(Int.unsigned(Int.repr(Byte.unsigned byte))))++
    Genv.bytes_of_init_data_list ge(map(fun value=>Init_int8(Int.repr(Byte.unsigned value)))rest)=inj_bytes(byte::rest)).
  rewrite Int.unsigned_repr by(pose proof(Byte.unsigned_range byte)as RANGE;
    change(0<=Byte.unsigned byte<256)in RANGE;change Int.max_unsigned with 4294967295;lia).
  change(Memdata.Byte(Byte.repr(Byte.unsigned byte))::
    Genv.bytes_of_init_data_list ge(map(fun value=>Init_int8(Int.repr(Byte.unsigned value)))rest)=
    Memdata.Byte byte::inj_bytes rest).
  rewrite Byte.repr_unsigned,IH;reflexivity.
Qed.

Lemma gateway_registered_string_bytes variable bytes:
  registered_string variable(map Byte.unsigned bytes)->
  gvar_init variable=map(fun byte=>Init_int8(Int.repr(Byte.unsigned byte)))(bytes++[Byte.zero]).
Proof.
  unfold registered_string;intro CONTENTS;rewrite CONTENTS,map_app,map_map,map_app;reflexivity.
Qed.

Lemma gateway_static_string_from_registration identifier variable bytes:
  (prog_defmap prog)!identifier=Some(Gvar variable)->gvar_volatile variable=false->
  registered_string variable(map Byte.unsigned bytes)->~In Byte.zero bytes->
  Z.of_nat(length bytes)+1<=Ptrofs.modulus->gateway_static_cstring identifier variable bytes.
Proof.
  intros DEFINITION NONVOLATILE CONTENTS NONZERO BOUND.
  unfold gateway_static_cstring;split;[exact DEFINITION|]. split;[exact NONVOLATILE|].
  split;[exact NONZERO|]. split;[exact BOUND|].
  rewrite(gateway_registered_string_bytes variable bytes CONTENTS);split.
  - rewrite gateway_byte_initial_size,length_app;cbn;lia.
  - apply gateway_byte_initial_contents.
Qed.

Local Opaque prog.
Theorem gateway_static_cstring_loaded identifier variable bytes initial:
  gateway_static_cstring identifier variable bytes->Genv.init_mem prog=Some initial->
  exists symbol,Genv.find_symbol(Clight.globalenv prog)identifier=Some symbol /\
    gateway_error_cstring initial(Vptr symbol Ptrofs.zero)bytes.
Proof.
  intros[DEFINITION[NONVOLATILE[NONZERO[BOUND[SIZE BYTES]]]]]INITIAL.
  destruct(gateway_actual_variable_binding identifier variable DEFINITION)as[symbol[SYMBOL VARIABLE]].
  destruct(Genv.init_mem_characterization(gv:=variable)(m:=initial)prog symbol VARIABLE INITIAL)
    as[PERMISSIONS[ONLY[DATA LOAD]]].
  change(Genv.bytes_of_init_data_list(Genv.globalenv prog)(gvar_init variable)=
    inj_bytes(bytes++[Byte.zero]))in BYTES.
  specialize(LOAD NONVOLATILE);rewrite SIZE,BYTES in LOAD.
  exists symbol;split;[exact SYMBOL|]. exists symbol,Ptrofs.zero.
  split;[reflexivity|]. split;[exact NONZERO|]. split;[|exact LOAD].
  change(Ptrofs.unsigned Ptrofs.zero)with 0;lia.
Qed.
