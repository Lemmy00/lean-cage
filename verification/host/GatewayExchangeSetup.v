(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Actual exchange allocation supplies the two separate private socket output arrays. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayExchangeEntry GatewayStackAllocation GatewaySpawnRuntime
  GatewayBindings GatewayThreadRuntime GatewayLocalRuntime GatewayPairSource GatewayPairStatements GatewayRegistry.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_entry_guard:=match fn_body f_host_exchange with Ssequence guard _=>guard|_=>Sskip end.
Definition exchange_initialized_body:=match fn_body f_host_exchange with Ssequence _ body=>body|_=>Sskip end.

Fixpoint exchange_setup_after(count:nat):statement:=
  match count with
  |O=>exchange_initialized_body
  |S previous=>match exchange_setup_after previous with Ssequence _ rest=>rest|_=>Sskip end end.
Definition exchange_setup_at count:=match exchange_setup_after count with Ssequence first _=>first|_=>Sskip end.
Definition exchange_clock_prefix:=exchange_setup_at 0.
Definition exchange_clock_guard:=exchange_setup_at 1.
Definition exchange_data_pair:=exchange_setup_at 2.
Definition exchange_control_pair:=exchange_setup_at 3.
Definition exchange_get_flags:=exchange_setup_at 4.
Definition exchange_flags_guard:=exchange_setup_at 5.
Definition exchange_actions_initialize:=exchange_setup_at 6.
Definition exchange_actions_guard:=exchange_setup_at 7.
Definition exchange_attributes_initialize:=exchange_setup_at 8.
Definition exchange_attributes_guard:=exchange_setup_at 9.
Definition exchange_group_setup:=exchange_setup_at 10.
Definition exchange_flags_setup:=exchange_setup_at 11.
Definition exchange_input_setup:=exchange_setup_at 12.
Definition exchange_output_setup:=exchange_setup_at 13.
Definition exchange_cancellation_setup:=exchange_setup_at 14.
Definition exchange_closefrom_setup:=exchange_setup_at 15.
Definition exchange_data_pair_call:=match exchange_data_pair with Ssequence call _=>call|_=>Sskip end.
Definition exchange_data_pair_guard:=match exchange_data_pair with Ssequence _ guard=>guard|_=>Sskip end.
Definition exchange_control_pair_call:=match exchange_control_pair with Ssequence call _=>call|_=>Sskip end.
Definition exchange_control_pair_guard:=match exchange_control_pair with Ssequence _ guard=>guard|_=>Sskip end.

Theorem actual_exchange_pair_calls:
  exchange_data_pair_call=Scall(Some _t'3)(Evar _host_private_pair(Tfunction[tptr tint]tint cc_default))
    [Evar _pair(tarray tint 2)] /\
  exchange_control_pair_call=Scall(Some _t'7)(Evar _host_private_pair(Tfunction[tptr tint]tint cc_default))
    [Evar _control(tarray tint 2)].
Proof. split;reflexivity. Qed.

Lemma exchange_pair_cells_from_stack memory object:
  Mem.range_perm memory object 0 8 Cur Freeable->gateway_pair_output_cells memory object Ptrofs.zero.
Proof.
  intro PERMISSIONS;split.
  - split;[lia|]. split;[change(8<=18446744073709551616);lia|]. split.
    + eapply Mem.perm_valid_block;apply(PERMISSIONS 0);lia.
    + intros position RANGE;eapply Mem.perm_implies;[apply PERMISSIONS;exact RANGE|constructor].
  - split.
    + split.
      * intros position RANGE;eapply Mem.perm_implies;[apply PERMISSIONS;change(0<=position<4)in RANGE;lia|constructor].
      * apply Z.divide_0_r.
    + split.
      * intros position RANGE;eapply Mem.perm_implies;[apply PERMISSIONS;change(4<=position<8)in RANGE;lia|constructor].
      * change(4|4);apply Z.divide_refl.
Qed.

Theorem actual_exchange_entry_owns_pairs ge before environment after:
  exchange_stack_buffers ge before environment after->
  exists data control,
    environment!_pair=Some(data,tarray tint 2) /\environment!_control=Some(control,tarray tint 2) /\data<>control /\
    ~Mem.valid_block before data /\~Mem.valid_block before control /\
    gateway_pair_output_cells after data Ptrofs.zero /\gateway_pair_output_cells after control Ptrofs.zero.
Proof.
  intros[BUFFERS[[LIVE DISTINCT]FRAME]].
  destruct(BUFFERS _pair(tarray tint 2)ltac:(cbn;auto 12))as[data[DATA[FRESH_DATA DATA_PERMISSIONS]]].
  destruct(BUFFERS _control(tarray tint 2)ltac:(cbn;auto 12))as[control[CONTROL[FRESH_CONTROL CONTROL_PERMISSIONS]]].
  exists data,control;split;[exact DATA|]. split;[exact CONTROL|]. split.
  - eapply DISTINCT;[exact DATA|exact CONTROL|discriminate].
  - split;[exact FRESH_DATA|]. split;[exact FRESH_CONTROL|]. split;apply exchange_pair_cells_from_stack;
      change(sizeof ge(tarray tint 2))with 8 in *;assumption.
Qed.

Lemma actual_exchange_setup_unshadowed ge before environment after identifier:
  alloc_variables ge empty_env before(fn_vars f_host_exchange)environment after->
  ~In identifier(map fst(fn_vars f_host_exchange))->environment!identifier=None.
Proof. intros ALLOC ABSENT;rewrite(gateway_alloc_variables_lookup ge empty_env before(fn_vars f_host_exchange)
  environment after identifier ALLOC ABSENT);apply PTree.gempty. Qed.

Theorem actual_exchange_endpoint_native {World}(native_private:World->block->Prop)world memory environment data control:
  gateway_native_environment native_private world memory environment->
  environment!_pair=Some(data,tarray tint 2)->environment!_control=Some(control,tarray tint 2)->
  native_private world data /\native_private world control.
Proof. intros NATIVE DATA CONTROL;split;[exact(proj2(NATIVE _ _ _ DATA))|exact(proj2(NATIVE _ _ _ CONTROL))]. Qed.

Lemma exchange_endpoint_reference ge environment temporaries memory identifier object:
  environment!identifier=Some(object,tarray tint 2)->
  expression_value ge environment temporaries memory(Evar identifier(tarray tint 2))(Vptr object Ptrofs.zero).
Proof.
  intro ARRAY;eapply location_read_value;[apply local_location_value;exact ARRAY|].
  apply deref_loc_reference;reflexivity.
Qed.

Theorem actual_exchange_data_pair_call(ge:Clight.genv)environment temporaries memory data symbol:
  environment!_pair=Some(data,tarray tint 2)->environment!_host_private_pair=None->
  Genv.find_symbol ge _host_private_pair=Some symbol->Genv.find_funct_ptr ge symbol=Some(Internal f_host_private_pair)->
  store_edge ge(State f_host_exchange exchange_data_pair_call
    (Kseq exchange_data_pair_guard(Kseq(exchange_setup_after 3)Kstop))environment temporaries memory)
    (Callstate(Internal f_host_private_pair)[Vptr data Ptrofs.zero]
      (Kcall(Some _t'3)f_host_exchange environment temporaries
        (Kseq exchange_data_pair_guard(Kseq(exchange_setup_after 3)Kstop)))memory).
Proof.
  intros ARRAY UNSHADOWED SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact UNSHADOWED|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr data Ptrofs.zero).
    + apply exchange_endpoint_reference;exact ARRAY.
    + reflexivity.
    + apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.
