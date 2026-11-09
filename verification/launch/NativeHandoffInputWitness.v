(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Build example inputs with the actual loader's global permissions. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
Require Import Machine ErrorNumber Library FreshMemory WriteMemory ReceiverAllocation ScalarMemory.
From EntryNative Require Import EntrySource NativeHandoffArguments NativeHandoffMachine NativeHandoffInput
  NativeHandoffInitial.
Import ListNotations.
Open Scope Z_scope.


Fixpoint handoff_initializers_readyb (ge:Genv.t Clight.fundef type) offset values : bool :=
  match values with
  | []=>true
  | value::rest=>
      (offset mod Genv.init_data_alignment value =? 0) &&
      (match value with Init_addrof id _=>match Genv.find_symbol ge id with Some _=>true|None=>false end|_=>true end) &&
      handoff_initializers_readyb ge(offset+init_data_size value)rest
  end.

Lemma handoff_initializers_ready_sound ge values : forall offset,
  handoff_initializers_readyb ge offset values=true ->
  Genv.init_data_list_aligned offset values /\
  forall id displacement,In(Init_addrof id displacement)values -> exists b,Genv.find_symbol ge id=Some b.
Proof.
  induction values as[|value rest IH];intros offset READY;[split;[exact I|intros;contradiction]|].
  cbn[handoff_initializers_readyb]in READY;apply andb_true_iff in READY;destruct READY as[HEAD TAIL].
  apply andb_true_iff in HEAD;destruct HEAD as[ALIGN SYMBOL].
  destruct(IH _ TAIL)as[REST RELOC];split.
  - split;[|exact REST]. apply Z.mod_divide.
    + destruct value;vm_compute;discriminate.
    + apply Z.eqb_eq;exact ALIGN.
  - intros id displacement[HERE|LATER].
    + subst value;cbn in SYMBOL;destruct(Genv.find_symbol ge id)as[b|]eqn:FOUND;[exists b;reflexivity|discriminate].
    + eapply RELOC;exact LATER.
Qed.

Definition handoff_globals_readyb := forallb
  (fun named=>match snd named with Gfun _=>true|Gvar variable=>handoff_initializers_readyb handoff_ge 0(gvar_init variable)end)
  EntrySource.global_definitions.
Lemma handoff_globals_ready : handoff_globals_readyb=true.
Proof. unfold handoff_globals_readyb,handoff_ge;vm_compute;reflexivity. Qed.

Lemma handoff_loader_memory_exists (program:Clight.program) :
  forallb (fun named=>match snd named with
    | Gfun _=>true
    | Gvar variable=>handoff_initializers_readyb (Genv.globalenv program) 0(gvar_init variable)
    end)(prog_defs program)=true -> exists initial,Genv.init_mem program=Some initial.
Proof.
  intros READY;apply Genv.init_mem_exists;intros id variable MEMBER.
  rewrite forallb_forall in READY;specialize(READY(id,Gvar variable)MEMBER).
  change(handoff_initializers_readyb (Genv.globalenv program) 0(gvar_init variable)=true)in READY.
  exact(handoff_initializers_ready_sound _ _ 0 READY).
Qed.

Theorem handoff_actual_initial_memory_exists : exists initial,
  Genv.init_mem EntrySource.prog=Some initial.
Proof. apply handoff_loader_memory_exists;exact handoff_globals_ready. Qed.

Lemma handoff_loader_ge : Clight.genv_genv handoff_ge=Genv.globalenv EntrySource.prog.
Proof. reflexivity. Qed.
Local Opaque handoff_ge handoff_symbol.

Lemma handoff_initial_string initial id variable bytes :
  Genv.init_mem EntrySource.prog=Some initial ->
  Genv.find_var_info handoff_ge(handoff_symbol id)=Some variable ->
  gvar_volatile variable=false ->
  init_data_list_size(gvar_init variable)=Z.of_nat(length(bytes++[Byte.zero])) ->
  Genv.bytes_of_init_data_list handoff_ge(gvar_init variable)=map Byte(bytes++[Byte.zero]) ->
  Forall(fun byte=>byte<>Byte.zero)bytes -> Z.of_nat(length(bytes++[Byte.zero]))<=Int64.max_unsigned ->
  c_string initial(handoff_global_address id)bytes.
Proof.
  intros INITIAL INFO VOLATILE SIZE BYTES NONZERO BOUND.
  rewrite handoff_loader_ge in INFO,BYTES.
  destruct(Genv.init_mem_characterization EntrySource.prog(handoff_symbol id) INFO INITIAL)
    as[PERMS[ONLY[LOAD BYTELOAD]]].
  split;[exact NONZERO|]. split.
  - unfold span_bounds,handoff_global_address;cbn[address_offset].
    split;[change(0<=0<18446744073709551616);lia|]. split;[|exact BOUND].
    change Ptrofs.modulus with 18446744073709551616;change Int64.max_unsigned with 18446744073709551615 in BOUND;lia.
  - specialize(BYTELOAD VOLATILE).
    change(Mem.loadbytes initial(handoff_symbol id)0(Z.of_nat(length(bytes++[Byte.zero])))=Some(map Byte(bytes++[Byte.zero]))).
    rewrite <- SIZE. eapply eq_trans;[exact BYTELOAD|]. f_equal;exact BYTES.
Qed.

Local Transparent handoff_ge handoff_symbol.

Lemma handoff_initial_uid_info :
  Genv.find_var_info handoff_ge(handoff_symbol EntrySource._run_uid)=Some EntrySource.v_run_uid.
Proof. unfold handoff_ge,handoff_symbol;vm_compute;reflexivity. Qed.
Lemma handoff_initial_policy_info :
  Genv.find_var_info handoff_ge(handoff_symbol EntrySource._policy__1)=Some EntrySource.v_policy__1.
Proof. unfold handoff_ge,handoff_symbol;vm_compute;reflexivity. Qed.
Lemma handoff_initial_root_info :
  Genv.find_var_info handoff_ge(handoff_symbol EntrySource._root_path)=Some EntrySource.v_root_path.
Proof. unfold handoff_ge,handoff_symbol;vm_compute;reflexivity. Qed.
Lemma handoff_initial_preflight_info :
  Genv.find_var_info handoff_ge(handoff_symbol EntrySource._preflight)=Some EntrySource.v_preflight.
Proof. unfold handoff_ge,handoff_symbol;vm_compute;reflexivity. Qed.
Lemma handoff_initial_mode_info :
  Genv.find_var_info handoff_ge(handoff_symbol EntrySource._mode)=Some EntrySource.v_mode.
Proof. unfold handoff_ge,handoff_symbol;vm_compute;reflexivity. Qed.

Lemma handoff_initial_uid_access initial : Genv.init_mem EntrySource.prog=Some initial ->
  Mem.valid_access initial Mint32(handoff_symbol EntrySource._run_uid)0 Writable.
Proof.
  intros INITIAL;pose proof handoff_initial_uid_info as INFO;rewrite handoff_loader_ge in INFO.
  pose proof(proj1(Genv.init_mem_characterization _ _ INFO INITIAL))as PERM.
  change(Mem.range_perm initial(handoff_symbol EntrySource._run_uid)0 4 Cur Writable)in PERM.
  split;[exact PERM|change(4|0);apply Z.divide_0_r].
Qed.
Lemma handoff_initial_policy_access initial : Genv.init_mem EntrySource.prog=Some initial ->
  Mem.valid_access initial Mptr(handoff_symbol EntrySource._policy__1)88 Writable.
Proof.
  intros INITIAL;pose proof handoff_initial_policy_info as INFO;rewrite handoff_loader_ge in INFO.
  pose proof(proj1(Genv.init_mem_characterization _ _ INFO INITIAL))as PERM.
  change(Mem.range_perm initial(handoff_symbol EntrySource._policy__1)0 96 Cur Writable)in PERM.
  split;[intros pos RANGE;apply PERM;change(88<=pos<96)in RANGE;lia|]. change(8|88);exists 11;reflexivity.
Qed.
Lemma handoff_initial_root_access initial : Genv.init_mem EntrySource.prog=Some initial ->
  Mem.range_perm initial(handoff_symbol EntrySource._root_path)0 160 Cur Writable.
Proof.
  intros INITIAL;pose proof handoff_initial_root_info as INFO;rewrite handoff_loader_ge in INFO.
  exact(proj1(Genv.init_mem_characterization _ _ INFO INITIAL)).
Qed.
Lemma handoff_initial_preflight_value initial : Genv.init_mem EntrySource.prog=Some initial ->
  Mem.loadv Mint32 initial(Vptr(handoff_symbol EntrySource._preflight)Ptrofs.zero)=Some(Vint Int.zero).
Proof.
  intros INITIAL;pose proof handoff_initial_preflight_info as INFO;rewrite handoff_loader_ge in INFO.
  destruct(Genv.init_mem_characterization _ _ INFO INITIAL)
    as[PERM[ONLY[DATA BYTES]]]. specialize(BYTES eq_refl).
  change(Mem.loadbytes initial(handoff_symbol EntrySource._preflight)0 4=
    Some[Byte Byte.zero;Byte Byte.zero;Byte Byte.zero;Byte Byte.zero])in BYTES.
  change(Mem.load Mint32 initial(handoff_symbol EntrySource._preflight)0=Some(Vint Int.zero)).
  replace(Vint Int.zero)with(decode_val Mint32[Byte Byte.zero;Byte Byte.zero;Byte Byte.zero;Byte Byte.zero])by reflexivity.
  eapply Mem.loadbytes_load;[exact BYTES|change(4|0);apply Z.divide_0_r].
Qed.
Lemma handoff_loader_pointer (program:AST.program Clight.fundef type) initial object variable id pointer :
  Genv.find_var_info(Genv.globalenv program)object=Some variable ->
  Genv.init_mem program=Some initial ->gvar_volatile variable=false ->
  gvar_init variable=[Init_addrof id Ptrofs.zero] ->
  Genv.find_symbol(Genv.globalenv program)id=Some pointer ->
  Mem.load Mptr initial object 0=Some(Vptr pointer Ptrofs.zero).
Proof.
  intros INFO INITIAL VOLATILE INIT SYMBOL.
  destruct(Genv.init_mem_characterization program object INFO INITIAL)as[PERM[ONLY[DATA BYTES]]].
  specialize(DATA VOLATILE);rewrite INIT in DATA.
  destruct(proj1 DATA)as[b[FOUND LOAD]].
  rewrite SYMBOL in FOUND;inversion FOUND;subst b;exact LOAD.
Qed.

Lemma handoff_initial_mode_value initial : Genv.init_mem EntrySource.prog=Some initial ->
  Mem.loadv Mptr initial(Vptr(handoff_symbol EntrySource._mode)Ptrofs.zero)=
    Some(address_value(handoff_global_address EntrySource.___stringlit_1)).
Proof.
  intros INITIAL;change(Mem.load Mptr initial(handoff_symbol EntrySource._mode)0=
    Some(Vptr(handoff_symbol EntrySource.___stringlit_1)Ptrofs.zero)).
  eapply handoff_loader_pointer with(variable:=EntrySource.v_mode)(id:=EntrySource.___stringlit_1).
  - pose proof handoff_initial_mode_info as INFO;rewrite handoff_loader_ge in INFO;exact INFO.
  - exact INITIAL.
  - reflexivity.
  - reflexivity.
  - unfold handoff_ge,handoff_symbol;vm_compute;reflexivity.
Qed.

Ltac handoff_initial_literal globvar :=
  eapply handoff_initial_string with(variable:=globvar);
  [assumption|unfold handoff_ge,handoff_symbol;vm_compute;reflexivity|reflexivity|
   reflexivity|unfold handoff_ge;vm_compute;reflexivity|
   vm_compute;repeat constructor;discriminate|
   vm_compute;lia || discriminate].

Lemma handoff_initial_literals initial : Genv.init_mem EntrySource.prog=Some initial ->
  Forall(fun literal=>c_string initial(handoff_global_address(fst literal))(snd literal))handoff_literal_bytes.
Proof.
  intros INITIAL;unfold handoff_literal_bytes;constructor.
  - handoff_initial_literal EntrySource.v___stringlit_1.
  - constructor.
    + handoff_initial_literal EntrySource.v___stringlit_111.
    + constructor.
      * handoff_initial_literal EntrySource.v___stringlit_112.
      * constructor.
        -- handoff_initial_literal EntrySource.v___stringlit_113.
        -- constructor.
           ++ handoff_initial_literal EntrySource.v___stringlit_114.
           ++ constructor.
Qed.

Definition handoff_fixture_global_names :=
  [EntrySource._run_uid;EntrySource._preflight;EntrySource._mode;EntrySource._policy__1;EntrySource._root_path]++map fst handoff_literal_bytes.
Lemma handoff_fixture_global_bindings : Forall
  (fun id=>Genv.find_symbol handoff_ge id=Some(handoff_symbol id))handoff_fixture_global_names.
Proof.
  unfold handoff_fixture_global_names,handoff_literal_bytes;cbn[map fst app];
    repeat constructor;unfold handoff_ge,handoff_symbol;vm_compute;reflexivity.
Qed.
Local Opaque handoff_ge handoff_symbol.
Lemma handoff_fixture_global_valid initial id : Genv.init_mem EntrySource.prog=Some initial ->
  In id handoff_fixture_global_names ->Mem.valid_block initial(handoff_symbol id).
Proof.
  intros INITIAL MEMBER;pose proof handoff_fixture_global_bindings as BINDINGS.
  rewrite Forall_forall in BINDINGS;pose proof(BINDINGS id MEMBER)as BINDING.
  rewrite handoff_loader_ge in BINDING.
  exact(@Genv.find_symbol_not_fresh Clight.fundef type EntrySource.prog id(handoff_symbol id)initial INITIAL BINDING).
Qed.
Lemma handoff_fixture_globals_separate left right :
  In left handoff_fixture_global_names ->In right handoff_fixture_global_names ->left<>right ->
  handoff_symbol left<>handoff_symbol right.
Proof.
  intros LEFT RIGHT DIFFERENT SAME;apply DIFFERENT.
  pose proof handoff_fixture_global_bindings as BINDINGS;rewrite Forall_forall in BINDINGS.
  eapply Genv.genv_vars_inj;[apply BINDINGS;exact LEFT|rewrite SAME;apply BINDINGS;exact RIGHT].
Qed.
Local Opaque handoff_ge handoff_symbol.

Lemma handoff_fixture_store_frame chunk before object offset value after :
  Mem.store chunk before object offset value=Some after ->
  Mem.unchanged_on(fun other _=>other<>object)before after.
Proof. intros STORE;eapply Mem.store_unchanged_on;[exact STORE|intros;congruence]. Qed.
Lemma handoff_fixture_bytes_frame before object offset values after :
  Mem.storebytes before object offset values=Some after ->
  Mem.unchanged_on(fun other _=>other<>object)before after.
Proof. intros STORE;eapply Mem.storebytes_unchanged_on;[exact STORE|intros;congruence]. Qed.
Lemma handoff_fixture_string_frame before after P pointer bytes :
  Mem.unchanged_on P before after ->(forall pos,P(address_block pointer)pos) ->
  c_string before pointer bytes ->c_string after pointer bytes.
Proof.
  intros FRAME SELECT[NONZERO[BOUNDS LOAD]];split;[exact NONZERO|]. split;[exact BOUNDS|].
  eapply Mem.loadbytes_unchanged_on;[exact FRAME|intros;apply SELECT|exact LOAD].
Qed.
Lemma handoff_fixture_load_frame before after P chunk object offset value :
  Mem.unchanged_on P before after ->(forall pos,P object pos) ->
  Mem.load chunk before object offset=Some value ->Mem.load chunk after object offset=Some value.
Proof. intros FRAME SELECT LOAD;eapply Mem.load_unchanged_on;[exact FRAME|intros;apply SELECT|exact LOAD]. Qed.
Lemma handoff_fixture_old_store base before chunk object offset value after :
  old_memory base before ->~Mem.valid_block base object ->
  Mem.store chunk before object offset value=Some after ->old_memory base after.
Proof.
  intros OLD FRESH STORE;eapply Mem.unchanged_on_trans;[exact OLD|].
  eapply Mem.unchanged_on_implies;[apply handoff_fixture_store_frame with(chunk:=chunk)(offset:=offset)(value:=value);exact STORE|].
  intros other pos VALID _ SAME;subst other;exact(FRESH VALID).
Qed.
Lemma handoff_fixture_old_bytes base before object offset values after :
  old_memory base before ->~Mem.valid_block base object ->
  Mem.storebytes before object offset values=Some after ->old_memory base after.
Proof.
  intros OLD FRESH STORE;eapply Mem.unchanged_on_trans;[exact OLD|].
  eapply Mem.unchanged_on_implies;[apply handoff_fixture_bytes_frame with(offset:=offset)(values:=values);exact STORE|].
  intros other pos VALID _ SAME;subst other;exact(FRESH VALID).
Qed.
Lemma handoff_fixture_old_access base after chunk object offset permission :
  old_memory base after ->Mem.valid_access base chunk object offset permission ->
  Mem.valid_access after chunk object offset permission.
Proof.
  intros OLD[PERMS ALIGN];split;[|exact ALIGN].
  intros pos BOUND;eapply Mem.perm_unchanged_on;[exact OLD| |apply PERMS;exact BOUND].
  eapply Mem.perm_valid_block;apply PERMS;exact BOUND.
Qed.

Lemma handoff_fixture_scalar_frame object before cells after : scalar_stores object before cells after ->
  Mem.unchanged_on(fun other _=>other<>object)before after.
Proof.
  intros STORES;induction STORES;[apply Mem.unchanged_on_refl|].
  eapply Mem.unchanged_on_trans;[eapply handoff_fixture_store_frame;exact H|exact IHSTORES].
Qed.
Lemma handoff_fixture_old_scalars base before object cells after :
  scalar_stores object before cells after ->old_memory base before ->~Mem.valid_block base object ->old_memory base after.
Proof.
  intros STORES;induction STORES;intros OLD FRESH;[exact OLD|].
  apply IHSTORES;[eapply handoff_fixture_old_store;eassumption|exact FRESH].
Qed.
Lemma handoff_fixture_scalar_access object before cells after chunk other offset permission :
  scalar_stores object before cells after ->Mem.valid_access before chunk other offset permission ->
  Mem.valid_access after chunk other offset permission.
Proof.
  intros STORES[PERMS ALIGN];split;[|exact ALIGN]. intros pos BOUND.
  apply(proj2(scalar_stores_permissions _ _ _ _ STORES _ _ _ _));apply PERMS;exact BOUND.
Qed.
Lemma handoff_fixture_stored_string before object bytes after :
  Mem.storebytes before object 0(map Byte(bytes++[Byte.zero]))=Some after ->
  Forall(fun byte=>byte<>Byte.zero)bytes ->Z.of_nat(length(bytes++[Byte.zero]))<=Int64.max_unsigned ->
  c_string after {|address_block:=object;address_offset:=0|}bytes.
Proof.
  intros STORE NONZERO BOUND;split;[exact NONZERO|]. split.
  - unfold span_bounds;cbn[address_offset]. split;[change(0<=0<18446744073709551616);lia|].
    split;[|exact BOUND]. change Ptrofs.modulus with 18446744073709551616.
    change Int64.max_unsigned with 18446744073709551615 in BOUND;lia.
  - pose proof(Mem.loadbytes_storebytes_same _ _ _ _ _ STORE)as LOAD.
    rewrite length_map in LOAD;exact LOAD.
Qed.
Definition handoff_fixture_command_bytes := map Byte.repr[47;98;105;110;47;115;104].
Definition handoff_fixture_root_bytes :=
  map Byte.repr[47;109;51;45;114;117;110;115;47;49;48;48;48;48;48;47;114;111;111;116].
Definition handoff_fixture_cells command :=
  [{|scalar_chunk:=Mptr;scalar_offset:=0;scalar_value:=Vptr command Ptrofs.zero|};
   {|scalar_chunk:=Mptr;scalar_offset:=8;scalar_value:=Vlong Int64.zero|}].
Lemma handoff_fixture_cells_valid command : Forall(scalar_valid 16)(handoff_fixture_cells command).
Proof.
  unfold handoff_fixture_cells;constructor.
  - split;[change(0<=0);lia|]. split;[change(0+8<=16);lia|change(8|0);apply Z.divide_0_r].
  - constructor.
    + split;[change(0<=8);lia|]. split;[change(8+8<=16);lia|change(8|8);apply Z.divide_refl].
    + constructor.
Qed.

Theorem handoff_fixture_private_memory before : exists cell command source after,
  ~Mem.valid_block before(tls_block cell) /\~Mem.valid_block before command /\~Mem.valid_block before source /\
  tls_block cell<>command /\tls_block cell<>source /\command<>source /\
  old_memory before after /\initialized_errno cell after Int.zero /\
  c_string after {|address_block:=command;address_offset:=0|}handoff_fixture_command_bytes /\
  Mem.load Mptr after source 0=Some(Vptr command Ptrofs.zero) /\
  Mem.load Mptr after source 8=Some(Vlong Int64.zero) /\Mem.weak_valid_pointer after command 0=true.
Proof.
  destruct(Mem.alloc before 0 4)as[m1 tlsb]eqn:A1.
  destruct(Mem.alloc m1 0 10)as[m2 command]eqn:A2.
  destruct(Mem.alloc m2 0 16)as[allocated source]eqn:A3.
  assert(CHAIN:local_allocations before[(tlsb,4);(command,10);(source,16)]allocated)
    by(econstructor;[exact A1|];econstructor;[exact A2|];econstructor;[exact A3|constructor]).
  pose proof(local_allocations_objects _ _ _ CHAIN)as OBJECTS.
  rewrite !Forall_cons_iff in OBJECTS;destruct OBJECTS as[[TLSFRESH TLSPERM][[COMMANDFRESH COMMANDPERM][[SOURCEFRESH SOURCEPERM]EMPTY]]].
  cbn[fst snd]in TLSFRESH,TLSPERM,COMMANDFRESH,COMMANDPERM,SOURCEFRESH,SOURCEPERM.
  assert(DISTINCT:tlsb<>command /\tlsb<>source /\command<>source).
  { pose proof(local_allocations_distinct _ _ _ CHAIN)as DISTINCT.
    change(NoDup[tlsb;command;source])in DISTINCT.
    inversion DISTINCT as[|a rest NOTTLS OTHER];subst.
    inversion OTHER as[|a rest NOTCMD LAST];subst;cbn in NOTTLS,NOTCMD;intuition congruence. }
  destruct DISTINCT as[TLSCOMMAND[TLSSOURCE COMMANDSOURCE]].
  assert(TLSACCESS:Mem.valid_access allocated Mint32 tlsb 0 Writable).
  { split;[intros pos RANGE;eapply Mem.perm_implies;[apply TLSPERM;exact RANGE|constructor]|change(4|0);apply Z.divide_0_r]. }
  destruct(Mem.valid_access_store allocated Mint32 tlsb 0(Vint Int.zero)TLSACCESS)as[tls_after TLSSTORE].
  assert(COMMANDACCESS:Mem.range_perm tls_after command 0
    (0+Z.of_nat(length(map Byte(handoff_fixture_command_bytes++[Byte.zero]))))Cur Writable).
  { intros pos RANGE;eapply Mem.perm_store_1;[exact TLSSTORE|].
    eapply Mem.perm_implies;[apply COMMANDPERM;change(0<=pos<8)in RANGE;lia|constructor]. }
  destruct(Mem.range_perm_storebytes tls_after command 0(map Byte(handoff_fixture_command_bytes++[Byte.zero]))COMMANDACCESS)
    as[command_after COMMANDSTORE].
  assert(SOURCEACCESS:Mem.range_perm command_after source 0 16 Cur Freeable).
  { intros pos RANGE;eapply Mem.perm_storebytes_1;[exact COMMANDSTORE|].
    eapply Mem.perm_store_1;[exact TLSSTORE|apply SOURCEPERM;exact RANGE]. }
  destruct(scalar_stores_exist source 16(handoff_fixture_cells command)command_after
    (handoff_fixture_cells_valid command)SOURCEACCESS)as[after SOURCESTORES].
  pose proof(handoff_fixture_scalar_frame _ _ _ _ SOURCESTORES)as SOURCEFRAME.
  pose proof(handoff_fixture_bytes_frame _ _ _ _ _ COMMANDSTORE)as COMMANDFRAME.
  assert(OLD:old_memory before after).
  { eapply handoff_fixture_old_scalars;[exact SOURCESTORES| |exact SOURCEFRESH].
    eapply handoff_fixture_old_bytes;[|exact COMMANDFRESH|exact COMMANDSTORE].
    eapply handoff_fixture_old_store;[eapply local_allocations_unchanged;exact CHAIN|exact TLSFRESH|exact TLSSTORE]. }
  assert(ERRNO:initialized_errno {|tls_block:=tlsb;tls_offset:=0|}after Int.zero).
  { split;[change(0<=0);lia|]. split;[change(0+4<=18446744073709551616);lia|]. split.
    - eapply handoff_fixture_scalar_access;[exact SOURCESTORES|].
      eapply Mem.storebytes_valid_access_1;[exact COMMANDSTORE|].
      eapply Mem.store_valid_access_1;[exact TLSSTORE|exact TLSACCESS].
    - change(Mem.load Mint32 after tlsb 0=Some(Vint Int.zero)).
      eapply handoff_fixture_load_frame;[exact SOURCEFRAME|intros;congruence|].
      eapply handoff_fixture_load_frame;[exact COMMANDFRAME|intros;congruence|].
      eapply Mem.load_store_same with(v:=Vint Int.zero);exact TLSSTORE. }
  assert(TEXT:c_string after {|address_block:=command;address_offset:=0|}handoff_fixture_command_bytes).
  { eapply handoff_fixture_string_frame;[exact SOURCEFRAME|intros;cbn;congruence|].
    eapply handoff_fixture_stored_string;[exact COMMANDSTORE| |change(8<=18446744073709551615);lia].
    vm_compute;repeat constructor;discriminate. }
  assert(HEAD:Mem.load Mptr after source 0=Some(Vptr command Ptrofs.zero)).
  { exact(scalar_stores_fields _ _ _ _ SOURCESTORES
      (scalar_orderedb_sound(handoff_fixture_cells command)eq_refl)
      {|scalar_chunk:=Mptr;scalar_offset:=0;scalar_value:=Vptr command Ptrofs.zero|}(or_introl eq_refl)). }
  assert(NULL:Mem.load Mptr after source 8=Some(Vlong Int64.zero)).
  { exact(scalar_stores_fields _ _ _ _ SOURCESTORES
      (scalar_orderedb_sound(handoff_fixture_cells command)eq_refl)
      {|scalar_chunk:=Mptr;scalar_offset:=8;scalar_value:=Vlong Int64.zero|}(or_intror(or_introl eq_refl))). }
  exists {|tls_block:=tlsb;tls_offset:=0|},command,source,after.
  split;[exact TLSFRESH|]. split;[exact COMMANDFRESH|]. split;[exact SOURCEFRESH|].
  split;[exact TLSCOMMAND|]. split;[exact TLSSOURCE|]. split;[exact COMMANDSOURCE|].
  split;[exact OLD|]. split;[exact ERRNO|]. split;[exact TEXT|]. split;[exact HEAD|]. split;[exact NULL|].
  unfold Mem.weak_valid_pointer;apply orb_true_iff;left;apply Mem.valid_pointer_nonempty_perm.
  destruct TEXT as[_[_ LOAD]];eapply Mem.perm_implies.
  - eapply Mem.loadbytes_range_perm;[exact LOAD|change(0<=0<8);lia].
  - constructor.
Qed.

Lemma handoff_fixture_old_perm base after object offset kind permission :
  old_memory base after ->Mem.perm base object offset kind permission ->Mem.perm after object offset kind permission.
Proof.
  intros OLD PERM;eapply Mem.perm_unchanged_on;[exact OLD|eapply Mem.perm_valid_block;exact PERM|exact PERM].
Qed.
Definition handoff_fixture_shared object (_:Z) :=
  object<>handoff_symbol EntrySource._run_uid /\object<>handoff_symbol EntrySource._root_path /\
  object<>handoff_symbol EntrySource._policy__1.
Lemma handoff_fixture_readonly id : In id handoff_fixture_global_names ->
  id<>EntrySource._run_uid ->id<>EntrySource._root_path ->id<>EntrySource._policy__1 ->
  forall pos,handoff_fixture_shared(handoff_symbol id)pos.
Proof.
  intros MEMBER UID ROOT POLICY pos;repeat split;eapply handoff_fixture_globals_separate;
    try assumption;unfold handoff_fixture_global_names;cbn;auto 8.
Qed.
Lemma handoff_fixture_literals_readonly : Forall
  (fun literal=>fst literal<>EntrySource._run_uid /\fst literal<>EntrySource._root_path /\fst literal<>EntrySource._policy__1)
  handoff_literal_bytes.
Proof. unfold handoff_literal_bytes;repeat constructor;discriminate. Qed.
Definition handoff_fixture_input command source : HandoffBorrowed :=
  {|handoff_borrowed_uid:=Int.repr 100000;handoff_borrowed_preflight:=Int.zero;
    handoff_borrowed_mode:=handoff_global_address EntrySource.___stringlit_1;
    handoff_borrowed_mode_bytes:=handoff_normal_bytes;
    handoff_borrowed_source:=source;handoff_borrowed_source_offset:=Ptrofs.zero;
    handoff_borrowed_arguments:=[(command,Ptrofs.zero)];
    handoff_borrowed_argument_bytes:=[handoff_fixture_command_bytes];
    handoff_borrowed_root_bytes:=handoff_fixture_root_bytes|}.
Ltac handoff_fixture_global := unfold handoff_fixture_global_names,handoff_literal_bytes;cbn;intuition congruence.

Theorem handoff_actual_input_memory_owned initial : Genv.init_mem EntrySource.prog=Some initial ->
  exists cell command source locals uid_after root_after before,
    ~Mem.valid_block initial(tls_block cell) /\~Mem.valid_block initial command /\
    ~Mem.valid_block initial source /\old_memory initial locals /\
    Mem.store Mint32 locals(handoff_symbol EntrySource._run_uid)0(Vint(Int.repr 100000))=Some uid_after /\
    Mem.storebytes uid_after(handoff_symbol EntrySource._root_path)0
      (map Byte(handoff_fixture_root_bytes++[Byte.zero]))=Some root_after /\
    Mem.store Mptr root_after(handoff_symbol EntrySource._policy__1)88(Vptr source Ptrofs.zero)=Some before /\
    handoff_borrowed_input cell before(handoff_fixture_input command source).
Proof.
  intros INITIAL.
  destruct(handoff_fixture_private_memory initial)as[cell[command[source[locals
    [TLSFRESH[COMMANDFRESH[SOURCEFRESH[TLSCOMMAND[TLSSOURCE[COMMANDSOURCE[OLD[ERRNO[TEXT[HEAD[NULL WEAK]]]]]]]]]]]]]]].
  assert(PRIVATE:forall object,In object[tls_block cell;command;source] ->
    forall id,In id handoff_fixture_global_names ->object<>handoff_symbol id).
  { intros object MEMBER id GLOBAL SAME.
    assert(VALID:Mem.valid_block initial(handoff_symbol id))by(eapply handoff_fixture_global_valid;eassumption).
    rewrite <- SAME in VALID;cbn in MEMBER;destruct MEMBER as[EQ|[EQ|[EQ|NONE]]];
      [subst object;exact(TLSFRESH VALID)|subst object;exact(COMMANDFRESH VALID)|subst object;exact(SOURCEFRESH VALID)|contradiction]. }
  assert(PRIVATESELECT:forall object,In object[tls_block cell;command;source] ->forall pos,handoff_fixture_shared object pos).
  { intros object MEMBER pos;repeat split;(apply PRIVATE;[exact MEMBER|handoff_fixture_global]). }
  assert(UIDACCESS:Mem.valid_access locals Mint32(handoff_symbol EntrySource._run_uid)0 Writable)
    by(eapply handoff_fixture_old_access;[exact OLD|apply handoff_initial_uid_access;exact INITIAL]).
  destruct(Mem.valid_access_store locals Mint32(handoff_symbol EntrySource._run_uid)0(Vint(Int.repr 100000))UIDACCESS)
    as[uid_after UIDSTORE].
  assert(ROOTACCESS:Mem.range_perm uid_after(handoff_symbol EntrySource._root_path)0 21 Cur Writable).
  { intros pos RANGE;eapply Mem.perm_store_1;[exact UIDSTORE|].
    eapply handoff_fixture_old_perm;[exact OLD|apply(handoff_initial_root_access _ INITIAL);lia]. }
  destruct(Mem.range_perm_storebytes uid_after(handoff_symbol EntrySource._root_path)0
    (map Byte(handoff_fixture_root_bytes++[Byte.zero]))ROOTACCESS)as[root_after ROOTSTORE].
  assert(POLICYACCESS:Mem.valid_access root_after Mptr(handoff_symbol EntrySource._policy__1)88 Writable).
  { eapply Mem.storebytes_valid_access_1;[exact ROOTSTORE|].
    eapply Mem.store_valid_access_1;[exact UIDSTORE|].
    eapply handoff_fixture_old_access;[exact OLD|apply handoff_initial_policy_access;exact INITIAL]. }
  destruct(Mem.valid_access_store root_after Mptr(handoff_symbol EntrySource._policy__1)88(Vptr source Ptrofs.zero)POLICYACCESS)
    as[before POLICYSTORE].
  assert(FRAME:Mem.unchanged_on handoff_fixture_shared locals before).
  { eapply Mem.unchanged_on_trans.
    - eapply Mem.store_unchanged_on;[exact UIDSTORE|]. intros pos RANGE[UID[ROOT POLICY]];contradiction.
    - eapply Mem.unchanged_on_trans.
      + eapply Mem.storebytes_unchanged_on;[exact ROOTSTORE|]. intros pos RANGE[UID[ROOT POLICY]];contradiction.
      + eapply Mem.store_unchanged_on;[exact POLICYSTORE|]. intros pos RANGE[UID[ROOT POLICY]];contradiction. }
  assert(PERMS:forall object pos kind permission,Mem.perm locals object pos kind permission ->Mem.perm before object pos kind permission).
  { intros object pos kind permission PERM;eapply Mem.perm_store_1;[exact POLICYSTORE|].
    eapply Mem.perm_storebytes_1;[exact ROOTSTORE|]. eapply Mem.perm_store_1;[exact UIDSTORE|exact PERM]. }
  pose proof(handoff_fixture_bytes_frame _ _ _ _ _ ROOTSTORE)as ROOTFRAME.
  pose proof(handoff_fixture_store_frame _ _ _ _ _ _ POLICYSTORE)as POLICYFRAME.
  assert(GLOBALNOTTLS:forall id,In id handoff_fixture_global_names ->handoff_symbol id<>tls_block cell).
  { intros id MEMBER SAME;apply(PRIVATE(tls_block cell)ltac:(cbn;auto)id MEMBER);symmetry;exact SAME. }
  assert(UIDROOT:handoff_symbol EntrySource._run_uid<>handoff_symbol EntrySource._root_path)
    by(apply handoff_fixture_globals_separate;[handoff_fixture_global|handoff_fixture_global|discriminate]).
  assert(UIDPOLICY:handoff_symbol EntrySource._run_uid<>handoff_symbol EntrySource._policy__1)
    by(apply handoff_fixture_globals_separate;[handoff_fixture_global|handoff_fixture_global|discriminate]).
  assert(ROOTPOLICY:handoff_symbol EntrySource._root_path<>handoff_symbol EntrySource._policy__1)
    by(apply handoff_fixture_globals_separate;[handoff_fixture_global|handoff_fixture_global|discriminate]).
  exists cell,command,source,locals,uid_after,root_after,before.
  split;[exact TLSFRESH|]. split;[exact COMMANDFRESH|]. split;[exact SOURCEFRESH|].
  split;[exact OLD|]. split;[exact UIDSTORE|]. split;[exact ROOTSTORE|]. split;[exact POLICYSTORE|].
  constructor.
  - exists Int.zero;destruct ERRNO as[LOW[HIGH[ACCESS LOAD]]];split;[exact LOW|]. split;[exact HIGH|]. split.
    + destruct ACCESS as[RANGE ALIGN];split;[intros pos BOUND;apply PERMS;apply RANGE;exact BOUND|exact ALIGN].
    + eapply handoff_fixture_load_frame;[exact FRAME|apply PRIVATESELECT;cbn;auto|exact LOAD].
  - unfold handoff_borrowed_blocks,handoff_fixture_input;cbn[handoff_borrowed_mode handoff_borrowed_source
      handoff_borrowed_arguments address_block];unfold handoff_literal_bytes;cbn[map fst app].
    repeat constructor;try(solve[apply GLOBALNOTTLS;handoff_fixture_global]);congruence.
  - change(Mem.load Mint32 before(handoff_symbol EntrySource._run_uid)0=Some(Vint(Int.repr 100000))).
    eapply handoff_fixture_load_frame;[exact POLICYFRAME|intros;exact UIDPOLICY|].
    eapply handoff_fixture_load_frame;[exact ROOTFRAME|intros;exact UIDROOT|].
    eapply Mem.load_store_same with(v:=Vint(Int.repr 100000));exact UIDSTORE.
  - change(Mem.load Mint32 before(handoff_symbol EntrySource._preflight)0=Some(Vint Int.zero)).
    eapply handoff_fixture_load_frame;[exact FRAME|apply handoff_fixture_readonly;[handoff_fixture_global|discriminate|discriminate|discriminate]|].
    eapply old_memory_load;[exact OLD|exact(handoff_initial_preflight_value _ INITIAL)].
  - change(Mem.load Mptr before(handoff_symbol EntrySource._mode)0=
      Some(address_value(handoff_global_address EntrySource.___stringlit_1))).
    eapply handoff_fixture_load_frame;[exact FRAME|apply handoff_fixture_readonly;[handoff_fixture_global|discriminate|discriminate|discriminate]|].
    eapply old_memory_load;[exact OLD|exact(handoff_initial_mode_value _ INITIAL)].
  - eapply handoff_fixture_string_frame;[exact FRAME| |].
    + cbn[handoff_fixture_input handoff_borrowed_mode address_block];apply handoff_fixture_readonly;[handoff_fixture_global|discriminate|discriminate|discriminate].
    + eapply old_memory_string;[exact OLD|].
      pose proof(handoff_initial_literals _ INITIAL)as LITERALS;inversion LITERALS;subst;exact H1.
  - eapply handoff_fixture_string_frame;[exact POLICYFRAME|intros;exact ROOTPOLICY|].
    eapply handoff_fixture_stored_string;[exact ROOTSTORE| |change(21<=18446744073709551615);lia].
    vm_compute;repeat constructor;discriminate.
  - change(Mem.load Mptr before(handoff_symbol EntrySource._policy__1)88=Some(Vptr source Ptrofs.zero)).
    eapply Mem.load_store_same with(v:=Vptr source Ptrofs.zero);exact POLICYSTORE.
  - change(1<=64)%nat;lia.
  - change(Mem.load Mptr before source 0=Some(Vptr command Ptrofs.zero) /\
      Mem.weak_valid_pointer before command 0=true /\Mem.load Mptr before source 8=Some(Vlong Int64.zero)).
    split.
    + eapply handoff_fixture_load_frame;[exact FRAME|apply PRIVATESELECT;cbn;auto|exact HEAD].
    + split;[eapply handoff_permissions_weak;[exact PERMS|exact WEAK]|].
      eapply handoff_fixture_load_frame;[exact FRAME|apply PRIVATESELECT;cbn;auto|exact NULL].
  - constructor;[|constructor].
    eapply handoff_fixture_string_frame;[exact FRAME|apply PRIVATESELECT;cbn;auto|exact TEXT].
  - pose proof(handoff_initial_literals _ INITIAL)as LITERALS.
    pose proof handoff_fixture_literals_readonly as READONLY.
    rewrite Forall_forall in LITERALS,READONLY|-*;intros literal MEMBER.
    destruct(READONLY literal MEMBER)as[UID[ROOT POLICY]].
    eapply handoff_fixture_string_frame;[exact FRAME| |].
    + cbn[handoff_global_address address_block];apply handoff_fixture_readonly;try assumption.
      unfold handoff_fixture_global_names;apply in_or_app;right;apply in_map;exact MEMBER.
    + eapply old_memory_string;[exact OLD|apply LITERALS;exact MEMBER].
Qed.

Theorem handoff_actual_input_memory_fresh initial : Genv.init_mem EntrySource.prog=Some initial ->
  exists cell command source locals uid_after root_after before,
    ~Mem.valid_block initial(tls_block cell) /\old_memory initial locals /\
    Mem.store Mint32 locals(handoff_symbol EntrySource._run_uid)0(Vint(Int.repr 100000))=Some uid_after /\
    Mem.storebytes uid_after(handoff_symbol EntrySource._root_path)0
      (map Byte(handoff_fixture_root_bytes++[Byte.zero]))=Some root_after /\
    Mem.store Mptr root_after(handoff_symbol EntrySource._policy__1)88(Vptr source Ptrofs.zero)=Some before /\
    handoff_borrowed_input cell before(handoff_fixture_input command source).
Proof.
  intro INITIAL.
  destruct(handoff_actual_input_memory_owned _ INITIAL)
    as[cell[command[source[locals[uid_after[root_after[before[TLS[COMMAND[SOURCE REST]]]]]]]]]].
  exists cell,command,source,locals,uid_after,root_after,before;split;assumption.
Qed.

Theorem handoff_actual_input_memory initial : Genv.init_mem EntrySource.prog=Some initial ->
  exists cell command source locals uid_after root_after before,
    old_memory initial locals /\
    Mem.store Mint32 locals(handoff_symbol EntrySource._run_uid)0(Vint(Int.repr 100000))=Some uid_after /\
    Mem.storebytes uid_after(handoff_symbol EntrySource._root_path)0
      (map Byte(handoff_fixture_root_bytes++[Byte.zero]))=Some root_after /\
    Mem.store Mptr root_after(handoff_symbol EntrySource._policy__1)88(Vptr source Ptrofs.zero)=Some before /\
    handoff_borrowed_input cell before(handoff_fixture_input command source).
Proof.
  intro INITIAL.
  destruct(handoff_actual_input_memory_fresh _ INITIAL)as[cell[command[source[locals[uid_after[root_after[before[FRESH REST]]]]]]]].
  exists cell,command,source,locals,uid_after,root_after,before;exact REST.
Qed.


Theorem handoff_actual_input_exists : exists initial cell input before,
  Genv.init_mem EntrySource.prog=Some initial /\handoff_borrowed_input cell before input /\
  handoff_borrowed_mode_bytes input=handoff_normal_bytes /\handoff_borrowed_uid input=Int.repr 100000.
Proof.
  destruct handoff_actual_initial_memory_exists as[initial INITIAL].
  destruct(handoff_actual_input_memory initial INITIAL)as[cell[command[source[locals[uid_after[root_after[before
    [OLD[UIDSTORE[ROOTSTORE[POLICYSTORE INPUT]]]]]]]]]]].
  exists initial,cell,(handoff_fixture_input command source),before;split;[exact INITIAL|].
  split;[exact INPUT|]. split;reflexivity.
Qed.
