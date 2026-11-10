(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real native callee allocates its own API output cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess ReceiverAllocation.
From HostGateway Require Import GatewaySource GatewayPython.
Import ListNotations.
Open Scope Z_scope.

Record field_arguments := {
  field_target : Values.val;
  field_object : Values.val;
  field_kind : int;
  field_maximum : int64
}.

Definition field_values arguments :=
  [field_target arguments;field_object arguments;Vint(field_kind arguments);Vlong(field_maximum arguments)].

Definition field_parameters arguments :=
  PTree.set _maximum (Vlong(field_maximum arguments))
  (PTree.set _kind (Vint(field_kind arguments))
  (PTree.set _object (field_object arguments)
  (PTree.set _field (field_target arguments) (create_undef_temps(fn_temps f_host_field_bytes))))).

Record field_locals := {
  field_local_data : block;
  field_local_size : block
}.

Definition field_environment locals :=
  PTree.set _size (field_local_size locals,tlong)
    (PTree.set _data (field_local_data locals,tptr tschar) empty_env).

Definition field_allocations before locals after :=
  exists middle,
    Mem.alloc before 0 8=(middle,field_local_data locals) /\
    Mem.alloc middle 0 8=(after,field_local_size locals).

Lemma field_allocation_chain before locals after :
  field_allocations before locals after ->
  local_allocations before [(field_local_data locals,8);(field_local_size locals,8)] after.
Proof. intros[middle[A B]];econstructor;[exact A|];econstructor;[exact B|constructor]. Qed.

Lemma field_function_entry ge before locals after arguments :
  field_allocations before locals after ->
  function_entry2 ge f_host_field_bytes (field_values arguments) before
    (field_environment locals) (field_parameters arguments) after.
Proof.
  intros[middle[A B]]. constructor.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros a b LEFT RIGHT.
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst a;
      repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst b;discriminate.
  - unfold field_environment;cbn[fn_vars].
    econstructor;[exact A|]. econstructor;[exact B|constructor].
  - reflexivity.
Qed.

Theorem actual_field_entry_allocates ge before arguments k :
  exists locals after,
    store_edge ge
      (Callstate(Internal f_host_field_bytes)(field_values arguments)k before)
      (State f_host_field_bytes(fn_body f_host_field_bytes)k
        (field_environment locals)(field_parameters arguments)after) /\
    field_allocations before locals after /\
    Mem.unchanged_on(fun _ _ => True)before after /\
    ~Mem.valid_block before(field_local_data locals) /\
    ~Mem.valid_block before(field_local_size locals) /\
    field_local_data locals <> field_local_size locals /\
    Mem.range_perm after(field_local_data locals)0 8 Cur Freeable /\
    Mem.range_perm after(field_local_size locals)0 8 Cur Freeable.
Proof.
  destruct(Mem.alloc before 0 8)as[middle data]eqn:A.
  destruct(Mem.alloc middle 0 8)as[after size]eqn:B.
  set(locals:={|field_local_data:=data;field_local_size:=size|}).
  assert(ALLOC:field_allocations before locals after)by(exists middle;auto).
  pose proof(field_allocation_chain _ _ _ ALLOC)as CHAIN.
  pose proof(local_allocations_objects _ _ _ CHAIN)as OBJECTS.
  inversion OBJECTS as[|? ? DATA TAIL];subst.
  inversion TAIL as[|? ? SIZE REST];subst.
  pose proof(local_allocations_distinct _ _ _ CHAIN)as DISTINCT.
  cbn in DATA,SIZE,DISTINCT.
  inversion DISTINCT as[|? ? NOTIN DUP];subst.
  exists locals,after;split.
  - apply function_entry_source_edge,field_function_entry;exact ALLOC.
  - split;[exact ALLOC|].
    split;[eapply local_allocations_unchanged;exact CHAIN|].
    split;[exact(proj1 DATA)|].
    split;[exact(proj1 SIZE)|].
    split;[intro SAME;apply NOTIN;cbn;auto|].
    split;[exact(proj2 DATA)|exact(proj2 SIZE)].
Qed.

Theorem actual_field_locals_are_runtime_private world before locals after :
  python_world_valid world before -> field_allocations before locals after ->
  ~python_runtime_owned world(field_local_data locals) /\
  ~python_runtime_owned world(field_local_size locals).
Proof.
  intros[_[_[VALID _]]] ALLOC.
  pose proof(local_allocations_objects _ _ _(field_allocation_chain _ _ _ ALLOC))as OBJECTS.
  inversion OBJECTS as[|? ? DATA TAIL];subst.
  inversion TAIL as[|? ? SIZE REST];subst.
  split;intro OWN;[apply(proj1 DATA)|apply(proj1 SIZE)];apply VALID;exact OWN.
Qed.
