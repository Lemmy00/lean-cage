(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Fixed launch vectors come from actual source stores in separately allocated arrays. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayExchangeEntry GatewayStackAllocation GatewayPrefix
  GatewaySpawnProcess GatewayRegistry GatewayGlobals GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Fixpoint gateway_find_local_initialization (identifier : ident) (body : statement) : option statement :=
  match body with
  | Ssequence first rest =>
      match first with
      | Sassign (Evar actual _) _ => if Pos.eqb identifier actual then Some body else
          match gateway_find_local_initialization identifier first with
          | Some found => Some found | None => gateway_find_local_initialization identifier rest end
      | _ => match gateway_find_local_initialization identifier first with
          | Some found => Some found | None => gateway_find_local_initialization identifier rest end
      end
  | _ => None
  end.

Definition spawn_vector_start := Eval vm_compute in
  match gateway_find_local_initialization _child (fn_body f_host_exchange) with
  | Some found => found | None => Sskip end.

Fixpoint spawn_vector_after (count : nat) : statement :=
  match count with
  | O => spawn_vector_start
  | S previous => match spawn_vector_after previous with Ssequence _ rest => rest | _ => Sskip end
  end.

Definition spawn_vector_assignment index :=
  match spawn_vector_after index with Ssequence first _ => first | _ => Sskip end.
Definition spawn_vector_rhs index :=
  match spawn_vector_assignment index with Sassign _ expression => expression | _ => Econst_int Int.zero tint end.
Definition spawn_vector_literal index :=
  match spawn_vector_rhs index with Evar identifier _ => identifier | _ => _child end.

Definition spawn_array_cell identifier count index :=
  Ederef (Ebinop Oadd (Evar identifier (tarray (tptr tschar) count))
    (Econst_int (Int.repr index) tint) (tptr (tptr tschar))) (tptr tschar).

Theorem actual_spawn_vector_structure :
  spawn_vector_assignment 0 = Sassign (Evar _child tint) (Econst_int Int.zero tint) /\
  spawn_vector_assignment 1 = Sassign (spawn_array_cell _arguments 2 0) (Evar _host_engine (tarray tschar 4096)) /\
  spawn_vector_assignment 2 = Sassign (spawn_array_cell _arguments 2 1)
    (Ecast (Econst_int Int.zero tint) (tptr tvoid)) /\
  spawn_vector_assignment 3 = Sassign (spawn_array_cell _environment 3 0)
    (Evar (spawn_vector_literal 3) (tarray tschar 19)) /\
  spawn_vector_assignment 4 = Sassign (spawn_array_cell _environment 3 1)
    (Evar (spawn_vector_literal 4) (tarray tschar 9)) /\
  spawn_vector_assignment 5 = Sassign (spawn_array_cell _environment 3 2)
    (Ecast (Econst_int Int.zero tint) (tptr tvoid)).
Proof. repeat split; reflexivity. Qed.

Definition spawn_path_bytes := map Byte.repr [80;65;84;72;61;47;117;115;114;47;98;105;110;58;47;98;105;110].
Definition spawn_locale_bytes := map Byte.repr [76;67;95;65;76;76;61;67].

Theorem actual_spawn_environment_literals :
  (exists variable, gateway_program_definition (spawn_vector_literal 3) global_definitions = Some (Gvar variable) /\
    gvar_readonly variable = true /\ registered_string variable (map Byte.unsigned spawn_path_bytes)) /\
  (exists variable, gateway_program_definition (spawn_vector_literal 4) global_definitions = Some (Gvar variable) /\
    gvar_readonly variable = true /\ registered_string variable (map Byte.unsigned spawn_locale_bytes)).
Proof. split; eexists; repeat split; reflexivity. Qed.

Lemma spawn_array_reference ge environment temporaries memory identifier count object :
  environment ! identifier = Some (object, tarray (tptr tschar) count) ->
  expression_value ge environment temporaries memory (Evar identifier (tarray (tptr tschar) count))
    (Vptr object Ptrofs.zero).
Proof.
  intro LOCAL; eapply location_read_value; [apply local_location_value; exact LOCAL |].
  apply deref_loc_reference; reflexivity.
Qed.

Lemma spawn_array_location ge environment temporaries memory identifier count object index :
  environment ! identifier = Some (object, tarray (tptr tschar) count) -> 0 <= index <= 2 ->
  location_value ge environment temporaries memory (spawn_array_cell identifier count index)
    object (Ptrofs.repr (8 * index)).
Proof.
  intros LOCAL BOUND; apply pointer_location_value; eapply binary_expression_value.
  - apply spawn_array_reference; exact LOCAL.
  - apply old_expression_value; constructor.
  - assert (index = 0 \/ index = 1 \/ index = 2) by lia.
    destruct H as [SAME | [SAME | SAME]]; subst index; reflexivity.
Qed.

Lemma spawn_array_store_edge ge function environment temporaries memory after identifier count object index
    expression value continuation :
  environment ! identifier = Some (object, tarray (tptr tschar) count) -> 0 <= index <= 2 ->
  expression_value ge environment temporaries memory expression value ->
  sem_cast value (typeof expression) (tptr tschar) memory = Some value ->
  Mem.store Mptr memory object (8 * index) value = Some after ->
  store_edge ge (State function (Sassign (spawn_array_cell identifier count index) expression)
      continuation environment temporaries memory)
    (State function Sskip continuation environment temporaries after).
Proof.
  intros LOCAL BOUND VALUE CAST STORE.
  eapply assignment_source_edge with (b := object) (ofs := Ptrofs.repr (8 * index)) (v := value) (w := value).
  - apply spawn_array_location; assumption.
  - exact VALUE.
  - exact CAST.
  - eapply assign_loc_value; [reflexivity |].
    unfold Mem.storev.
    rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite zle_true by (change (8 * index + 8 <= 18446744073709551616); lia).
    exact STORE.
Qed.

Theorem actual_exchange_entry_owns_spawn_vectors ge before environment after :
  exchange_stack_buffers ge before environment after ->
  exists child arguments variables,
    environment ! _child = Some (child, tint) /\
    environment ! _arguments = Some (arguments, tarray (tptr tschar) 2) /\
    environment ! _environment = Some (variables, tarray (tptr tschar) 3) /\
    child <> arguments /\ child <> variables /\ arguments <> variables /\
    Mem.range_perm after child 0 4 Cur Freeable /\
    Mem.range_perm after arguments 0 16 Cur Freeable /\
    Mem.range_perm after variables 0 24 Cur Freeable.
Proof.
  intros [BUFFERS [[LIVE DISTINCT] FRAME]].
  destruct (BUFFERS _child tint ltac:(cbn; auto 14)) as [child [CHILD [FRESH_CHILD CHILD_ACCESS]]].
  destruct (BUFFERS _arguments (tarray (tptr tschar) 2) ltac:(cbn; auto 14))
    as [arguments [ARGUMENTS [FRESH_ARGUMENTS ARGUMENT_ACCESS]]].
  destruct (BUFFERS _environment (tarray (tptr tschar) 3) ltac:(cbn; auto 14))
    as [variables [VARIABLES [FRESH_VARIABLES VARIABLE_ACCESS]]].
  exists child, arguments, variables; split; [exact CHILD |]. split; [exact ARGUMENTS |]. split; [exact VARIABLES |].
  split; [eapply DISTINCT; [exact CHILD | exact ARGUMENTS | discriminate] |].
  split; [eapply DISTINCT; [exact CHILD | exact VARIABLES | discriminate] |].
  split; [eapply DISTINCT; [exact ARGUMENTS | exact VARIABLES | discriminate] |].
  split; [exact CHILD_ACCESS |]. split; [exact ARGUMENT_ACCESS | exact VARIABLE_ACCESS].
Qed.
