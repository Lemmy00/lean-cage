(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Only the guarded source owns direct class-root stores. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib AST Ctypes Clight.
From HostGateway Require Import GatewaySource.
Import ListNotations.

Fixpoint initialization_has_statement (selected : statement -> bool) (body : statement) : bool :=
  selected body || match body with
  | Ssequence first rest | Sifthenelse _ first rest | Sloop first rest =>
      initialization_has_statement selected first || initialization_has_statement selected rest
  | Sswitch _ cases => initialization_has_cases selected cases
  | Slabel _ following => initialization_has_statement selected following
  | _ => false
  end
with initialization_has_cases (selected : statement -> bool) (cases : labeled_statements) : bool :=
  match cases with
  | LSnil => false
  | LScons _ body rest => initialization_has_statement selected body || initialization_has_cases selected rest
  end.

Definition initialization_direct_call identifier body := match body with
  | Scall _ (Evar target (Tfunction _ _ _)) _ => Pos.eqb identifier target
  | _ => false end.

Definition initialization_direct_store (identifiers : list ident) body := match body with
  | Sassign (Evar target _) _ => existsb (Pos.eqb target) identifiers
  | _ => false end.

Definition initialization_source_functions (selected : statement -> bool) : list ident :=
  map fst (filter (fun definition => match snd definition with
    | Gfun (Internal function) => initialization_has_statement selected (fn_body function)
    | _ => false end) global_definitions).

Theorem actual_initialization_only_direct_caller :
  initialization_source_functions (initialization_direct_call _host_initialize) = [_PyInit__host].
Proof. vm_compute; reflexivity. Qed.

Theorem actual_initialization_only_direct_class_writer :
  initialization_source_functions
    (initialization_direct_store [_host_path_class; _host_cancellation_class; _host_outcome_class]) =
    [_host_initialize].
Proof. vm_compute; reflexivity. Qed.

Theorem actual_initialization_only_direct_flag_writer :
  initialization_source_functions (initialization_direct_store [_host_initializing; _host_initialized]) =
    [_PyInit__host].
Proof. vm_compute; reflexivity. Qed.

Theorem initialization_selected_function_member selected identifier function :
  In (identifier, Gfun (Internal function)) global_definitions ->
  initialization_has_statement selected (fn_body function) = true ->
  In identifier (initialization_source_functions selected).
Proof.
  intros DEFINITION SELECTED; apply in_map_iff.
  exists (identifier, Gfun (Internal function)); split; [reflexivity |].
  apply filter_In; split; [exact DEFINITION |exact SELECTED].
Qed.

Theorem initialization_direct_class_store_owner identifier function :
  In (identifier, Gfun (Internal function)) global_definitions ->
  initialization_has_statement
    (initialization_direct_store [_host_path_class; _host_cancellation_class; _host_outcome_class])
    (fn_body function) = true -> identifier = _host_initialize.
Proof.
  intros DEFINITION STORE.
  pose proof (initialization_selected_function_member _ _ _ DEFINITION STORE) as OWNER.
  rewrite actual_initialization_only_direct_class_writer in OWNER.
  destruct OWNER as [SAME |EMPTY]; [symmetry; exact SAME |contradiction].
Qed.
