(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.machine: Actual internal Clight steps, explicit external/loss boundary. *)
From Coq Require Import ZArith List String Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events
  Ctypes Ctypesdefs Clight.
Require Import Slice IO.
Import ListNotations.
Open Scope Z_scope.

Record tls := { tls_block : block; tls_offset : Z }.

Definition io_function (op : direction) :=
  EF_external (match op with reading => "read" | writing => "write" end)
    (mksignature [Xint; Xptr; Xlong] Xlong cc_default).

Definition errno_function := EF_external "__errno_location"
  (mksignature [] Xptr cc_default).

Definition request_args (q : request) :=
  [Vint (descriptor q); Vptr (buffer_block q) (Ptrofs.repr (buffer_offset q));
   Vlong (Int64.repr (requested q))].

Inductive boundary (cell : tls) : Clight.state -> request -> Prop :=
| at_io : forall q k m,
    errno_block q = tls_block cell -> errno_offset q = tls_offset cell ->
    boundary cell
      (Callstate (External (io_function (operation q))
        [tint; tptr tvoid; tulong] tlong cc_default) (request_args q) k m) q.

Definition internal_state (s : Clight.state) : Prop :=
  match s with
  | Callstate (External _ _ _ _) _ _ _ => False
  | State _ (Sbuiltin _ _ _ _) _ _ _ _ => False
  | _ => True
  end.

Inductive machine := live (s : Clight.state) | dead (m : mem).
Inductive event :=
| source_step (t : trace)
| io_step (q : request) (r : reply)
| errno_step
| wait_step
| loss_step
| partial_loss (q : request) (bytes : list Byte.int) (error : option int).

Definition memory_of (s : Clight.state) : mem :=
  match s with State _ _ _ _ _ m | Callstate _ _ _ m | Returnstate _ _ m => m end.

Inductive step (ge : genv) (cell : tls) : machine -> event -> machine -> Prop :=
| internal : forall s t s',
    internal_state s -> step2 ge s t s' ->
    step ge cell (live s) (source_step t) (live s')
| effect : forall q k m r m',
    boundary cell
      (Callstate (External (io_function (operation q))
        [tint; tptr tvoid; tulong] tlong cc_default) (request_args q) k m) q ->
    io_return q m r m' ->
    step ge cell
      (live (Callstate (External (io_function (operation q))
        [tint; tptr tvoid; tulong] tlong cc_default) (request_args q) k m))
      (io_step q r) (live (Returnstate (Vlong (returned r)) k m'))
| errno_address : forall k m,
    0 <= tls_offset cell -> tls_offset cell + 4 <= Ptrofs.modulus ->
    Mem.valid_access m Mint32 (tls_block cell) (tls_offset cell) Writable ->
    step ge cell
      (live (Callstate (External errno_function [] (tptr tint) cc_default) [] k m))
      errno_step
      (live (Returnstate (Vptr (tls_block cell) (Ptrofs.repr (tls_offset cell))) k m))
| waiting : forall s q,
    boundary cell s q -> owned q (memory_of s) ->
    step ge cell (live s) wait_step (live s)
| lose : forall s, step ge cell (live s) loss_step (dead (memory_of s))
| lose_during_io : forall q k m bytes error m',
    boundary cell
      (Callstate (External (io_function (operation q))
        [tint; tptr tvoid; tulong] tlong cc_default) (request_args q) k m) q ->
    io_return q m (transfer bytes error) m' ->
    step ge cell
      (live (Callstate (External (io_function (operation q))
        [tint; tptr tvoid; tulong] tlong cc_default) (request_args q) k m))
      (partial_loss q bytes error) (dead m').

Theorem no_stock_external_bypass : forall ge cell ef ts ty cc args k m t target,
  ~ step ge cell (live (Callstate (External ef ts ty cc) args k m))
      (source_step t) target.
Proof. intros ge cell ef ts ty cc args k m t target H; inversion H; subst; contradiction. Qed.

Theorem internal_steps_are_actual : forall ge cell s t s',
  step ge cell (live s) (source_step t) (live s') -> step2 ge s t s'.
Proof. intros; inversion H; subst; assumption. Qed.

Theorem no_stock_builtin_bypass : forall ge cell f opt ef args values k e le m t target,
  ~ step ge cell (live (State f (Sbuiltin opt ef args values) k e le m))
      (source_step t) target.
Proof. intros ge cell f opt ef args values k e le m t target H; inversion H; subst; contradiction. Qed.

Theorem internal_steps_are_silent : forall ge cell s t s',
  step ge cell (live s) (source_step t) (live s') -> t = E0.
Proof.
  intros ge cell s t s' H. inversion H; subst.
  match goal with H : step2 _ _ _ _ |- _ => inversion H; subst; try reflexivity end;
    contradiction.
Qed.

Theorem loss_at_every_boundary : forall ge cell s,
  step ge cell (live s) loss_step (dead (memory_of s)).
Proof. intros; constructor. Qed.

Theorem dead_cannot_resume : forall ge cell m e target,
  ~ step ge cell (dead m) e target.
Proof. intros ge cell m e target H; inversion H. Qed.

Theorem partial_loss_never_returns : forall ge cell s q bytes error target,
  step ge cell (live s) (partial_loss q bytes error) target ->
  exists m', target = dead m'.
Proof. intros; inversion H; subst; eauto. Qed.

Theorem source_loss_before_first_write : forall ge cell e le m,
  step ge cell (live (State f_write_all (fn_body f_write_all) Kstop e le m))
    loss_step (dead m).
Proof. intros; constructor. Qed.

Theorem io_step_return_bounds : forall ge cell s q r target,
  step ge cell (live s) (io_step q r) target ->
  Int64.signed (returned r) = -1 \/
    0 <= Int64.signed (returned r) <= requested q.
Proof. intros; inversion H; subst; eapply return_bounds; eauto. Qed.

Inductive steps (ge : genv) (cell : tls) : machine -> list event -> machine -> Prop :=
| steps_nil : forall s, steps ge cell s [] s
| steps_cons : forall s e mid rest last,
    step ge cell s e mid -> steps ge cell mid rest last ->
    steps ge cell s (e :: rest) last.

Theorem arbitrary_blocked_prefix : forall ge cell s q n,
  boundary cell s q -> owned q (memory_of s) ->
  steps ge cell (live s) (repeat wait_step n ++ [loss_step])
    (dead (memory_of s)).
Proof.
  intros ge cell s q n B O. induction n; simpl.
  - econstructor; [constructor|constructor].
  - econstructor; [eapply waiting; eauto|exact IHn].
Qed.

(* These equations are checked against the regenerated maintained-source AST.
   They identify the call sites; they are not a whole-function simulation. *)
Fixpoint direct_calls (s : statement) : list ident :=
  match s with
  | Scall _ (Evar id _) _ => [id]
  | Ssequence a b | Sloop a b => direct_calls a ++ direct_calls b
  | Sifthenelse _ a b => direct_calls a ++ direct_calls b
  | _ => []
  end.

Theorem write_all_calls_identified :
  direct_calls (fn_body f_write_all) = [_write; ___errno_location].
Proof. reflexivity. Qed.

Theorem terminal_receiver_calls_identified :
  direct_calls (fn_body f_m4_collect_failure) =
    [_read; ___errno_location; _close; _get32; _get32; _get32; _get32; _get32; _get32;
     _result_of; _result_of; _result_of; _result_of].
Proof. reflexivity. Qed.

Definition source_definition (id : ident) :=
  find (fun item => Pos.eqb (fst item) id) (prog_defs Slice.prog).

Theorem source_write_signature : source_definition _write =
  Some (_write, Gfun (External (io_function writing)
    [tint; tptr tvoid; tulong] tlong cc_default)).
Proof. reflexivity. Qed.

Theorem source_read_signature : source_definition _read =
  Some (_read, Gfun (External (io_function reading)
    [tint; tptr tvoid; tulong] tlong cc_default)).
Proof. reflexivity. Qed.

Theorem source_errno_signature : source_definition ___errno_location =
  Some (___errno_location, Gfun (External errno_function [] (tptr tint) cc_default)).
Proof. reflexivity. Qed.

Theorem allocated_partial_read_loss : forall ge (bytes : list Byte.int),
  Z.of_nat (length bytes) = 2 ->
  exists cell q m after k,
    requested q = 4 /\
    step ge cell
      (live (Callstate (External (io_function reading)
        [tint; tptr tvoid; tulong] tlong cc_default) (request_args q) k m))
      (partial_loss q bytes None) (dead after) /\
    Mem.loadbytes after (buffer_block q) (buffer_offset q) 2 = Some (map Byte bytes).
Proof.
  intros ge bytes LENGTH.
  destruct owned_read_inhabited as [q [m [OWN [READ COUNT]]]].
  destruct (read_transfer_exists q m bytes OWN READ) as [after EFFECT]; [lia|].
  exists {| tls_block := errno_block q; tls_offset := errno_offset q |}, q, m, after, Kstop.
  split; [exact COUNT|]. split.
  - rewrite <- READ. eapply lose_during_io; [constructor; reflexivity|exact EFFECT].
  - rewrite <- LENGTH. eapply read_exact_bytes; eauto.
Qed.
