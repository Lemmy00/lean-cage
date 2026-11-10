(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Public run/check wrappers preserve caller arguments and select exact modes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayRegistry.
Import ListNotations.
Open Scope Z_scope.

Definition workspace_wrapper(run:bool):=if run then f_host_workspace_run else f_host_workspace_check.
Definition workspace_pointer_type:=snd(hd(_self,tvoid)(fn_params f_host_workspace_run)).
Definition py_object_pointer:=tptr(Tstruct __object noattr).
Definition wrapper_values(self arguments keywords:Values.val):=[self;arguments;keywords].
Definition wrapper_parameters run self arguments keywords:=
  PTree.set _keywords keywords(PTree.set _args arguments(PTree.set _self self
    (create_undef_temps(fn_temps(workspace_wrapper run))))).
Definition wrapper_call run:=
  match fn_body(workspace_wrapper run)with Ssequence call _=>call|_=>Sskip end.
Definition wrapper_after run:=
  match fn_body(workspace_wrapper run)with Ssequence _ rest=>rest|_=>Sskip end.
Definition wrapper_function_expression:=Evar _host_workspace_execute
  (Tfunction[workspace_pointer_type;py_object_pointer;py_object_pointer;tint]py_object_pointer cc_default).
Definition wrapper_forward_arguments(run:bool):=
  [Etempvar _self workspace_pointer_type;Etempvar _args py_object_pointer;
   Etempvar _keywords py_object_pointer;Econst_int(if run then Int.one else Int.zero)tint].
Lemma wrapper_call_body run:
  wrapper_call run=Scall(Some _t'1)wrapper_function_expression(wrapper_forward_arguments run).
Proof. destruct run;reflexivity. Qed.
Definition wrapper_cont run self arguments keywords k:=
  Kcall(Some _t'1)(workspace_wrapper run)empty_env(wrapper_parameters run self arguments keywords)
    (Kseq(wrapper_after run)k).
Definition python_nullable_pointer value:=
  (exists block offset,value=Vptr block offset) \/value=Vlong Int64.zero.

Ltac wrapper_lookup :=
  unfold wrapper_parameters;
  repeat first[rewrite PTree.gss|rewrite PTree.gso by discriminate];reflexivity.

Lemma wrapper_function_entry ge memory run self arguments keywords :
  function_entry2 ge(workspace_wrapper run)(wrapper_values self arguments keywords)memory
    empty_env(wrapper_parameters run self arguments keywords)memory.
Proof.
  destruct run;constructor.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros a b LEFT RIGHT.
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst a;
      repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst b;discriminate.
  - constructor.
  - reflexivity.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros a b LEFT RIGHT.
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst a;
      repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst b;discriminate.
  - constructor.
  - reflexivity.
Qed.

Theorem actual_wrapper_forwards_call (ge:Clight.genv) memory run self selfOffset arguments argsOffset
    keywords k symbol :
  python_nullable_pointer keywords ->
  Genv.find_symbol ge _host_workspace_execute=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_workspace_execute) ->
  store_edge ge
    (State(workspace_wrapper run)(wrapper_call run)(Kseq(wrapper_after run)k)empty_env
      (wrapper_parameters run(Vptr self selfOffset)(Vptr arguments argsOffset)keywords)memory)
    (Callstate(Internal f_host_workspace_execute)
      [Vptr self selfOffset;Vptr arguments argsOffset;keywords;Vint(if run then Int.one else Int.zero)]
      (wrapper_cont run(Vptr self selfOffset)(Vptr arguments argsOffset)keywords k)memory).
Proof.
  intros NULLABLE SYMBOL FUNCTION.
  rewrite wrapper_call_body;unfold wrapper_cont.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero)
    (types:=[workspace_pointer_type;py_object_pointer;py_object_pointer;tint])
    (ty:=py_object_pointer)(cc:=cc_default).
  - reflexivity.
  - apply old_expression_value;eapply value_function;
      [reflexivity|exact SYMBOL|reflexivity].
  - unfold wrapper_forward_arguments.
    eapply cons_argument_values with(v:=Vptr self selfOffset);
      [apply old_expression_value;apply value_temp;wrapper_lookup|reflexivity|].
    eapply cons_argument_values with(v:=Vptr arguments argsOffset);
      [apply old_expression_value;apply value_temp;wrapper_lookup|reflexivity|].
    eapply cons_argument_values with(v:=keywords);
      [apply old_expression_value;apply value_temp;wrapper_lookup| |].
    + destruct NULLABLE as[[block[offset SAME]]|SAME];subst keywords;reflexivity.
    + eapply cons_argument_values;
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_public_wrapper_entry (ge:Clight.genv) memory run self selfOffset arguments argsOffset
    keywords k symbol :
  python_nullable_pointer keywords ->
  Genv.find_symbol ge _host_workspace_execute=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_workspace_execute) ->
  store_path ge(fun _=>True)
    (Callstate(Internal(workspace_wrapper run))
      [Vptr self selfOffset;Vptr arguments argsOffset;keywords]k memory)3
    (Callstate(Internal f_host_workspace_execute)
      [Vptr self selfOffset;Vptr arguments argsOffset;keywords;Vint(if run then Int.one else Int.zero)]
      (wrapper_cont run(Vptr self selfOffset)(Vptr arguments argsOffset)keywords k)memory).
Proof.
  intros NULLABLE SYMBOL FUNCTION.
  eapply store_next;[exact I|apply function_entry_source_edge,wrapper_function_entry|].
  assert(BODY:fn_body(workspace_wrapper run)=Ssequence(wrapper_call run)(wrapper_after run)).
  { destruct run;reflexivity. }
  rewrite BODY.
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|apply actual_wrapper_forwards_call with(symbol:=symbol);assumption|].
  constructor;exact I.
Qed.
