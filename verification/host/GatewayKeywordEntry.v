(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Recover the parser's real fresh local storage from its actual call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCalls GatewayFunctionEntry GatewayStackAllocation
  GatewayThreadRuntime GatewayLocalRuntime GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Record gateway_keyword_arguments:={
  keyword_positional_object:val;
  keyword_dictionary_object:val;
  keyword_format_pointer:val;
  keyword_names_pointer:val;
  keyword_field_count:int;
  keyword_required_count:int;
  keyword_only_flag:int;
  keyword_output_pointer:val
}.

Definition keyword_argument_values arguments:=
  [keyword_positional_object arguments;keyword_dictionary_object arguments;keyword_format_pointer arguments;
   keyword_names_pointer arguments;Vint(keyword_field_count arguments);Vint(keyword_required_count arguments);
   Vint(keyword_only_flag arguments);keyword_output_pointer arguments].

Definition keyword_parameters arguments:=
  PTree.set _outputs(keyword_output_pointer arguments)
    (PTree.set _keyword_only(Vint(keyword_only_flag arguments))
      (PTree.set _required(Vint(keyword_required_count arguments))
        (PTree.set _count(Vint(keyword_field_count arguments))
          (PTree.set _names__6(keyword_names_pointer arguments)
            (PTree.set _format(keyword_format_pointer arguments)
              (PTree.set _keywords(keyword_dictionary_object arguments)
                (PTree.set _args(keyword_positional_object arguments)(create_undef_temps(fn_temps f_host_parse_objects))))))))).

Lemma keyword_entry_canonical ge arguments before environment temporaries allocated:
  function_entry2 ge f_host_parse_objects(keyword_argument_values arguments)before environment temporaries allocated->
  temporaries=keyword_parameters arguments /\
    alloc_variables ge empty_env before(fn_vars f_host_parse_objects)environment allocated.
Proof.
  intro ENTRY;inversion ENTRY;subst.
  match goal with BIND:bind_parameter_temps _ _ _=Some temporaries|-_=>
    change(Some(keyword_parameters arguments)=Some temporaries)in BIND;inversion BIND;subst end.
  split;[reflexivity|assumption].
Qed.

Lemma actual_keyword_variables_unique:list_norepet(map fst(fn_vars f_host_parse_objects)).
Proof. repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil. Qed.

Definition keyword_stack_buffers ge before environment after:Prop:=
  (forall identifier ty,In(identifier,ty)(fn_vars f_host_parse_objects)->
    exists object,environment!identifier=Some(object,ty) /\~Mem.valid_block before object /\
      Mem.range_perm after object 0(sizeof ge ty)Cur Freeable) /\
    gateway_stack_environment after environment /\Mem.unchanged_on(fun _ _=>True)before after.

Lemma actual_keyword_allocations ge before environment after:
  alloc_variables ge empty_env before(fn_vars f_host_parse_objects)environment after->
  keyword_stack_buffers ge before environment after.
Proof.
  intro ALLOC;split.
  - intros identifier ty MEMBER;eapply gateway_alloc_variables_member;
      [exact ALLOC|exact actual_keyword_variables_unique|exact MEMBER].
  - split;[eapply gateway_alloc_variables_stack;[exact ALLOC|apply gateway_empty_stack_environment]|].
    eapply gateway_alloc_variables_frame;exact ALLOC.
Qed.

Theorem actual_keyword_entry_owns_seen ge before environment after:
  keyword_stack_buffers ge before environment after->
  exists seen,environment!_seen=Some(seen,tarray tuchar 14) /\~Mem.valid_block before seen /\
    Mem.range_perm after seen 0 14 Cur Freeable /\
    (forall caller,Mem.valid_block before caller->caller<>seen).
Proof.
  intros[BUFFERS[STACK FRAME]].
  destruct(BUFFERS _seen(tarray tuchar 14)ltac:(cbn;auto))as[seen[LOOK[FRESH PERMISSIONS]]].
  exists seen;split;[exact LOOK|]. split;[exact FRESH|]. split;[exact PERMISSIONS|].
  intros caller LIVE SAME;subst caller;contradiction.
Qed.

Section Entry.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

Theorem actual_keyword_source_allocates ge arguments before world events returned after next:
  discipline None before world->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_parse_objects)(keyword_argument_values arguments)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  exists prefix suffix called current environment allocated,
    events=prefix++gateway_source Events.E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_parse_objects)(keyword_argument_values arguments)Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_parse_objects)(keyword_argument_values arguments)Kstop called)current) /\
    keyword_stack_buffers ge called environment allocated /\discipline None allocated current /\
    gateway_native_environment native_private current allocated environment /\
    gateway_steps backend ge
      (gateway_live(State f_host_parse_objects(fn_body f_host_parse_objects)Kstop environment
        (keyword_parameters arguments)allocated)current)suffix
      (gateway_live(Returnstate returned Kstop after)next).
Proof.
  intros SIDE RUN.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_parse_objects(keyword_argument_values arguments)
    Kstop before world events returned Kstop after next RUN)
    as(prefix & suffix & called & current & environment & temporaries & allocated &
      EVENTS & AMBIENT & PREFIX & ENTRY & REST).
  assert(CALLED:discipline None called current).
  { eapply gateway_ambient_run_ready with(source:=Callstate(Internal f_host_parse_objects)
      (keyword_argument_values arguments)Kstop before).
    - intros original source changed target READY INTERFERENCE.
      exact(proj1(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ READY INTERFERENCE)).
    - exact SIDE.
    - exact AMBIENT.
    - exact PREFIX. }
  destruct(keyword_entry_canonical ge arguments called environment temporaries allocated ENTRY)as[TEMPS ALLOC].
  subst temporaries.
  destruct(gateway_native_alloc_variables backend io native_private stable_readonly discipline thread_errno runtime ge None
    empty_env called(fn_vars f_host_parse_objects)environment allocated current ALLOC CALLED
    (gateway_native_environment_empty native_private current called))as[ALLOCATED NATIVE].
  exists prefix,suffix,called,current,environment,allocated.
  split;[exact EVENTS|]. split;[exact AMBIENT|]. split;[exact PREFIX|].
  split;[apply actual_keyword_allocations;exact ALLOC|]. split;[exact ALLOCATED|]. split;assumption.
Qed.

End Entry.
