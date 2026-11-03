(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.connection: Runtime producers supply primitive effects, not reporting conclusions. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import IO Machine Library ProcessEffects LibraryMachine LibraryControl ReportingTrace RuntimeProgram.
Import ListNotations.
Local Open Scope Z_scope.

(* Each constructor states a single library operation independently of the
   calling routine and its eventual result. Addresses remain CompCert pointers. *)
Inductive primitive_return (cell : tls) :
 Clight.fundef -> list val -> mem -> library_event -> val -> mem -> Prop :=
| primitive_io : forall q m reply after,
 errno_block q=tls_block cell -> errno_offset q=tls_offset cell ->
 io_return q m reply after ->
 primitive_return cell
   (External (io_function(operation q)) [tint;tptr tvoid;tulong] tlong cc_default)
   (request_args q) m (original_event(io_step q reply)) (Vlong(returned reply)) after
| primitive_errno : forall m,
 0<=tls_offset cell -> tls_offset cell+4<=Ptrofs.modulus ->
 Mem.valid_access m Mint32 (tls_block cell) (tls_offset cell) Writable ->
 primitive_return cell (External errno_function [] (tptr tint) cc_default) [] m
   (original_event errno_step) (Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell))) m
| primitive_strcmp : forall m left right value,
 strcmp_result m left right value ->
 primitive_return cell strcmp_definition [address_value left;address_value right] m
   (strcmp_returned left right value) (Vint value) m
| primitive_memcmp : forall m left right count value,
 memcmp_result m left right count value ->
 primitive_return cell memcmp_definition (comparison_args left right count) m
   (memcmp_returned left right count value) (Vint value) m
| primitive_memcpy : forall m source destination bytes after,
 copy_result m source destination bytes after ->
 primitive_return cell memcpy_definition (copy_args source destination bytes) m
   (memcpy_returned source destination bytes) (address_value destination) after
| primitive_close : forall m fd reply after,
 close_effect cell m reply after ->
 primitive_return cell close_definition [Vint fd] m
   (close_returned fd reply) (Vint(close_value reply)) after.

Definition trace_bytes (observe : Events.event -> list Byte.int) (t : trace) :=
 flat_map observe t.

(* Restrict the primitive contract to calls actually reachable from the owned
   source entry. This neither constrains unrelated helper functions nor forces
   one private TLS address to serve every possible memory/injection world. *)
Record runtime_contract (ge : Clight.genv) (cell : tls)
 (observe : Events.event -> list Byte.int) (initial : Clight.state) : Prop := {
 runtime_errno_root : errno_root ge(tls_block cell)(tls_offset cell);
 runtime_sound : forall prefix ef types result_type convention args k before trace result after,
   library_steps ge cell (live initial) prefix
     (live(Callstate(External ef types result_type convention) args k before)) ->
   external_call ef (Genv.to_senv ge) args before trace result after ->
   exists event,
     primitive_return cell (External ef types result_type convention) args before event result after /\
     trace_bytes observe trace=reporting_bytes event;
 runtime_progress : forall prefix ef types result_type convention args k before,
   library_steps ge cell (live initial) prefix
     (live(Callstate(External ef types result_type convention) args k before)) ->
   exists trace value final,
     external_call ef (Genv.to_senv ge) args before trace value final
}.

Lemma primitive_source_step ge cell def args before event result after k :
 primitive_return cell def args before event result after ->
 library_step ge cell (live(Callstate def args k before)) event
   (live(Returnstate result k after)).
Proof.
 intro EFFECT;inversion EFFECT;subst.
 - apply original_step;eapply effect;[constructor;assumption|eassumption].
 - apply original_step;apply errno_address;assumption.
 - apply strcmp_step;assumption.
 - apply memcmp_step;assumption.
 - apply memcpy_step;assumption.
 - apply close_step;assumption.
Qed.

Lemma trace_bytes_app observe first rest :
 trace_bytes observe(first**rest)=trace_bytes observe first++trace_bytes observe rest.
Proof. apply flat_map_app. Qed.
