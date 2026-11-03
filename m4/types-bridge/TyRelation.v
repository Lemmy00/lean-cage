(* §AR-m4-routes.reporting.types: Total codecs for the two actual type representations. *)
From Stdlib Require Import ZArith NArith PeanoNat List Lia.
From LeanImport Require Import Lean.
Require Import TypePrefix TypeRecursors StmtPrefix.
From compcert.cfrontend Require Import Ctypes.
Local Close Scope lean_scope.
Local Close Scope Nat_scope.

Definition bool_out (b : Bool) : bool :=
 match b with Bool_false => false | Bool_true => true end.
Definition bool_in (b : bool) : Bool :=
 match b with false => Bool_false | true => Bool_true end.
Lemma bool_in_out b : bool_in (bool_out b) = b.
Proof. destruct b; reflexivity. Qed.
Lemma bool_out_in b : bool_out (bool_in b) = b.
Proof. destruct b; reflexivity. Qed.

Fixpoint positive_out (p : CC_Positive) : positive :=
 match p with
 | CC_Positive_xH => xH
 | CC_Positive_xO p => xO (positive_out p)
 | CC_Positive_xI p => xI (positive_out p)
 end.
Fixpoint positive_in (p : positive) : CC_Positive :=
 match p with
 | xH => CC_Positive_xH
 | xO p => CC_Positive_xO (positive_in p)
 | xI p => CC_Positive_xI (positive_in p)
 end.
Lemma positive_in_out p : positive_in (positive_out p) = p.
Proof. induction p; cbn; congruence. Qed.
Lemma positive_out_in p : positive_out (positive_in p) = p.
Proof. induction p; cbn; congruence. Qed.

Lemma natural_in_out n : Nat_of_N (N_of_Nat n) = n.
Proof. unfold Nat_of_N, N_of_Nat; rewrite Nat2N.id; apply Nat2natid. Qed.
Lemma natural_out_in n : N_of_Nat (Nat_of_N n) = n.
Proof. unfold Nat_of_N, N_of_Nat; rewrite nat2Natid; apply N2Nat.id. Qed.

Definition integer_out (z : Int) : Z :=
 match z with
 | Int_ofNat n => Z.of_N (N_of_Nat n)
 | Int_negSucc n => (- Z.of_N (N.succ (N_of_Nat n)))%Z
 end.
Definition integer_in (z : Z) : Int :=
 match z with
 | Z0 => Int_ofNat Nat_zero
 | Zpos p => Int_ofNat (Nat_of_N (Npos p))
 | Zneg p => Int_negSucc (Nat_of_N (N.pred (Npos p)))
 end.
Lemma integer_in_out z : integer_in (integer_out z) = z.
Proof.
 destruct z as [n|n]; cbn [integer_out].
 - unfold integer_in; destruct (N_of_Nat n) eqn:H; cbn.
   + f_equal; rewrite <- (natural_in_out n), H; reflexivity.
   + f_equal; change (Nat_of_N (Npos p) = n); rewrite <- H; apply natural_in_out.
 - unfold integer_in; destruct (N.succ (N_of_Nat n)) eqn:H; cbn.
   + exfalso; exact (N.neq_succ_0 _ H).
   + f_equal; change (Nat_of_N (N.pred (Npos p)) = n).
     rewrite <- H, N.pred_succ, natural_in_out; reflexivity.
Qed.
Lemma integer_out_in z : integer_out (integer_in z) = z.
Proof.
 destruct z as [|p|p]; cbn [integer_in integer_out].
 - reflexivity.
 - now rewrite natural_out_in.
 - rewrite natural_out_in, N.succ_pred_pos; reflexivity.
Qed.

Definition option_out {A B} (f : A -> B) (o : Option_inst1 A) : option B :=
 match o with Option_none_inst1 _ => None | Option_some_inst1 _ a => Some (f a) end.
Definition option_in {A B} (f : A -> B) (o : option A) : Option_inst1 B :=
 match o with None => Option_none_inst1 B | Some a => Option_some_inst1 B (f a) end.
Lemma option_in_out {A B} (f : A -> B) (g : B -> A)
 (H : forall a, g (f a) = a) o : option_in g (option_out f o) = o.
Proof. destruct o; cbn; [reflexivity|now rewrite H]. Qed.
Lemma option_out_in {A B} (f : A -> B) (g : B -> A)
 (H : forall a, g (f a) = a) o : option_out g (option_in f o) = o.
Proof. destruct o; cbn; [now rewrite H|reflexivity]. Qed.

Definition attr_out (a : CC_Attr) : Ctypes.attr :=
 match a with CC_Attr_mk v align =>
 Ctypes.mk_attr (bool_out v) (option_out N_of_Nat align) end.
Definition attr_in (a : Ctypes.attr) : CC_Attr :=
 match a with Ctypes.mk_attr v align =>
 CC_Attr_mk (bool_in v) (option_in Nat_of_N align) end.
Lemma attr_in_out a : attr_in (attr_out a) = a.
Proof.
 destruct a as [v align].
 change (CC_Attr_mk (bool_in (bool_out v))
  (option_in Nat_of_N (option_out N_of_Nat align)) = CC_Attr_mk v align).
 rewrite bool_in_out, option_in_out; auto using natural_in_out.
Qed.
Lemma attr_out_in a : attr_out (attr_in a) = a.
Proof.
 destruct a as [v align].
 change (Ctypes.mk_attr (bool_out (bool_in v))
  (option_out N_of_Nat (option_in Nat_of_N align)) = Ctypes.mk_attr v align).
 rewrite bool_out_in, option_out_in; auto using natural_out_in.
Qed.

Definition cc_out (cc : CC_CallConv) : AST.calling_convention :=
 match cc with CC_CallConv_mk vararg unproto ret =>
 AST.mkcallconv (option_out integer_out vararg) (bool_out unproto) (bool_out ret) end.
Definition cc_in (cc : AST.calling_convention) : CC_CallConv :=
 match cc with AST.mkcallconv vararg unproto ret =>
 CC_CallConv_mk (option_in integer_in vararg) (bool_in unproto) (bool_in ret) end.
Lemma cc_in_out cc : cc_in (cc_out cc) = cc.
Proof.
 destruct cc as [vararg unproto ret].
 change (CC_CallConv_mk (option_in integer_in (option_out integer_out vararg))
  (bool_in (bool_out unproto)) (bool_in (bool_out ret)) = CC_CallConv_mk vararg unproto ret).
 rewrite !bool_in_out, option_in_out; auto using integer_in_out.
Qed.
Lemma cc_out_in cc : cc_out (cc_in cc) = cc.
Proof.
 destruct cc as [vararg unproto ret].
 change (AST.mkcallconv (option_out integer_out (option_in integer_in vararg))
  (bool_out (bool_in unproto)) (bool_out (bool_in ret)) = AST.mkcallconv vararg unproto ret).
 rewrite !bool_out_in, option_out_in; auto using integer_out_in.
Qed.

Definition intsize_out (v : CC_IntSize) : Ctypes.intsize :=
 match v with
 | CC_IntSize_I8 => Ctypes.I8
 | CC_IntSize_I16 => Ctypes.I16
 | CC_IntSize_I32 => Ctypes.I32
 | CC_IntSize_IBool => Ctypes.IBool
 end.
Definition intsize_in (v : Ctypes.intsize) : CC_IntSize :=
 match v with
 | Ctypes.I8 => CC_IntSize_I8
 | Ctypes.I16 => CC_IntSize_I16
 | Ctypes.I32 => CC_IntSize_I32
 | Ctypes.IBool => CC_IntSize_IBool
 end.
Lemma intsize_in_out v : intsize_in (intsize_out v) = v.
Proof. destruct v; reflexivity. Qed.
Lemma intsize_out_in v : intsize_out (intsize_in v) = v.
Proof. destruct v; reflexivity. Qed.

Definition signedness_out (v : CC_Signedness) : Ctypes.signedness :=
 match v with
 | CC_Signedness_Signed => Ctypes.Signed
 | CC_Signedness_Unsigned => Ctypes.Unsigned
 end.
Definition signedness_in (v : Ctypes.signedness) : CC_Signedness :=
 match v with
 | Ctypes.Signed => CC_Signedness_Signed
 | Ctypes.Unsigned => CC_Signedness_Unsigned
 end.
Lemma signedness_in_out v : signedness_in (signedness_out v) = v.
Proof. destruct v; reflexivity. Qed.
Lemma signedness_out_in v : signedness_out (signedness_in v) = v.
Proof. destruct v; reflexivity. Qed.

Definition floatsize_out (v : CC_FloatSize) : Ctypes.floatsize :=
 match v with
 | CC_FloatSize_F32 => Ctypes.F32
 | CC_FloatSize_F64 => Ctypes.F64
 end.
Definition floatsize_in (v : Ctypes.floatsize) : CC_FloatSize :=
 match v with
 | Ctypes.F32 => CC_FloatSize_F32
 | Ctypes.F64 => CC_FloatSize_F64
 end.
Lemma floatsize_in_out v : floatsize_in (floatsize_out v) = v.
Proof. destruct v; reflexivity. Qed.
Lemma floatsize_out_in v : floatsize_out (floatsize_in v) = v.
Proof. destruct v; reflexivity. Qed.

Fixpoint type_out (t : CC_Ty) : Ctypes.type :=
 match t with
 | CC_Ty_Tvoid => Ctypes.Tvoid
 | CC_Ty_Tint sz sg a => Ctypes.Tint (intsize_out sz) (signedness_out sg) (attr_out a)
 | CC_Ty_Tlong sg a => Ctypes.Tlong (signedness_out sg) (attr_out a)
 | CC_Ty_Tfloat sz a => Ctypes.Tfloat (floatsize_out sz) (attr_out a)
 | CC_Ty_Tpointer t a => Ctypes.Tpointer (type_out t) (attr_out a)
 | CC_Ty_Tarray t sz a => Ctypes.Tarray (type_out t) (integer_out sz) (attr_out a)
 | CC_Ty_Tfunction args ret cc =>
   let fix out_args (xs : List_inst1 CC_Ty) : list Ctypes.type :=
    match xs with
    | List_nil_inst1 _ => nil
    | List_cons_inst1 _ head tail => cons (type_out head) (out_args tail)
    end in
   Ctypes.Tfunction (out_args args) (type_out ret) (cc_out cc)
 | CC_Ty_Tstruct id a => Ctypes.Tstruct (positive_out id) (attr_out a)
 | CC_Ty_Tunion id a => Ctypes.Tunion (positive_out id) (attr_out a)
 end.
Fixpoint types_out (xs : List_inst1 CC_Ty) : list Ctypes.type :=
 match xs with
 | List_nil_inst1 _ => nil
 | List_cons_inst1 _ head tail => cons (type_out head) (types_out tail)
 end.
Fixpoint type_in (t : Ctypes.type) : CC_Ty :=
 match t with
 | Ctypes.Tvoid => CC_Ty_Tvoid
 | Ctypes.Tint sz sg a => CC_Ty_Tint (intsize_in sz) (signedness_in sg) (attr_in a)
 | Ctypes.Tlong sg a => CC_Ty_Tlong (signedness_in sg) (attr_in a)
 | Ctypes.Tfloat sz a => CC_Ty_Tfloat (floatsize_in sz) (attr_in a)
 | Ctypes.Tpointer t a => CC_Ty_Tpointer (type_in t) (attr_in a)
 | Ctypes.Tarray t sz a => CC_Ty_Tarray (type_in t) (integer_in sz) (attr_in a)
 | Ctypes.Tfunction args ret cc =>
   let fix in_args (xs : list Ctypes.type) : List_inst1 CC_Ty :=
    match xs with
    | nil => List_nil_inst1 CC_Ty
    | cons head tail => List_cons_inst1 CC_Ty (type_in head) (in_args tail)
    end in
   CC_Ty_Tfunction (in_args args) (type_in ret) (cc_in cc)
 | Ctypes.Tstruct id a => CC_Ty_Tstruct (positive_in id) (attr_in a)
 | Ctypes.Tunion id a => CC_Ty_Tunion (positive_in id) (attr_in a)
 end.
Fixpoint types_in (xs : list Ctypes.type) : List_inst1 CC_Ty :=
 match xs with
 | nil => List_nil_inst1 CC_Ty
 | cons head tail => List_cons_inst1 CC_Ty (type_in head) (types_in tail)
 end.

Lemma source_type_roundtrip : forall t, type_in (type_out t) = t.
Proof.
 apply (@StmtPrefix.CC_Ty_rec_checked
   (fun t => type_in (type_out t) = t)
   (fun xs => types_in (types_out xs) = xs)).
 - reflexivity.
 - intros; cbn [type_out type_in].
   now rewrite intsize_in_out, signedness_in_out, attr_in_out.
 - intros; cbn [type_out type_in]; now rewrite signedness_in_out, attr_in_out.
 - intros; cbn [type_out type_in]; now rewrite floatsize_in_out, attr_in_out.
 - intros child a IH; change (CC_Ty_Tpointer (type_in (type_out child)) (attr_in (attr_out a)) = CC_Ty_Tpointer child a).
   now rewrite IH, attr_in_out.
 - intros child sz a IH; change (CC_Ty_Tarray (type_in (type_out child)) (integer_in (integer_out sz)) (attr_in (attr_out a)) = CC_Ty_Tarray child sz a).
   now rewrite IH, integer_in_out, attr_in_out.
 - intros xs ret cc IHxs IHret.
   change (CC_Ty_Tfunction (types_in (types_out xs)) (type_in (type_out ret)) (cc_in (cc_out cc)) = CC_Ty_Tfunction xs ret cc).
   now rewrite IHxs, IHret, cc_in_out.
 - intros; cbn [type_out type_in]; now rewrite positive_in_out, attr_in_out.
 - intros; cbn [type_out type_in]; now rewrite positive_in_out, attr_in_out.
 - reflexivity.
 - intros head tail IHhead IHtail; cbn [types_out types_in]; now rewrite IHhead, IHtail.
Qed.

Lemma source_types_roundtrip xs : types_in (types_out xs) = xs.
Proof.
 induction xs as [|head tail IH]; cbn [types_out types_in].
 - reflexivity.
 - now rewrite source_type_roundtrip, IH.
Qed.

Lemma native_type_roundtrip : forall t, type_out (type_in t) = t.
Proof.
 fix IH 1.
 intro t; destruct t as [|sz sg a|sg a|sz a|child a|child sz a|args ret cc|id a|id a].
 - reflexivity.
 - change (Ctypes.Tint (intsize_out (intsize_in sz)) (signedness_out (signedness_in sg)) (attr_out (attr_in a)) = Ctypes.Tint sz sg a).
   now rewrite intsize_out_in, signedness_out_in, attr_out_in.
 - change (Ctypes.Tlong (signedness_out (signedness_in sg)) (attr_out (attr_in a)) = Ctypes.Tlong sg a).
   now rewrite signedness_out_in, attr_out_in.
 - change (Ctypes.Tfloat (floatsize_out (floatsize_in sz)) (attr_out (attr_in a)) = Ctypes.Tfloat sz a).
   now rewrite floatsize_out_in, attr_out_in.
 - change (Ctypes.Tpointer (type_out (type_in child)) (attr_out (attr_in a)) = Ctypes.Tpointer child a).
   now rewrite IH, attr_out_in.
 - change (Ctypes.Tarray (type_out (type_in child)) (integer_out (integer_in sz)) (attr_out (attr_in a)) = Ctypes.Tarray child sz a).
   now rewrite IH, integer_out_in, attr_out_in.
 - change (Ctypes.Tfunction (types_out (types_in args)) (type_out (type_in ret)) (cc_out (cc_in cc)) = Ctypes.Tfunction args ret cc).
   rewrite IH, cc_out_in; f_equal.
   revert args; fix IL 1; intro xs; destruct xs as [|head tail]; cbn [types_in types_out].
   + reflexivity.
   + now rewrite IH, IL.
 - change (Ctypes.Tstruct (positive_out (positive_in id)) (attr_out (attr_in a)) = Ctypes.Tstruct id a).
   now rewrite positive_out_in, attr_out_in.
 - change (Ctypes.Tunion (positive_out (positive_in id)) (attr_out (attr_in a)) = Ctypes.Tunion id a).
   now rewrite positive_out_in, attr_out_in.
Qed.
Lemma native_types_roundtrip xs : types_out (types_in xs) = xs.
Proof.
 induction xs as [|head tail IH]; cbn [types_out types_in].
 - reflexivity.
 - now rewrite native_type_roundtrip, IH.
Qed.

Theorem type_representation_bijection :
 (forall t, type_in (type_out t) = t) /\
 (forall t, type_out (type_in t) = t).
Proof. split; [exact source_type_roundtrip|exact native_type_roundtrip]. Qed.
Print Assumptions type_representation_bijection.
Print Assumptions source_types_roundtrip.
Print Assumptions native_types_roundtrip.

Lemma natural_zero : N_of_Nat Nat_zero = N0.
Proof. reflexivity. Qed.
Lemma natural_successor n : N_of_Nat (Nat_succ n) = N.succ (N_of_Nat n).
Proof. unfold N_of_Nat; cbn [nat_of_Nat]; apply Nat2N.inj_succ. Qed.
Lemma integer_nonnegative n : integer_out (Int_ofNat n) = Z.of_N (N_of_Nat n).
Proof. reflexivity. Qed.
Lemma integer_negative n : integer_out (Int_negSucc n) = (-Z.of_N (N.succ (N_of_Nat n)))%Z.
Proof. reflexivity. Qed.
Lemma bool_false_preserved : bool_out Bool_false = false.
Proof. reflexivity. Qed.
Lemma bool_true_preserved : bool_out Bool_true = true.
Proof. reflexivity. Qed.
Lemma positive_one_preserved : positive_out CC_Positive_xH = xH.
Proof. reflexivity. Qed.
Lemma positive_even_preserved p : positive_out (CC_Positive_xO p) = xO (positive_out p).
Proof. reflexivity. Qed.
Lemma positive_odd_preserved p : positive_out (CC_Positive_xI p) = xI (positive_out p).
Proof. reflexivity. Qed.
Lemma intsize_I8_preserved : intsize_out CC_IntSize_I8 = Ctypes.I8.
Proof. reflexivity. Qed.
Lemma intsize_I16_preserved : intsize_out CC_IntSize_I16 = Ctypes.I16.
Proof. reflexivity. Qed.
Lemma intsize_I32_preserved : intsize_out CC_IntSize_I32 = Ctypes.I32.
Proof. reflexivity. Qed.
Lemma intsize_IBool_preserved : intsize_out CC_IntSize_IBool = Ctypes.IBool.
Proof. reflexivity. Qed.
Lemma signedness_Signed_preserved : signedness_out CC_Signedness_Signed = Ctypes.Signed.
Proof. reflexivity. Qed.
Lemma signedness_Unsigned_preserved : signedness_out CC_Signedness_Unsigned = Ctypes.Unsigned.
Proof. reflexivity. Qed.
Lemma floatsize_F32_preserved : floatsize_out CC_FloatSize_F32 = Ctypes.F32.
Proof. reflexivity. Qed.
Lemma floatsize_F64_preserved : floatsize_out CC_FloatSize_F64 = Ctypes.F64.
Proof. reflexivity. Qed.

Lemma attr_fields_preserved v align :
 attr_out (CC_Attr_mk v align) = Ctypes.mk_attr (bool_out v) (option_out N_of_Nat align).
Proof. reflexivity. Qed.
Lemma callconv_fields_preserved vararg unproto ret :
 cc_out (CC_CallConv_mk vararg unproto ret) =
 AST.mkcallconv (option_out integer_out vararg) (bool_out unproto) (bool_out ret).
Proof. reflexivity. Qed.
Lemma type_void_preserved  : type_out (CC_Ty_Tvoid) = Ctypes.Tvoid.
Proof. reflexivity. Qed.
Lemma type_int_preserved sz sg a : type_out (CC_Ty_Tint sz sg a) = Ctypes.Tint (intsize_out sz) (signedness_out sg) (attr_out a).
Proof. reflexivity. Qed.
Lemma type_long_preserved sg a : type_out (CC_Ty_Tlong sg a) = Ctypes.Tlong (signedness_out sg) (attr_out a).
Proof. reflexivity. Qed.
Lemma type_float_preserved sz a : type_out (CC_Ty_Tfloat sz a) = Ctypes.Tfloat (floatsize_out sz) (attr_out a).
Proof. reflexivity. Qed.
Lemma type_pointer_preserved t a : type_out (CC_Ty_Tpointer t a) = Ctypes.Tpointer (type_out t) (attr_out a).
Proof. reflexivity. Qed.
Lemma type_array_preserved t sz a : type_out (CC_Ty_Tarray t sz a) = Ctypes.Tarray (type_out t) (integer_out sz) (attr_out a).
Proof. reflexivity. Qed.
Lemma type_function_preserved args ret cc : type_out (CC_Ty_Tfunction args ret cc) = Ctypes.Tfunction (types_out args) (type_out ret) (cc_out cc).
Proof. reflexivity. Qed.
Lemma type_struct_preserved id a : type_out (CC_Ty_Tstruct id a) = Ctypes.Tstruct (positive_out id) (attr_out a).
Proof. reflexivity. Qed.
Lemma type_union_preserved id a : type_out (CC_Ty_Tunion id a) = Ctypes.Tunion (positive_out id) (attr_out a).
Proof. reflexivity. Qed.
Lemma argument_nil_preserved : types_out (List_nil_inst1 CC_Ty) = nil.
Proof. reflexivity. Qed.
Lemma argument_cons_preserved head tail :
 types_out (List_cons_inst1 CC_Ty head tail) = cons (type_out head) (types_out tail).
Proof. reflexivity. Qed.
